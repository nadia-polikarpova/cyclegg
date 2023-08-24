use colored::Colorize;
use egg::*;
use log::warn;
use std::collections::{HashMap, VecDeque};
use std::time::{Duration, Instant};
use symbolic_expressions::{parser, Sexp};

use crate::ast::*;
use crate::config::*;
use crate::egraph::*;

// We will use SymbolLang with no analysis for now
pub type Eg = EGraph<SymbolLang, ConstructorFolding>;
pub type Rw = Rewrite<SymbolLang, ConstructorFolding>;

/// A special scrutinee name used to signal that case split bound has been exceeded
const BOUND_EXCEEDED: &str = "__";

/// Condition that checks whether the substitution is into a smaller tuple of variable
#[derive(Clone)]
pub struct SmallerVar {
  pub scrutinees: Vec<Symbol>,
  pub ty_splits: HashMap<String, Sexp>,
}

impl SmallerVar {
  /// Substitution as a string, for debugging purposes
  fn pretty_subst(subst: &[(&Symbol, Expr)]) -> String {
    let strings: Vec<String> = subst
      .iter()
      .map(|p| format!("{} -> {}", &p.0.to_string(), &p.1.to_string()))
      .collect();
    strings.join(", ")
  }

  /// Is the range of subst smaller than its domain, when compared as a tuple?
  /// For now implements a sound but incomplete measure,
  /// where all components of the range need to be no larger, and at least one has to be strictly smaller.
  /// TODO: Implement a fancy automata-theoretic check here.
  fn smaller_tuple(subst: &Vec<(&Symbol, Expr)>, ty_splits: &HashMap<String, Sexp>) -> bool {
    let mut has_strictly_smaller = false;
    let info = SmallerVar::pretty_subst(subst.as_slice());
    for (var, expr) in subst {
      let var_name = var.to_string();
      let expr_name = expr.to_string();
      if CONFIG.structural_comparison {
        // Suppose a cyclic lemma is defined over the variable l0
        //
        // Suppose also that
        //   - After a case split, l0 = Cons x1 l1
        //   - After a second case split, l1 = Cons x2 l2
        //
        // With a structural comparison, we will allow the cyclic lemma to be
        // used on Cons x1 Nil, because we know that Nil is always smaller than
        // l1.
        //
        // In practice, this is probably not often useful.
        let sexp = parser::parse_str(&expr_name).unwrap();
        if contains_function(&sexp) {
          return false;
        }
        let var_sexp = &fix_singletons(recursively_resolve_variable(&var_name, ty_splits));
        let structural_comparison_result = structural_comparision(&sexp, var_sexp);
        // warn!("structurally comparing {} to var {} (resolved to {}), result: {:?}", sexp, var_name, var_sexp, structural_comparison_result);
        if let StructuralComparison::LT = structural_comparison_result {
          // warn!("{} is smaller than {}", sexp, var_name);
          has_strictly_smaller = true;
        } else if let StructuralComparison::Incomparable = structural_comparison_result {
          warn!(
            "cannot apply lemma with subst [{}], reason: {:?}",
            info, structural_comparison_result
          );
          return false;
        }
      } else {
        // In this branch we only check if the arguments are variables or
        // directly matching constructors.
        if is_descendant(&expr_name, &var_name) {
          // Target is strictly smaller than source
          has_strictly_smaller = true;
        } else if expr_name != var_name {
          // Target is neither strictly smaller nor equal to source
          // warn!("cannot apply lemma with subst [{}]", info);
          return false;
        }
      }
    }
    if has_strictly_smaller {
      warn!("applying lemma with subst [{}]", info);
    } else {
      warn!("cannot apply lemma with subst [{}]", info);
    }
    has_strictly_smaller
  }
}

impl Condition<SymbolLang, ConstructorFolding> for SmallerVar {
  /// Returns true if the substitution is into a smaller tuple of variables
  fn check(&self, egraph: &mut Eg, _eclass: Id, subst: &Subst) -> bool {
    let extractor = Extractor::new(egraph, AstSize);
    // Lookup all variables in the subst; some may be undefined if the lemma has fewer parameters
    let target_ids_mb = self.scrutinees.iter().map(|x| subst.get(to_wildcard(x)));
    let pairs = self
      .scrutinees
      .iter()
      .zip(target_ids_mb) // zip variables with their substitutions
      .filter(|(_, mb)| mb.is_some()) // filter out undefined variables
      .map(|(v, mb)| (v, extractor.find_best(*mb.unwrap()).1)); // actually look up the expression by class id
                                                                // Check that the expressions are smaller variables
    SmallerVar::smaller_tuple(&pairs.collect(), &self.ty_splits)
  }
}

/// The set of constructors in an e-class.
/// The order of variants is important: since we use the derived order during the merge.
#[derive(Debug, PartialEq, PartialOrd, Eq, Ord, Clone)]
pub enum Constructors {
  /// No constructors
  Zero,
  /// Single constructor
  One(Symbol),
  /// At least two different constructors (inconsistency)
  Two(Symbol, Symbol),
}

#[derive(Default, Clone)]
pub struct ConstructorFolding;

impl Analysis<SymbolLang> for ConstructorFolding {
  type Data = Constructors;

  fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
    // If we are merging classes with two different constructors,
    // record that this class is now inconsistent
    // (and remember both constructors, we'll need them to build an explanation)
    if let Constructors::One(s1) = to {
      if let Constructors::One(s2) = from {
        if *s1 != s2 {
          *to = Constructors::Two(*s1, s2);
          return DidMerge(true, true);
        } else {
          // TODO: Unify their children
        }
      }
    }
    // Otherwise, just take the max constructor set
    merge_max(to, from)
  }

  fn make(_: &EGraph<SymbolLang, Self>, enode: &SymbolLang) -> Self::Data {
    if is_constructor(enode.op.into()) {
      Constructors::One(enode.op)
    } else {
      Constructors::Zero
    }
  }
}

fn rec_expr_to_pattern_ast<L: Clone>(rec_expr: RecExpr<L>) -> RecExpr<ENodeOrVar<L>> {
  let enode_or_vars: Vec<ENodeOrVar<L>> = rec_expr
    .as_ref()
    .iter()
    .cloned()
    .map(|node| ENodeOrVar::ENode(node))
    .collect();
  enode_or_vars.into()
}

/// When we do a case split we will instantiate a variable x to
/// (Cons fresh_var1 fresh_var2 ...). We need to update our prev_instantiations
/// to account for this equality. We will copy each past instantiation and add
/// a new instantiation where instead of assigning x to itself, we will assign it
/// to the sexp. We'll also add assignments of the vars in the constructor to
/// themselves.
fn add_con_app_to_prev_instantiations<I>(
  prev_instantiations: &mut Vec<HashMap<String, Sexp>>,
  var: &String,
  con_app_sexp: &Sexp,
  app_vars: I,
) where
  I: IntoIterator<Item = String> + Clone,
{
  // These instantiations are equivalent but we need to track them so that
  // we can discover all possible new instantiations when we add a variable.
  let equal_instantiations: Vec<HashMap<String, Sexp>> = prev_instantiations
    .iter()
    .flat_map(|instantiation| {
      // If the var isn't in the instantiation, then we don't need to make a
      // new instantiation for it because assigning it in that instantiation
      // would be meaningless.
      if instantiation.contains_key(var) {
        let mut new_instantiation = instantiation.clone();
        new_instantiation.insert(var.clone(), con_app_sexp.clone());
        for app_var in app_vars.clone() {
          new_instantiation.insert(app_var.clone(), Sexp::String(app_var.clone()));
        }
        Some(new_instantiation)
      } else {
        None
      }
    })
    .collect();
  prev_instantiations.extend(equal_instantiations);
}

/// For simplicity of implementation, an instantiation will look like
/// {x: (S x'), x': Z}
/// instead of the simpler
/// {x: (S Z)}
/// This function will traverse the instantiation and make substitutions
/// where appropriate.
fn resolve_instantiation(instantiation: &HashMap<String, Sexp>) -> HashMap<String, Sexp> {
  let mut resolved_instantiation = HashMap::new();
  for var in instantiation.keys() {
    resolve_var_instantiation(instantiation, &mut resolved_instantiation, var);
  }
  resolved_instantiation
}

fn resolve_var_instantiation(
  instantiation: &HashMap<String, Sexp>,
  resolved_instantiation: &mut HashMap<String, Sexp>,
  var: &String,
) {
  match instantiation.get(var) {
    // This shouldn't happen...
    Some(Sexp::Empty) => unreachable!("Empty instantiation for variable {}", var),
    Some(Sexp::String(descendent)) => {
      if descendent != var {
        resolve_var_instantiation(instantiation, resolved_instantiation, descendent);
        match resolved_instantiation.get(descendent) {
          // The descendent doesn't resolve to anything (is a leaf)
          None => {
            resolved_instantiation.insert(var.clone(), Sexp::String(descendent.clone()));
          }
          // The descendent resolves to something
          Some(sexp) => {
            resolved_instantiation.insert(var.clone(), sexp.clone());
          }
        };
      }
    }
    Some(constructor_sexp @ Sexp::List(sexps)) => {
      let mut sexp_iter = sexps.iter();
      // The list should have at least one element in it
      let constructor = sexp_iter.next().unwrap();
      // This might be empty
      let mut new_sexps: Vec<Sexp> = sexp_iter
        .map(|sexp| {
          if let Sexp::String(sexp_var) = sexp {
            if !resolved_instantiation.contains_key(sexp_var) {
              resolve_var_instantiation(instantiation, resolved_instantiation, sexp_var);
            }
            resolved_instantiation.get(sexp_var).unwrap_or(sexp).clone()
          } else {
            unreachable!(
              "Constructor with argument that isn't a variable: {}",
              constructor_sexp
            )
          }
        })
        .collect();
      // Remake the sexp
      new_sexps.insert(0, constructor.clone());
      resolved_instantiation.insert(var.clone(), Sexp::List(new_sexps));
    }
    None => (),
  }
}

/// When we find a new variable that is a descendent of some others, we will
/// discover new instantiations of the LHS and RHS that we can unify using this
/// variable.
fn instantiate_new_ih_equalities(
  egraph: &mut Eg,
  prev_instantiations: &mut Vec<HashMap<String, Sexp>>,
  var: &String,
  var_ancestors: &[String],
  lhs: &Sexp,
  rhs: &Sexp,
  params: &[String],
) {
  let new_instantiations: Vec<HashMap<String, Sexp>> = prev_instantiations
    .iter()
    .flat_map(|instantiation| {
      // TODO: do we need to take the powerset of the ancestors here? I don't
      // think so precisely because they are ancestors instead of being unrelated.
      // There should be some past instantiation which resolves all ancestors to
      // themselves and some past instantiation which resolves all ancestors to
      // the closest ancestor to var (so if we instantiate it to var, all
      // ancestors get instantiated to var).
      var_ancestors.iter().flat_map(|ancestor| {
        // There are possibly many instantiations that refer to the ancestor. If
        // we replaced the ancestor with its descendent var in all of them, then
        // we would duplicate a bunch of instantiations.
        //
        // Consider for example the case where we start with the instantiation
        // [{x: x}, {x: S x', x': x'}, {x: Z}]
        // and we want to instantiate x to y for some reason.
        // Without this restriction we would get
        // [{x: y}, {x: y, x': x'}, {x: y}]
        // We really just want to get
        // [{x: y}]
        // once
        if ancestor != var
          && instantiation.contains_key(ancestor)
          && instantiation[ancestor] == Sexp::String(ancestor.to_string())
        {
          let mut new_instantiation = instantiation.clone();
          new_instantiation.insert(ancestor.clone(), Sexp::String(var.clone()));
          Some(new_instantiation)
        } else {
          None
        }
      })
    })
    .collect();
  for new_instantiation in new_instantiations.iter() {
    let resolved_instantiation = resolve_instantiation(new_instantiation);
    // println!("var: {}, ancestors: {:?}", var, var_ancestors);
    // println!("resolved instantiation: {:?}", resolved_instantiation);
    // .to_string().parse().unwrap() converts from sexp to RecExpr<ENodeOrVar<SymbolLang>>
    let new_lhs = recursively_resolve_sexp(lhs, &resolved_instantiation)
      .to_string()
      .parse()
      .unwrap();
    let new_rhs = recursively_resolve_sexp(rhs, &resolved_instantiation)
      .to_string()
      .parse()
      .unwrap();
    // println!("new lhs: {}, new rhs: {}", &new_lhs, &new_rhs);
    // The instantiation as a string
    let instantiation_str = params
      .iter()
      .map(|param| {
        format!(
          "{}={}",
          param,
          resolved_instantiation
            .get(param)
            // If the parameter isn't instantiated to anything,
            // we can assume that it is unchanged.
            .unwrap_or(&Sexp::String(param.clone()))
        )
      })
      .collect::<Vec<String>>()
      .join(",");
    egraph.union_instantiations(
      &new_lhs,
      &new_rhs,
      &Subst::default(),
      format!("ih-equality-{}", instantiation_str),
    );
  }
  prev_instantiations.extend(new_instantiations);
}

/// Proof goal
pub struct Goal<'a> {
  /// Goal name
  pub name: String,
  /// Equivalences we already proved
  pub egraph: Eg,
  pub explanation: Option<Explanation<SymbolLang>>,
  /// Rewrites are split into reductions (invertible rules) and lemmas (non-invertible rules)
  reductions: &'a Vec<Rw>,
  // TODO: Could be a hashmap
  lemmas: Vec<(String, Pat, Pat, SmallerVar)>,
  /// Universally-quantified variables of the goal
  /// (i.e. top-level parameters and binders derived from them through pattern matching)
  pub local_context: Context,
  /// Map from a variable to its split (right now we only track data constructor
  /// splits)
  ty_splits: HashMap<String, Sexp>,
  /// The top-level parameters to the goal
  pub params: Vec<String>,
  /// Variables we can case-split
  /// (i.e. the subset of local_context that have datatype types)
  scrutinees: VecDeque<Symbol>,
  /// Stores the expression each guard variable maps to. Since we only need
  /// these for proof emission, we just store the expression as a String.
  guard_exprs: HashMap<String, String>,
  // TODO: It almost feels like we could use an e-graph to track these past
  // instantiations, but we can't use the main e-graph because there's other stuff
  // that gets put into it.
  prev_var_instantiations: Vec<HashMap<String, Sexp>>,
  /// Our goal is to prove lhs == rhs
  lhs: Expr,
  pub lhs_sexp: Sexp,
  lhs_id: Id,
  rhs: Expr,
  pub rhs_sexp: Sexp,
  rhs_id: Id,
  /// Environment
  pub env: &'a Env,
  /// Global context (i.e. constructors and top-level bindings)
  pub global_context: &'a Context,
  /// Definitions in a form amenable to proof emission
  pub defns: &'a Defns,
}

impl<'a> Goal<'a> {
  /// Create top-level goal
  pub fn top(
    name: &str,
    lhs_sexp: Sexp,
    rhs_sexp: Sexp,
    params: Vec<(Symbol, Type)>,
    env: &'a Env,
    global_context: &'a Context,
    reductions: &'a Vec<Rw>,
    defns: &'a Defns,
  ) -> Self {
    let mut egraph: Eg = EGraph::default().with_explanations_enabled();
    let lhs = lhs_sexp.to_string().parse().unwrap();
    let rhs = rhs_sexp.to_string().parse().unwrap();
    egraph.add_expr(&lhs);
    egraph.add_expr(&rhs);
    egraph.rebuild();
    let lhs_id = egraph.lookup_expr(&lhs).unwrap();
    let rhs_id = egraph.lookup_expr(&rhs).unwrap();

    let mut res = Self {
      name: name.to_string(),
      egraph,
      explanation: None,
      reductions,
      lemmas: vec![],
      local_context: Context::new(),
      ty_splits: HashMap::new(),
      params: params.iter().map(|(p, _)| p.to_string()).collect(),
      guard_exprs: HashMap::new(),
      scrutinees: VecDeque::new(),
      // The only instantiation we've considered thus far is where every param maps to itself.
      // We won't unify the LHS and RHS under this instantiation, though, because that would
      // immediately (and falsely) prove the theorem.
      prev_var_instantiations: [params
        .iter()
        .map(|(param_symb, _param_type)| {
          (param_symb.to_string(), Sexp::String(param_symb.to_string()))
        })
        .collect::<HashMap<String, Sexp>>()]
      .into(),
      lhs,
      lhs_sexp,
      lhs_id,
      rhs,
      rhs_sexp,
      rhs_id,
      env,
      global_context,
      defns,
    };
    for (name, ty) in params {
      res.add_scrutinee(name, &ty, 0);
      res.local_context.insert(name, ty);
    }
    res
  }

  pub fn copy(&self) -> Self {
    Goal {
      name: self.name.clone(),
      egraph: self.egraph.clone(),
      // If we reach this point, I think we won't have an explanation
      explanation: None,
      reductions: self.reductions,
      lemmas: self.lemmas.clone(),
      local_context: self.local_context.clone(),
      ty_splits: self.ty_splits.clone(),
      params: self.params.clone(),
      guard_exprs: self.guard_exprs.clone(),
      scrutinees: self.scrutinees.clone(),
      prev_var_instantiations: self.prev_var_instantiations.clone(),
      lhs: self.lhs.clone(),
      lhs_sexp: self.lhs_sexp.clone(),
      lhs_id: self.lhs_id,
      rhs: self.rhs.clone(),
      rhs_sexp: self.rhs_sexp.clone(),
      rhs_id: self.rhs_id,
      env: self.env,
      global_context: self.global_context,
      // NOTE: We don't really need to clone this.
      defns: self.defns,
    }
  }

  pub fn get_lhs(&self) -> Expr {
    let extractor = Extractor::new(&self.egraph, AstSize);
    extractor.find_best(self.lhs_id).1
  }

  pub fn get_rhs(&self) -> Expr {
    let extractor = Extractor::new(&self.egraph, AstSize);
    extractor.find_best(self.rhs_id).1
  }

  /// Saturate the goal by applying all available rewrites
  pub fn saturate(mut self) -> Self {
    // FIXME: don't collect/clone?
    let lemmas: Vec<Rw> = self
      .lemmas
      .iter()
      .map(|(name, lhs, rhs, cond)| {
        Rewrite::new(
          name,
          lhs.clone(),
          ConditionalApplier {
            applier: rhs.clone(),
            condition: cond.clone(),
          },
        )
        .unwrap()
      })
      .collect();
    let rewrites = self.reductions.iter().chain(lemmas.iter());
    let runner = Runner::default()
      .with_explanations_enabled()
      .with_egraph(self.egraph)
      .run(rewrites);
    self.egraph = runner.egraph;
    self
  }

  /// Check if the goal has been discharged,
  /// and if so, create an explanation.
  pub fn check_validity(&mut self) {
    if self.egraph.find(self.lhs_id) == self.egraph.find(self.rhs_id) {
      // We have shown that LHS == RHS
      self.explanation = Some(self.egraph.explain_equivalence(&self.lhs, &self.rhs));
    } else {
      // Check if this case in unreachable (i.e. if there are any inconsistent e-classes in the e-graph)
      let res = self.egraph.classes().find_map(|eclass| {
        if let Constructors::Two(s1, s2) = eclass.data {
          if CONFIG.verbose {
            println!("{}: {} = {}", "UNREACHABLE".bright_red(), s1, s2);
          }
          // This is here only for the purpose of proof generation:
          let extractor = Extractor::new(&self.egraph, AstSize);
          let expr1 = extract_with_node(eclass, &extractor, |enode| enode.op == s1).unwrap();
          let expr2 = extract_with_node(eclass, &extractor, |enode| enode.op == s2).unwrap();
          Some((expr1, expr2))
        } else {
          None
        }
      });
      if let Some((expr1, expr2)) = res {
        self.explanation = Some(self.egraph.explain_equivalence(&expr1, &expr2));
      }
    }
  }

  /// Check whether an expression is reducible using this goal's reductions
  pub fn is_reducible(&self, expr: &Expr) -> bool {
    let mut local_graph: Eg = Default::default();
    local_graph.add_expr(expr);
    local_graph.rebuild();
    for reduction in self.reductions {
      if !reduction.search(&local_graph).is_empty() {
        return true;
      }
    }
    false
  }

  /// Create a rewrite `lhs => rhs` which will serve as the lemma ("induction hypothesis") for a cycle in the proof;
  /// here lhs and rhs are patterns, created by replacing all scrutinees with wildcards;
  /// soundness requires that the pattern only apply to variable tuples smaller than the current scrutinee tuple.
  fn mk_lemma_rewrites(&mut self, state: &ProofState) -> Vec<(String, Pat, Pat, SmallerVar)> {
    let lhs_id = self.egraph.find(self.lhs_id);
    let rhs_id = self.egraph.find(self.rhs_id);
    let exprs = get_all_expressions(&self.egraph, vec![lhs_id, rhs_id]);
    let is_var = |v| self.local_context.contains_key(v);

    let mut rewrites = vec![];
    // for _rhs_expr in exprs.get(&rhs_id).unwrap() {
    //   // warn!("equivalence for lemma rhs {} and goal rhs: {}", rhs_expr, self.egraph.explain_equivalence(rhs_expr, &self.rhs).get_flat_string());
    // }
    for lhs_expr in exprs.get(&lhs_id).unwrap() {
      // warn!("equivalence for lemma lhs {} and goal lhs: {}", lhs_expr, self.egraph.explain_equivalence(lhs_expr, &self.lhs).get_flat_string());
      let lhs: Pattern<SymbolLang> = to_pattern(lhs_expr, is_var);
      if (CONFIG.irreducible_only && self.is_reducible(lhs_expr)) || has_guard_wildcards(&lhs) {
        continue;
      }
      for rhs_expr in exprs.get(&rhs_id).unwrap() {
        if state.timeout() {
          return rewrites;
        }
        let rhs: Pattern<SymbolLang> = to_pattern(rhs_expr, is_var);
        if (CONFIG.irreducible_only && self.is_reducible(rhs_expr)) || has_guard_wildcards(&rhs) {
          continue;
        }
        let condition = SmallerVar {
          scrutinees: self.scrutinees.iter().cloned().collect(),
          // TODO: Can we take a reference instead of cloning?
          ty_splits: self.ty_splits.clone(),
        };
        let mut added_lemma = false;
        if rhs.vars().iter().all(|x| lhs.vars().contains(x)) {
          // if rhs has no extra wildcards, create a lemma lhs => rhs
          self.add_lemma(lhs.clone(), rhs.clone(), condition.clone(), &mut rewrites);
          added_lemma = true;
          if CONFIG.single_rhs {
            continue;
          };
        }
        if lhs.vars().iter().all(|x| rhs.vars().contains(x)) {
          // if lhs has no extra wildcards, create a lemma rhs => lhs
          self.add_lemma(rhs.clone(), lhs.clone(), condition, &mut rewrites);
          added_lemma = true;
          if CONFIG.single_rhs {
            continue;
          };
        }
        if !added_lemma {
          warn!("cannot create a lemma from {} and {}", lhs, rhs);
        }
      }
    }
    rewrites
  }

  /// Add a rewrite `lhs => rhs` to `rewrites` if not already present
  fn add_lemma(
    &self,
    lhs: Pat,
    rhs: Pat,
    cond: SmallerVar,
    rewrites: &mut Vec<(String, Pat, Pat, SmallerVar)>,
  ) {
    let name = format!("lemma-{}={}", lhs, rhs);
    let mut existing_lemmas = self.lemmas.iter().chain(rewrites.iter());
    if !existing_lemmas.any(|lemma| lemma.0 == name) {
      // Only add the lemma if we don't already have it:
      // warn!("creating lemma: {} => {}", lhs, rhs);
      let lemma = (name, lhs, rhs, cond);
      rewrites.push(lemma);
    }
  }

  /// Add var as a scrutinee if its type `ty` is a datatype;
  /// if depth bound is exceeded, add a sentinel symbol instead
  fn add_scrutinee(&mut self, var: Symbol, ty: &Type, depth: usize) {
    if let Ok(dt) = ty.datatype() {
      if self.env.contains_key(&Symbol::from(dt)) {
        // Only add new variable to scrutinees if its depth doesn't exceed the bound
        if depth < CONFIG.max_split_depth {
          self.scrutinees.push_back(var);
        } else {
          self.scrutinees.push_back(Symbol::from(BOUND_EXCEEDED));
        }
      }
    }
  }

  /// If the egraph contains ITEs whose condition is "irreducible"
  /// (i.e. not equivalent to a constant or a scrutinee variable),
  /// add a fresh scrutinee to its eclass, so that we can match on it.
  fn split_ite(&mut self) {
    let guard_var = "?g".parse().unwrap();
    let constants = vec![Symbol::from(&*TRUE), Symbol::from(&*FALSE)];
    // Iterator over all reducible symbols (i.e. Boolean constants and scrutinees)
    let reducible = self.scrutinees.iter().chain(constants.iter());
    // Pattern "(ite ?g ?x ?y)"
    let searcher: Pattern<SymbolLang> = format!("({} {} ?x ?y)", *ITE, guard_var).parse().unwrap();
    let matches = searcher.search(&self.egraph);
    // Collects class IDs of all irreducible guards;
    // it's a map because the same guard can match more than once, but we only want to add a new scrutinee once
    let mut irreducible_guards = HashMap::new();
    for m in matches {
      for subst in m.substs {
        let guard_id = *subst.get(guard_var).unwrap();
        // Root symbols of all enodes in guard_id's eclass
        let symbols: Vec<Symbol> = self.egraph[guard_id].nodes.iter().map(|n| n.op).collect();
        // This guard is irreducible if symbols are disjoint from reducible
        if !reducible.clone().any(|s| symbols.contains(s)) {
          irreducible_guards.insert(guard_id, subst);
        }
      }
    }
    // Iterate over all irreducible guard eclasses and add a new scrutinee to each
    for (guard_id, subst) in irreducible_guards {
      let fresh_var = Symbol::from(format!("{}{}", GUARD_PREFIX, guard_id));
      // This is here only for logging purposes
      let expr = Extractor::new(&self.egraph, AstSize).find_best(guard_id).1;
      let add_scrutinee_message =
        format!("adding scrutinee {} to split condition {}", fresh_var, expr);
      warn!("{}", add_scrutinee_message);
      self
        .local_context
        .insert(fresh_var, BOOL_TYPE.parse().unwrap());
      // We are adding the new scrutinee to the front of the deque,
      // because we want to split conditions first, since they don't introduce new variables
      self.scrutinees.push_front(fresh_var);
      let new_node = SymbolLang::leaf(fresh_var);
      let new_pattern_ast = vec![ENodeOrVar::ENode(new_node.clone())].into();
      let guard_var_pattern_ast = vec![ENodeOrVar::Var(guard_var)].into();
      self
        .guard_exprs
        .insert(fresh_var.to_string(), expr.to_string());
      self.egraph.union_instantiations(
        &guard_var_pattern_ast,
        &new_pattern_ast,
        &subst,
        add_scrutinee_message,
      );
    }
    self.egraph.rebuild();
  }

  /// Consume this goal and add its case splits to the proof state
  fn case_split(mut self, state: &mut ProofState<'a>, mk_lemmas: bool) {
    let new_lemmas = if mk_lemmas {
      self.mk_lemma_rewrites(state)
    } else {
      vec![]
    };
    // Create rewrites `lhs => lhs'` and `rhs => rhs'` which will be used with the IH in lieu of cyclic lemmas.
    // let half_lemmas = self.mk_half_lemma_rewrites(state);

    // Get the next variable to case-split on
    let var = self.scrutinees.pop_front().unwrap();
    let var_str = var.to_string();
    warn!("case-split on {}", var);
    let var_node = SymbolLang::leaf(var);
    let var_pattern_ast: RecExpr<ENodeOrVar<SymbolLang>> = vec![ENodeOrVar::ENode(var_node)].into();
    // Get the type of the variable, and then remove the variable
    if self.local_context.get(&var).is_none() {
      panic!("{} not in local context", var);
    }
    let ty = self.local_context.get(&var).unwrap();
    // Convert to datatype name
    let dt = Symbol::from(ty.datatype().unwrap());
    // Get the constructors of the datatype
    let (_, cons) = self.env.get(&dt).unwrap();
    // We will add this to state.proof to describe the case split.
    let mut instantiated_cons_and_goals: Vec<(String, String)> = vec![];
    // For each constructor, create a new goal and push it onto the proof state
    // (we process constructors in reverse order so that base case ends up at the top of the stack)
    for &con in cons.iter().rev() {
      let mut new_goal = self.copy();
      new_goal.name = format!("{}:", self.name);
      if mk_lemmas {
        new_goal.lemmas = self
          .lemmas
          .iter()
          .chain(new_lemmas.iter())
          .cloned()
          .collect();
      }

      // Get the types of constructor arguments
      let con_ty = self.global_context.get(&con).unwrap();
      let con_args = Goal::instantiate_constructor(con_ty, ty);
      // For each argument: create a fresh variable and add it to the context and to scrutinees
      let mut fresh_vars = vec![];

      for (i, arg_type) in con_args.iter().enumerate() {
        let fresh_var_name = format!("{}_{}{}", var, self.egraph.total_size(), i);
        let depth = var_depth(&fresh_var_name[..]);
        let fresh_var = Symbol::from(fresh_var_name.clone());
        fresh_vars.push(fresh_var);
        // Add new variable to context
        new_goal.local_context.insert(fresh_var, arg_type.clone());
        new_goal.add_scrutinee(fresh_var, arg_type, depth);
        if !mk_lemmas {
          // Find all vars that this variable descends from.
          //
          // TODO: this can be pulled out of both for loops. It will require
          // some logic to add another variable (the parent).
          let ancestors: Vec<String> = self
            .local_context
            .iter()
            .flat_map(|(ancestor_var, ancestor_type)| {
              if ancestor_type == arg_type && is_descendant(&fresh_var_name, ancestor_var.as_str())
              {
                Some(ancestor_var.to_string())
              } else {
                None
              }
            })
            .collect();
          // TODO: Can this be made more efficient by only once computing the
          // new possible instantiations for each constructor arg? Perhaps also
          // even for each case split? And then we would just take those
          // instantiations and use them for each fresh variable.
          instantiate_new_ih_equalities(
            &mut new_goal.egraph,
            &mut new_goal.prev_var_instantiations,
            &fresh_var_name,
            &ancestors,
            &new_goal.lhs_sexp,
            &new_goal.rhs_sexp,
            &new_goal.params,
          );
        }
        // NOTE If we are adding a new variable with the same type as its parent,
        // then we might be losing information about it.
        //
        // For example, if we case split x = S x', we simply add x' to the
        // e-graph with no new information about it. But all equalities
        // involving x are also true of x' because it is smaller than x.
        //
        // We resolve this when mk_lemmas is false by calling out to
        // instantiate_new_ih_euqalities (the idea being that all facts about x
        // are derived from its presence in the IH), but if we had a faster way
        // of copying the facts about x to x' that could make things easier.
      }

      // Create an application of the constructor to the fresh vars
      let fresh_var_strings_iter = fresh_vars.iter().map(|x| x.to_string());
      let con_app_string = format!(
        "({} {})",
        con,
        fresh_var_strings_iter
          .clone()
          .collect::<Vec<String>>()
          .join(" ")
      );
      let con_app_sexp = parser::parse_str(&con_app_string).unwrap();
      // This is a split we need to track
      new_goal
        .ty_splits
        .insert(var_str.clone(), con_app_sexp.clone());
      // also in all of the conditions in the lemmas (there is probably a better
      // way to do this...)
      for (_, _, _, smaller_var) in new_goal.lemmas.iter_mut() {
        smaller_var
          .ty_splits
          .insert(var_str.clone(), con_app_sexp.clone());
      }
      // We also need to add this split to the prev_var_instantiations
      add_con_app_to_prev_instantiations(
        &mut new_goal.prev_var_instantiations,
        &var_str,
        &con_app_sexp,
        fresh_var_strings_iter,
      );
      let con_app: Expr = con_app_string.parse().unwrap();

      new_goal.name = format!("{}{}={}", new_goal.name, var, con_app);

      instantiated_cons_and_goals.push((con_app_string, new_goal.name.clone()));

      // Add con_app to the new goal's egraph and union it with var
      new_goal.egraph.add_expr(&con_app);
      let _con_app_id = new_goal.egraph.lookup_expr(&con_app).unwrap();
      // Not sure if it's proper to use new_goal.name here
      new_goal.egraph.union_instantiations(
        &var_pattern_ast,
        &rec_expr_to_pattern_ast(con_app),
        &Subst::default(),
        new_goal.name.clone(),
      );
      new_goal.egraph.rebuild();

      // Remove old variable from the egraph and context
      remove_node(&mut new_goal.egraph, &SymbolLang::leaf(var));
      // warn!("removing var {}", var);
      // FIXME: is this OK? add a full_context?
      // new_goal.local_context.remove(&var);
      new_goal.egraph.rebuild();

      // Add the subgoal to the proof state
      state.goals.push(new_goal);
    }
    // We split on var into the various instantiated constructors and subgoals.
    //
    // If the var begins with the guard prefix, it is an ITE split and we will
    // add the condition that was split on to our proof term. This is necessary
    // because for ITE splits we introduce a new variable that we bind an
    // expression to.
    if var_str.starts_with(GUARD_PREFIX) {
      // There should only be two cases.
      assert_eq!(instantiated_cons_and_goals.len(), 2);
      state.proof.insert(
        self.name,
        ProofTerm::ITESplit(
          var_str.clone(),
          self.guard_exprs[&var_str].clone(),
          instantiated_cons_and_goals,
        ),
      );
    // Otherwise, we are doing a case split on a variable.
    } else {
      state.proof.insert(
        self.name,
        ProofTerm::CaseSplit(var_str, instantiated_cons_and_goals),
      );
    }
  }

  /// Save e-graph to file
  fn save_egraph(&self) {
    let filename = CONFIG.output_directory.join(format!("{}.png", self.name));
    let verbosity = format!("-q{}", CONFIG.log_level as usize);
    let dot = self.egraph.dot();
    dot
      .run_dot([
        "-Tpng",
        verbosity.as_str(),
        "-o",
        &filename.to_string_lossy(),
      ])
      .unwrap();
  }

  /// Given a polymorphic constructor type and a concrete instantiation of a datatype,
  /// return the concrete types of constructor arguments.
  fn instantiate_constructor(con_ty: &Type, actual: &Type) -> Vec<Type> {
    let (args, ret) = con_ty.args_ret();
    let instantiations = find_instantiations(&ret, actual);
    // println!("args: {:?}, ret: {}, actual: {:?}", args, ret, actual);
    // println!("instantiations: {:?}", instantiations);
    let ret = args
      .iter()
      .map(|arg| Type::new(resolve_sexp(&arg.repr, &instantiations)))
      .collect();
    // println!("new types: {:?}", ret);
    ret
  }
}

#[derive(Clone, Debug)]
pub enum ProofTerm {
  /// - Arg0: Name of the variable we split on
  /// - Arg1: List of cases we split on
  ///   * Arg0: Sexp we split to
  ///   * Arg1: Name of goal from this split
  ///
  /// Example:
  /// ```
  /// CaseSplit("x", [("(Z)", "goal_1"), ("(S x')","goal_2")])
  /// ```
  /// corresponds to the proof
  /// ```
  /// case x of
  ///   Z    -> goal_1
  ///   S x' -> goal_2
  /// ```
  CaseSplit(String, Vec<(String, String)>),
  /// The same thing as a case split, except instead of splitting on one of the
  /// symbolic variables, we split on an expression.
  ///
  /// - Arg0: A fresh variable introduced that is equal to the expression
  /// - Arg1: The expression we split on
  /// - Arg2: List of cases we split on (same as above).
  ///         There will always be two cases, corresponding to `True` and `False`.
  ///
  /// Example:
  /// ```
  /// ITESplit("g0", "(lt x y)", [("True", "goal_1"), ("False", "goal_2")])
  /// ```
  /// corresponds to the proof
  /// ```
  /// let g0 = lt x y in
  ///   case g0 of
  ///     True  -> goal_1
  ///     False -> goal_2
  /// ```
  ITESplit(String, String, Vec<(String, String)>),
}

/// A proof state is a list of subgoals,
/// all of which have to be discharged
pub struct ProofState<'a> {
  pub goals: Vec<Goal<'a>>,
  pub solved_goal_explanation_and_context: HashMap<String, (Explanation<SymbolLang>, Context)>,
  pub proof: HashMap<String, ProofTerm>,
  pub start_time: Instant,
}

impl<'a> ProofState<'a> {
  // Has timeout been reached?
  pub fn timeout(&self) -> bool {
    CONFIG.timeout.is_some()
      && self.start_time.elapsed() > Duration::new(CONFIG.timeout.unwrap(), 0)
  }
}

/// Pretty-printed proof state
pub fn pretty_state(state: &ProofState) -> String {
  format!(
    "[{}]",
    state
      .goals
      .iter()
      .map(|g| g.name.clone())
      .collect::<Vec<String>>()
      .join(", ")
  )
}

/// Outcome of a proof attempt
#[derive(Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum Outcome {
  Valid,
  Invalid,
  Unknown,
  Timeout,
}

impl std::fmt::Display for Outcome {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match *self {
      Outcome::Valid => write!(f, "{}", "VALID".green()),
      Outcome::Invalid => write!(f, "{}", "INVALID".red()),
      Outcome::Unknown => write!(f, "{}", "UNKNOWN".yellow()),
      Outcome::Timeout => write!(f, "{}", "TIMEOUT".yellow()),
    }
  }
}

pub fn explain_goal_failure(goal: &Goal) {
  println!("{} {}", "Could not prove".red(), goal.name);
  println!("{}", "LHS Nodes".cyan());
  let extractor = egg::Extractor::new(&goal.egraph, AstSize);
  for lhs_node in goal.egraph[goal.lhs_id].nodes.iter() {
    let child_rec_exprs: String = lhs_node
      .children
      .iter()
      .map(|child_id| {
        let (_, best_rec_expr) = extractor.find_best(*child_id);
        best_rec_expr.to_string()
      })
      .collect::<Vec<String>>()
      .join(" ");
    if child_rec_exprs.is_empty() {
      println!("({})", lhs_node);
    } else {
      println!("({} {})", lhs_node, child_rec_exprs);
    }
  }
  println!("{}", "RHS Nodes".cyan());
  for rhs_node in goal.egraph[goal.rhs_id].nodes.iter() {
    let child_rec_exprs: String = rhs_node
      .children
      .iter()
      .map(|child_id| {
        let (_, best_rec_expr) = extractor.find_best(*child_id);
        best_rec_expr.to_string()
      })
      .collect::<Vec<String>>()
      .join(" ");
    if child_rec_exprs.is_empty() {
      println!("({})", rhs_node);
    } else {
      println!("({} {})", rhs_node, child_rec_exprs);
    }
  }
}

/// Top-level interface to the theorem prover.
pub fn prove(mut goal: Goal, make_cyclic_lemmas: bool) -> (Outcome, ProofState) {
  // let initial_goal_name = goal.name.clone();
  let mut state = ProofState {
    goals: vec![goal],
    solved_goal_explanation_and_context: HashMap::default(),
    proof: HashMap::default(),
    start_time: Instant::now(),
  };
  while !state.goals.is_empty() {
    if state.timeout() {
      return (Outcome::Timeout, state);
    }

    // TODO: This should be info! but I don't know how to suppress all the info output from egg
    warn!("PROOF STATE: {}", pretty_state(&state));
    // Pop the first subgoal
    goal = state.goals.pop().unwrap();
    // Saturate the goal
    goal = goal.saturate();
    if CONFIG.save_graphs {
      goal.save_egraph();
    }
    goal.check_validity();
    if let Some(mut explanation) = goal.explanation {
      // This goal has been discharged, proceed to the next goal
      if CONFIG.verbose {
        println!("{} {}", "Proved case".bright_blue(), goal.name);
        println!("{}", explanation.get_flat_string());
      }
      state
        .solved_goal_explanation_and_context
        .insert(goal.name, (explanation, goal.local_context));
      continue;
    }
    if CONFIG.verbose {
      explain_goal_failure(&goal);
    }
    warn!("goal scrutinees before split: {:?}", goal.scrutinees);
    goal.split_ite();
    warn!("goal scrutinees after split: {:?}", goal.scrutinees);
    if goal.scrutinees.is_empty() {
      // This goal has no more variables to case-split on,
      // so this goal, and hence the whole conjecture, is invalid
      if CONFIG.verbose {
        for remaining_goal in &state.goals {
          println!("{} {}", "Remaining case".yellow(), remaining_goal.name);
        }
      }
      return (Outcome::Invalid, state);
    }
    if goal.scrutinees.front().unwrap() == &Symbol::from(BOUND_EXCEEDED) {
      // This goal could be further split, but we have reached the maximum depth,
      // we cannot prove or disprove the conjecture
      if CONFIG.verbose {
        for remaining_goal in &state.goals {
          println!("{} {}", "Remaining case".yellow(), remaining_goal.name);
        }
      }
      return (Outcome::Unknown, state);
    }
    goal.case_split(&mut state, make_cyclic_lemmas);
    if CONFIG.verbose {
      println!("{}", "Case splitting and continuing...".purple());
    }
  }
  // All goals have been discharged, so the conjecture is valid:
  (Outcome::Valid, state)
}
