use std::collections::{VecDeque, HashSet, HashMap};
use egg::{*};
use log::{warn, error};
use colored::Colorize;
use symbolic_expressions::{Sexp, parser};
use std::time::{Instant, Duration};

use crate::ast::{*};
use crate::egraph::{*};
use crate::config::{*};

// We will use SymbolLang with no analysis for now
pub type Eg = EGraph<SymbolLang, ()>;
pub type Rw = Rewrite<SymbolLang, ()>;

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
  fn pretty_subst(subst: &Vec<(&Symbol, Expr)>) -> String {
    let strings: Vec<String> = subst.iter().map(|p| format!("{} -> {}", &p.0.to_string(), &p.1.to_string())).collect();
    strings.join(", ")
  }

  /// Is the range of subst smaller than its domain, when compared as a tuple?
  /// For now implements a sound but incomplete measure,
  /// where all components of the range need to be no larger, and at least one has to be strictly smaller.
  /// TODO: Implement a fancy automata-theoretic check here.
  fn smaller_tuple(subst: &Vec<(&Symbol, Expr)>, ty_splits: &HashMap<String, Sexp>) -> bool {
    let mut has_strictly_smaller = false;
    let info = SmallerVar::pretty_subst(subst);    
    for (var, expr) in subst {
      let var_name = var.to_string();
      let expr_name = expr.to_string();
      let var_sexp = Sexp::String(var_name.clone());
      let sexp = parser::parse_str(&expr_name).unwrap();
      if contains_function(&sexp) {
        return false;
      }
      let var_sexp = &fix_singletons(resolve_variable(&var_name, ty_splits));
      let structural_comparison_result = structural_comparision(&sexp, var_sexp);
      // warn!("structurally comparing {} to var {} (resolved to {}), result: {:?}", sexp, var_name, var_sexp, structural_comparison_result);
      if let StructuralComparison::LT = structural_comparison_result {
        // warn!("{} is smaller than {}", sexp, var_name);
        has_strictly_smaller = true;
      } else if let StructuralComparison::Incomparable = structural_comparison_result {
        warn!("cannot apply lemma with subst [{}], reason: {:?}", info, structural_comparison_result);
        return false;
      }
      // if is_descendant(&expr_name, &var_name) {
      //   // Target is strictly smaller than source
      //   has_strictly_smaller = true;
      // // } else if expr_name == "Z" {
      // //   // pass
      // // } else if var_name == "n" && expr_name == "(S n_40)" {
      // //   // pass
      // } else if expr_name != var_name {
      //   // Target is neither strictly smaller nor equal to source
      //   // warn!("cannot apply lemma with subst [{}]", info);
      //   return false;
      // }
    }
    if has_strictly_smaller { warn!("applying lemma with subst [{}]", info); }
    else { warn!("cannot apply lemma with subst [{}]", info); }
    has_strictly_smaller
  }
}

impl Condition<SymbolLang, ()> for SmallerVar {
  /// Returns true if the substitution is into a smaller tuple of variables
  fn check(&self, egraph: &mut Eg, _eclass: Id, subst: &Subst) -> bool {
    let extractor = Extractor::new(egraph, AstSize);
    // Lookup all variables in the subst; some may be undefined if the lemma has fewer parameters
    let target_ids_mb = self.scrutinees.iter().map(|x| subst.get(to_wildcard(&x)));
    let pairs = self.scrutinees.iter()
                  .zip(target_ids_mb)                                       // zip variables with their substitutions
                  .filter(|(_, mb)| mb.is_some())                           // filter out undefined variables
                  .map(|(v, mb)| (v, extractor.find_best(*mb.unwrap()).1)); // actually look up the expression by class id
    // Check that the expressions are smaller variables
    SmallerVar::smaller_tuple(&pairs.collect(), &self.ty_splits)
  }
}

fn rec_expr_to_pattern_ast<L: Clone>(rec_expr: RecExpr<L>) -> RecExpr<ENodeOrVar<L>> {
  let enode_or_vars: Vec<ENodeOrVar<L>> = rec_expr.as_ref().into_iter()
                                                           .cloned()
                                                           .map(|node| ENodeOrVar::ENode(node))
                                                           .collect();
  enode_or_vars.into()
}

fn instantiate_vars(expr: &Expr, var_instantiations: &Vec<(Symbol, SymbolLang)>) -> Expr {
  // This should only replace one node, but I guess if there is a duplication of
  // the var in the RecExpr for some reason it will still work.
  let new_expr: Vec<SymbolLang> = expr.as_ref().iter().map(|node| {
    match node {
      SymbolLang { op, children: _ } => {
        for (var, target) in var_instantiations.iter() {
          if op == var {
            return target.clone();
          }
        }
        return node.clone();
      }
    }
  }).collect();
  return Expr::from(new_expr);
}

// FIXME: this is a hack to deal with the case where you have something like
// expr: (xs)
// var_instantiations: {xs: (Cons y ys), y: z}
//
// If you instantiate once, you'll get
//
// new_expr: (Cons y ys)
//
// But you actually want it to be
//
// new_expr: (Cons z ys)
//
// because you needed to instantiate y to z.
//
// The right solution is to precompute the properly resolved instantiations. But a
// valid (and slow!) hack is to just keep instantiating until we reach a fixpoint.
fn instantiate_vars_fixpoint(expr: &Expr, var_instantiations: &Vec<(Symbol, SymbolLang)>) -> Expr {
  let mut last_expr = expr.clone();
  let mut new_expr = instantiate_vars(expr, var_instantiations);
  while new_expr != last_expr {
    new_expr = instantiate_vars(&new_expr, var_instantiations);
    last_expr = new_expr.clone();
  }
  return new_expr;
}

fn find_parent_vars<'a>(vars: &'a Vec<(String, Type)>, var_name: &String) -> Vec<&'a (String, Type)> {
  vars.iter()
    .filter(|(v_name, _v_type)| is_descendant(var_name, v_name) || v_name == var_name)
    .collect()
}

fn get_var_descendent_combinations(var_descendents: &HashMap<String, Vec<String>>) -> Vec<Vec<(String, String)>> {
  // TODO CK: I think this is significant overkill. I'm pretty sure we don't need to take
  // all combinations, but instead only some small part of them.
  //
  // At the very least we only need to do combinations of descendents with
  // whatever new variable(s) we add - which will prevent some amount of
  // combinatorial explosion.
  let mut descendent_combinations: Vec<Vec<(String, String)>> = vec!(vec!());
  for (var, descendents) in var_descendents.iter() {
    let mut new_combinations = vec!();
    for descendent in descendents {
      for descendent_combination in descendent_combinations.iter() {
        let mut new_combination = descendent_combination.clone();
        new_combination.push((var.clone(), descendent.clone()));
        new_combinations.push(new_combination);
      }
    }
    descendent_combinations = new_combinations;
  }
  return descendent_combinations;
}

fn instantiate_descendent_lhs_and_rhs(egraph: &mut Eg, lhs: &Expr, rhs: &Expr, vars_descendents: &HashMap<String, Vec<String>>) {
  // println!("vars_descendents: {:?}", vars_descendents);
  for param_instantiations in get_var_descendent_combinations(vars_descendents) {
    let var_instantiations = param_instantiations
      .into_iter()
      .map(|(param, descendent)| (Symbol::from(param), SymbolLang::leaf(descendent)))
      .collect();
    // FIXME: need to somehow expand the instantiated variable if we've case
    // split on it and given it a value.
    let new_lhs = instantiate_vars_fixpoint(lhs, &var_instantiations);
    let new_rhs = instantiate_vars_fixpoint(rhs, &var_instantiations);
    // println!("var_instantiations: {:?}, new lhs: {}, new rhs: {}", &var_instantiations, &new_lhs, &new_rhs);
    egraph.add_expr(&new_lhs);
    egraph.add_expr(&new_rhs);
  }
}

/// When we do a case split we will instantiate a variable x to
/// (Cons fresh_var1 fresh_var2 ...). We need to update our prev_instantiations
/// to account for this equality. We will copy each past instantiation and add
/// a new instantiation where instead of assigning x to itself, we will assign it
/// to the sexp. We'll also add assignments of the vars in the constructor to
/// themselves.
fn add_con_app_to_prev_instantiations<I>(prev_instantiations: &mut Vec<HashMap<String, Sexp>>,
                                      var: &String, con_app_sexp: &Sexp, app_vars: I)
where
  I: IntoIterator<Item = String> + Clone {
  // These instantiations are equivalent but we need to track them so that
  // we can discover all possible new instantiations when we add a variable.
  let equal_instantiations: Vec<HashMap<String, Sexp>> =
    prev_instantiations.iter().flat_map(|instantiation| {
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
  }).collect();
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

fn resolve_var_instantiation(instantiation: &HashMap<String, Sexp>,
                             resolved_instantiation: &mut HashMap<String, Sexp>, var: &String) {
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
          },
          // The descendent resolves to something
          Some(sexp) => {
            resolved_instantiation.insert(var.clone(), sexp.clone());
          }
        };
      }
    },
    Some(constructor_sexp @ Sexp::List(sexps)) => {
      let mut sexp_iter = sexps.iter();
      // The list should have at least one element in it
      let constructor = sexp_iter.next().unwrap();
      // This might be empty
      let mut new_sexps: Vec<Sexp> = sexp_iter.map(|sexp| {
        if let Sexp::String(sexp_var) = sexp {
          if !resolved_instantiation.contains_key(sexp_var) {
            resolve_var_instantiation(instantiation, resolved_instantiation, sexp_var);
          }
          resolved_instantiation.get(sexp_var).unwrap_or(sexp).clone()
        } else {
          unreachable!("Constructor with argument that isn't a variable: {}", constructor_sexp)
        }
      }).collect();
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
fn instantiate_new_ih_equalities(egraph: &mut Eg, prev_instantiations: &mut Vec<HashMap<String, Sexp>>,
                                 var: &String, var_ancestors: &Vec<String>, lhs: &Sexp, rhs: &Sexp, params: &Vec<String>) {
  let new_instantiations: Vec<HashMap<String, Sexp>> =
    prev_instantiations.iter().flat_map(|instantiation| {
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
      if ancestor != var && instantiation.contains_key(ancestor)
        && instantiation[ancestor] == Sexp::String(ancestor.to_string()) {
        let mut new_instantiation = instantiation.clone();
        new_instantiation.insert(ancestor.clone(), Sexp::String(var.clone()));
        Some(new_instantiation)
      } else {
        None
      }
    })
  }).collect();
  for new_instantiation in new_instantiations.iter() {
    let resolved_instantiation = resolve_instantiation(new_instantiation);
    // println!("resolved instantiation: {:?}", resolved_instantiation);
    // .to_string().parse().unwrap() converts from sexp to RecExpr<ENodeOrVar<SymbolLang>>
    let new_lhs = resolve_sexp(lhs, &resolved_instantiation).to_string().parse().unwrap();
    let new_rhs = resolve_sexp(rhs, &resolved_instantiation).to_string().parse().unwrap();
    // println!("new lhs: {}, new rhs: {}", &new_lhs, &new_rhs);
    // The instantiation as a string
    let instantiation_str = params.iter().map(|param| {
      format!("{}={}",
              param,
              resolved_instantiation
                .get(param)
                // If the parameter isn't instantiated to anything,
                // we can assume that it is unchanged.
                .unwrap_or(&Sexp::String(param.clone())))
    }).collect::<Vec<String>>().join(",");
    egraph.union_instantiations(&new_lhs, &new_rhs, &Subst::default(), format!("ih-equality-{}", instantiation_str));
  }
  prev_instantiations.extend(new_instantiations);
}

/// Proof goal
pub struct Goal {
  /// Goal name
  pub name: String,
  /// Equivalences we already proved
  pub egraph: Eg,
  pub explanation: Option<Explanation<SymbolLang>>,
  /// Rewrites are split into reductions (invertible rules) and lemmas (non-invertible rules)
  reductions: Vec<Rw>,
  // TODO: Could be a hashmap
  pub lemmas: Vec<(String, Pat, Pat, SmallerVar)>,
  /// Universally-quantified variables of the goal
  /// (i.e. top-level parameters and binders derived from them through pattern matching)
  pub local_context: Context,
  // /// The top-level universally-quanitifed variables used as the arugments for
  // /// the proof: these are the roots of ty_splits
  // pub top_level_variables: Vec<Symbol>,
  /// Map from a variable to its split (right now we only track data constructor
  /// splits)
  pub ty_splits: HashMap<String, Sexp>,
  /// The top-level parameters to the goal
  pub params: Vec<String>,
  /// Variables we can case-split
  /// (i.e. the subset of local_context that have datatype types)
  scrutinees: VecDeque<Symbol>,
  /// Stores the expression each guard variable maps to. Since we only need
  /// these for proof emission, we just store the expression as a String.
  pub guard_exprs: HashMap<String, String>,
  pub prev_var_instantiations: Vec<HashMap<String, Sexp>>,
  // TODO: add set tracking the variable instantiations we have so far
  // used. this will be used to build up potential other instantiations we can
  // use to "ground" the proving state in later iterations.
  // TODO: It almost feels like we could use an e-graph to track these past
  // instantiations, but we can't use the main e-graph because there's other stuff
  // that gets put into it.
  // FIXME: vars/vars_descendents could be much more efficient using Symbols
  /// The vars over which the theorem is quantified (including those introduced
  /// by case splits)
  pub vars: Vec<(String, Type)>,
  /// The descendents of each of the vars
  pub vars_descendents: HashMap<String, Vec<String>>,
  /// Our goal is to prove lhs == rhs
  pub lhs: Expr,
  pub lhs_sexp: Sexp,
  pub lhs_id: Id,
  pub rhs: Expr,
  pub rhs_sexp: Sexp,
  pub rhs_id: Id,
  /// Environment
  pub env: Env,
  /// Global context (i.e. constructors and top-level bindings)
  pub global_context: Context,
  /// Definitions in a form amenable to proof emission
  pub defns: Defns,
}

impl Goal {
  /// Create top-level goal
  pub fn top(
    name: &str,
    lhs: Expr,
    lhs_sexp: Sexp,
    rhs: Expr,
    rhs_sexp: Sexp,
    params: Vec<(Symbol, Type)>,
    env: &Env,
    global_context: &Context,
    reductions: &[Rw],
    defns: Defns,
  ) -> Self {
    let mut egraph: Eg = EGraph::default().with_explanations_enabled();
    egraph.add_expr(&lhs);
    egraph.add_expr(&rhs);
    egraph.rebuild();
    let lhs_id = egraph.lookup_expr(&lhs).unwrap();
    let rhs_id = egraph.lookup_expr(&rhs).unwrap();

    let mut res = Self {
      name: name.to_string(),
      egraph,
      explanation: None,
      reductions: reductions.to_vec(),
      lemmas: vec![],
      local_context: Context::new(),
      ty_splits: HashMap::new(),
      params: params.iter().map(|(p, _)| p.to_string()).collect(),
      guard_exprs: HashMap::new(),
      scrutinees: VecDeque::new(),
      vars: params.iter().map(|(param_symb, param_type)|(param_symb.to_string(), param_type.clone())).collect(),
      // The only instantiation we've considered thus far is where every param maps to itself.
      // We won't unify the LHS and RHS under this instantiation, though, because that would
      // immediately (and falsely) prove the theorem.
      prev_var_instantiations: [params.iter().map(|(param_symb, _param_type)|{
        (param_symb.to_string(), Sexp::String(param_symb.to_string()))
      }).collect::<HashMap<String, Sexp>>()].into(),
      // Each param is its own descendent
      vars_descendents: params.iter().map(|(param_symb, _)| (param_symb.to_string(), vec!(param_symb.to_string()))).collect(),
      lhs,
      lhs_sexp,
      lhs_id,
      rhs,
      rhs_sexp,
      rhs_id,
      env: env.clone(),
      global_context: global_context.clone(),
      defns,
    };
    for (name, ty) in params {
      res.add_scrutinee(name, &ty, 0);
      res.local_context.insert(name, ty);      
    }
    res
  }

  pub fn clone(&self) -> Self {
      Goal {
        name: self.name.clone(),
        egraph: self.egraph.clone(),
        // If we reach this point, I think we won't have an explanation
        explanation: None,
        reductions: self.reductions.clone(),
        lemmas: self.lemmas.iter().chain(self.lemmas.iter()).cloned().collect(),
        local_context: self.local_context.clone(),
        ty_splits: self.ty_splits.clone(),
        params: self.params.clone(),
        guard_exprs: self.guard_exprs.clone(),
        scrutinees: self.scrutinees.clone(),
        prev_var_instantiations: self.prev_var_instantiations.clone(),
        vars: self.vars.clone(),
        vars_descendents: self.vars_descendents.clone(),
        lhs: self.lhs.clone(),
        lhs_sexp: self.lhs_sexp.clone(),
        // lhs: var_rec_expr.clone(),
        lhs_id: self.lhs_id,
        // Putting a dummy value for now; We'll set this later once we create con_app.
        rhs: self.rhs.clone(),
        rhs_sexp: self.rhs_sexp.clone(),
        rhs_id: self.rhs_id,
        env: self.env.clone(),
        global_context: self.global_context.clone(),
        // NOTE: We don't really need to clone this.
        defns: self.defns.clone(),
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

  /// Have we proven that lhs == rhs?
  pub fn done(&self) -> bool {
    self.egraph.find(self.lhs_id) == self.egraph.find(self.rhs_id)
  }

  /// Saturate the goal by applying all available rewrites
  pub fn saturate(mut self) -> Self {
    // FIXME: don't collect/clone?
    let lemmas: Vec<Rw> = self.lemmas.iter().map(|(name, lhs, rhs, cond)| Rewrite::new(name, lhs.clone(), ConditionalApplier { applier: rhs.clone(), condition: cond.clone() }).unwrap()).collect();
    let rewrites = self.reductions.iter().chain(lemmas.iter());
    let mut runner = Runner::default().with_explanations_enabled().with_egraph(self.egraph).run(rewrites);
    if runner.egraph.find(self.lhs_id) == runner.egraph.find(self.rhs_id) {
      self.explanation = Some(runner.explain_equivalence(&self.lhs, &self.rhs))
    }
    self.egraph = runner.egraph;
    self
  }

  /// Check whether an expression is reducible using this goal's reductions
  pub fn is_reducible(&self, expr: &Expr) -> bool {
    let mut local_graph: Eg = Default::default();
    local_graph.add_expr(expr);
    local_graph.rebuild();
    for reduction in &self.reductions {
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
    for rhs_expr in exprs.get(&rhs_id).unwrap() {
      // warn!("equivalence for lemma rhs {} and goal rhs: {}", rhs_expr, self.egraph.explain_equivalence(rhs_expr, &self.rhs).get_flat_string());
    }
    for lhs_expr in exprs.get(&lhs_id).unwrap() {
      // warn!("equivalence for lemma lhs {} and goal lhs: {}", lhs_expr, self.egraph.explain_equivalence(lhs_expr, &self.lhs).get_flat_string());
      let lhs: Pattern<SymbolLang> = to_pattern(lhs_expr, is_var);
      if (CONFIG.irreducible_only && self.is_reducible(lhs_expr)) || has_guard_wildcards(&lhs) {
        continue;
      }
      for rhs_expr in exprs.get(&rhs_id).unwrap() {
        if state.timeout() { return rewrites; }
        let rhs: Pattern<SymbolLang> = to_pattern(rhs_expr, is_var);
        if (CONFIG.irreducible_only && self.is_reducible(rhs_expr)) || has_guard_wildcards(&rhs) {
          continue;
        }
        let condition = SmallerVar {
          scrutinees: self.scrutinees.iter().cloned().collect(),
          ty_splits: self.ty_splits.clone(),
        };
        let mut added_lemma = false;
        if rhs.vars().iter().all(|x| lhs.vars().contains(x)) {
          // if rhs has no extra wildcards, create a lemma lhs => rhs
          self.add_lemma(lhs.clone(), rhs.clone(), condition.clone(), &mut rewrites);
          added_lemma = true;
          if CONFIG.single_rhs { continue };
        }
        if lhs.vars().iter().all(|x| rhs.vars().contains(x)) {
          // if lhs has no extra wildcards, create a lemma rhs => lhs
          self.add_lemma(rhs.clone(), lhs.clone(), condition, &mut rewrites);
          added_lemma = true;
          if CONFIG.single_rhs { continue };
        }
        if !added_lemma {
          warn!("cannot create a lemma from {} and {}", lhs, rhs);
        }
      }
    }
    rewrites        
  }

  /// Create rewrites `lhs => lhs'` and `rhs => rhs'` which will be used with the IH in lieu of cyclic lemmas.
  fn mk_half_lemma_rewrites(&mut self, state: &ProofState) -> Vec<(String, Pat, Pat, SmallerVar)> {
    let lhs_id = self.egraph.find(self.lhs_id);
    let rhs_id = self.egraph.find(self.rhs_id);
    let exprs = get_all_expressions(&self.egraph, vec![lhs_id, rhs_id]);
    let is_var = |v| self.local_context.contains_key(v);

    let original_lhs_sexp = parser::parse_str(&self.lhs.to_string()).unwrap();
    let resolved_original_lhs_sexp = resolve_sexp(&original_lhs_sexp, &self.ty_splits);
    let resolved_original_lhs: Expr = resolved_original_lhs_sexp.to_string().parse().unwrap();
    let resolved_original_lhs_pat: Pattern<SymbolLang> = to_pattern(&resolved_original_lhs, is_var);

    let original_rhs_sexp = parser::parse_str(&self.rhs.to_string()).unwrap();
    let resolved_original_rhs_sexp = resolve_sexp(&original_rhs_sexp, &self.ty_splits);
    let resolved_original_rhs: Expr = resolved_original_rhs_sexp.to_string().parse().unwrap();
    let resolved_original_rhs_pat: Pattern<SymbolLang> = to_pattern(&resolved_original_rhs, is_var);

    let mut rewrites = vec![];
    for lhs_expr in exprs.get(&lhs_id).unwrap() {
      if state.timeout() { return rewrites; }
      let lhs: Pattern<SymbolLang> = to_pattern(lhs_expr, is_var);
      if lhs == resolved_original_lhs_pat {
        continue;
      }
      if (CONFIG.irreducible_only && self.is_reducible(lhs_expr)) || has_guard_wildcards(&lhs) {
        continue;
      }
      let condition = SmallerVar {
        scrutinees: self.scrutinees.iter().cloned().collect(),
        ty_splits: self.ty_splits.clone(),
      };
      let mut added_lemma = false;
      if resolved_original_lhs_pat.vars().iter().all(|x| lhs.vars().contains(x)) {
        // if original_lhs has no extra wildcards, create a lemma lhs => original_lhs
        self.add_lemma(lhs.clone(), resolved_original_lhs_pat.clone(), condition.clone(), &mut rewrites);
        added_lemma = true;
      }
      if !added_lemma {
        warn!("cannot create a lemma from {} and {}", lhs, resolved_original_lhs_pat);
      }
    }
    for rhs_expr in exprs.get(&rhs_id).unwrap() {
      if state.timeout() { return rewrites; }
      let rhs: Pattern<SymbolLang> = to_pattern(rhs_expr, is_var);
      if rhs == resolved_original_rhs_pat {
        continue;
      }
      if (CONFIG.irreducible_only && self.is_reducible(rhs_expr)) || has_guard_wildcards(&rhs) {
        continue;
      }
      let condition = SmallerVar {
        scrutinees: self.scrutinees.iter().cloned().collect(),
        ty_splits: self.ty_splits.clone(),
      };
      let mut added_lemma = false;
      if resolved_original_rhs_pat.vars().iter().all(|x| rhs.vars().contains(x)) {
        // if original_rhs has no extra wildcards, create a lemma rhs => original_rhs
        self.add_lemma(rhs.clone(), resolved_original_rhs_pat.clone(), condition.clone(), &mut rewrites);
        added_lemma = true;
      }
      if !added_lemma {
        warn!("cannot create a lemma from {} and {}", rhs, resolved_original_rhs_pat);
      }
    }
    rewrites
  }

  /// Add a rewrite `lhs => rhs` to `rewrites` if not already present
  fn add_lemma(&self, lhs: Pat, rhs: Pat, cond: SmallerVar, rewrites: &mut Vec<(String, Pat, Pat, SmallerVar)>) {
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
    let constants = vec![Symbol::from(TRUE), Symbol::from(FALSE)];
    // Iterator over all reducible symbols (i.e. Boolean constants and scrutinees)
    let reducible = self.scrutinees.iter().chain(constants.iter());
    // Pattern "(ite ?g ?x ?y)"
    let searcher: Pattern<SymbolLang> = format!("({} {} ?x ?y)", ITE, guard_var).parse().unwrap();
    let matches = searcher.search(&self.egraph);
    // Collects class IDs of all irreducible guards;
    // it's a map because the same guard can match more than once, but we only want to add a new scrutinee once
    let mut irreducible_guards = HashMap::new();
    for m in matches {
      for subst in m.substs {
        let guard_id = subst.get(guard_var).unwrap().clone();
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
      warn!("adding scrutinee {} to split condition {}", fresh_var, expr);      
      self.local_context.insert(fresh_var, BOOL_TYPE.parse().unwrap());
      // We are adding the new scrutinee to the front of the deque,
      // because we want to split conditions first, since they don't introduce new variables
      self.scrutinees.push_front(fresh_var);
      let new_node = SymbolLang::leaf(fresh_var);
      let new_pattern_ast = vec![ENodeOrVar::ENode(new_node.clone())].into();
      let new_id = self.egraph.add(SymbolLang::leaf(fresh_var));
      let guard_var_pattern_ast = vec![ENodeOrVar::Var(guard_var)].into();
      self.guard_exprs.insert(fresh_var.to_string(), expr.to_string());
      self.egraph.union_instantiations(&guard_var_pattern_ast, &new_pattern_ast, &subst, "add guard scrutinee");
    }
    self.egraph.rebuild();
  }

  /// Consume this goal and add its case splits to the proof state
  fn case_split(mut self, state: &mut ProofState, mk_lemmas: bool) {
    let lemmas = if mk_lemmas {
      self.mk_lemma_rewrites(state)
    } else {
      vec!()
    };
    // if mk_lemmas {
    //   for lemma in &lemmas {
    //     warn!("Creating lemma {}", lemma.0);
    //   }
    // }

    // let half_lemmas = self.mk_half_lemma_rewrites(state);
    // for lemma in &half_lemmas {
    //   warn!("Creating half lemma {}", lemma.0);
    // }
    // let half_lemmas = vec!();

    // Get the next variable to case-split on
    let var = self.scrutinees.pop_front().unwrap();
    let var_str = var.to_string();
    warn!("case-split on {}", var);
    let var_node = SymbolLang::leaf(var);
    let var_rec_expr: RecExpr<SymbolLang> = vec!(var_node.clone()).into();
    let var_pattern_ast: RecExpr<ENodeOrVar<SymbolLang>> = vec!(ENodeOrVar::ENode(var_node.clone())).into();
    let var_id = self.egraph.lookup(var_node).unwrap();
    // Get the type of the variable, and then remove the variable
    if let None = self.local_context.get(&var) {
      panic!("{} not in local context", var);
    }
    let ty = self.local_context.get(&var).unwrap();
    // Convert to datatype name
    let dt = Symbol::from(ty.datatype().unwrap());
    // Get the constructors of the datatype
    let (_, cons) = self.env.get(&dt).unwrap();
    // We will add this to state.proof to describe the case split.
    let mut instantiated_cons_and_goals: Vec<(String, String)> = vec!();
    // For each constructor, create a new goal and push it onto the proof state
    // (we process constructors in reverse order so that base case ends up at the top of the stack)
    for &con in cons.iter().rev() {
      let mut new_goal = Goal {
        name: format!("{}:", self.name),
        egraph: self.egraph.clone(),
        // If we reach this point, I think we won't have an explanation
        explanation: None,
        reductions: self.reductions.clone(),
        lemmas: self.lemmas.iter().chain(lemmas.iter()).cloned().collect(),
          // self.lemmas.iter().chain(half_lemmas.iter()).cloned().collect(),
        local_context: self.local_context.clone(),
        ty_splits: self.ty_splits.clone(),
        params: self.params.clone(),
        guard_exprs: self.guard_exprs.clone(),
        scrutinees: self.scrutinees.clone(),
        prev_var_instantiations: self.prev_var_instantiations.clone(),
        vars: self.vars.clone(),
        vars_descendents: self.vars_descendents.clone(),
        lhs: self.lhs.clone(),
        // lhs: var_rec_expr.clone(),
        lhs_id: self.lhs_id,
        lhs_sexp: self.lhs_sexp.clone(),
        // Putting a dummy value for now; We'll set this later once we create con_app.
        rhs: self.rhs.clone(),
        rhs_id: self.rhs_id,
        rhs_sexp: self.rhs_sexp.clone(),
        env: self.env.clone(),
        global_context: self.global_context.clone(),
        defns: self.defns.clone(),
      };      

      // Get the types of constructor arguments
      let con_ty = self.global_context.get(&con).unwrap();
      let con_args = Goal::instantiate_constructor(con_ty, ty);
      // For each argument: create a fresh variable and add it to the context and to scrutinees
      let mut fresh_vars = vec![];
      // let mut instantiated_egraphs = vec![];

      // FIXME: Hack to deal with modification that happens inside the next for
      // loop. Maybe the right thing to do is to just keep a temporary vec of
      // what vars we're adding and add it after we're done iterating, like with
      // fresh_vars.
      let vars_clone = self.vars.clone();
      let parent_vars = find_parent_vars(&vars_clone, &var_str);
      for i in 0..con_args.len() {
        let fresh_var_name = format!("{}_{}{}", var, self.egraph.total_size(), i);
        let depth = var_depth(&fresh_var_name[..]);
        let fresh_var = Symbol::from(fresh_var_name.clone());
        fresh_vars.push(fresh_var);
        // Add new variable to context
        let arg_type = &con_args[i];
        new_goal.local_context.insert(fresh_var, arg_type.clone());
        new_goal.add_scrutinee(fresh_var, arg_type, depth);
        new_goal.vars.push((fresh_var_name.clone(), arg_type.clone()));
        new_goal.vars_descendents.insert(fresh_var_name.clone(), vec!(fresh_var_name.clone()));
        for (parent_var, parent_var_type) in parent_vars.iter() {
          // This var is a descendent of each ancestor.
          if arg_type == parent_var_type {
            if let Some(descendents) = new_goal.vars_descendents.get_mut(parent_var) {
              descendents.push(fresh_var_name.clone());
            } else {
              new_goal.vars_descendents.insert(parent_var.clone(), vec!(parent_var.clone(), fresh_var_name.clone()));
            }
          }
        }
        if !mk_lemmas {
          let ancestors: Vec<String> = self.vars.iter().flat_map(|(ancestor_var, ancestor_type)|{
            if ancestor_type == arg_type {
              Some(ancestor_var.clone())
            } else {
              None
            }
          }).collect();
          instantiate_new_ih_equalities(&mut new_goal.egraph, &mut new_goal.prev_var_instantiations,
                                        &fresh_var_name, &ancestors, &new_goal.lhs_sexp, &new_goal.rhs_sexp, &new_goal.params);
        }

        // if arg_type == ty {
        //   warn!("specializing {} to {}", var, fresh_var);
        //   let mut instantiated_egraph = new_goal.egraph.clone();
        //   let new_var_pattern_ast: RecExpr<ENodeOrVar<SymbolLang>> = vec!(ENodeOrVar::ENode(SymbolLang::leaf(fresh_var))).into();
        //   instantiated_egraph.union_instantiations(&var_pattern_ast, &new_var_pattern_ast, &Subst::default(), format!("{} specialize lemmas", new_goal.name));
        //   instantiated_egraph.rebuild();
        //   // Remove the variable from the egraph
        //   remove_node(&mut instantiated_egraph, &SymbolLang::leaf(var));
        //   instantiated_egraphs.push(instantiated_egraph);
        // }
      }

      // Create an application of the constructor to the fresh vars
      let fresh_var_strings_iter = fresh_vars.iter().map(|x| x.to_string());
      let con_app_string = format!("({} {})", con, fresh_var_strings_iter.clone().collect::<Vec<String>>().join(" "));
      let con_app_sexp = parser::parse_str(&con_app_string).unwrap();
      new_goal.ty_splits.insert(var_str.clone(), con_app_sexp.clone());
      add_con_app_to_prev_instantiations(&mut new_goal.prev_var_instantiations, &var_str, &con_app_sexp, fresh_var_strings_iter);
      for lemma in new_goal.lemmas.iter_mut() {
        lemma.3.ty_splits.insert(var_str.clone(), con_app_sexp.clone());
      }
      let con_app: Expr = con_app_string.parse().unwrap();
      // new_goal.rhs = con_app.clone();

      new_goal.name = format!("{}{}={}", new_goal.name, var, con_app);

      instantiated_cons_and_goals.push((con_app_string, new_goal.name.clone()));

      // Add con_app to the new goal's egraph and union it with var
      new_goal.egraph.add_expr(&con_app);
      let con_app_id = new_goal.egraph.lookup_expr(&con_app).unwrap();
      // Not sure if it's proper to use new_goal.name here
      new_goal.egraph.union_instantiations(&var_pattern_ast, &rec_expr_to_pattern_ast(con_app), &Subst::default(), new_goal.name.clone());
      new_goal.egraph.rebuild();

      // Remove old variable from the egraph and context
      remove_node(&mut new_goal.egraph, &SymbolLang::leaf(var));
      warn!("removing var {}", var);
      new_goal.local_context.remove(&var);
      new_goal.egraph.rebuild();

      // println!("egraph size before: {}", new_goal.egraph.total_size());
      // println!("egraph before: {:?}", new_goal.egraph); //new_goal.egraph.classes().map(|class| format!("{:?}", class)).collect::<String>());
      // // Union the other lemma instantiations
      // for instantiated_egraph in instantiated_egraphs {
      //   // new_goal.egraph.egraph_union(&instantiated_egraph);
      //   let right_unions = instantiated_egraph.get_union_equalities();
      //   for (left, right, why) in right_unions {
      //     let left_pattern = instantiated_egraph.id_to_pattern(left, &Default::default()).0.ast;
      //     let right_pattern = instantiated_egraph.id_to_pattern(right, &Default::default()).0.ast;
      //     if left_pattern == var_pattern_ast || right_pattern == var_pattern_ast {
      //       continue;
      //     }
      //     println!("union between {} and {}", left_pattern, right_pattern);
      //     new_goal.egraph.union_instantiations(
      //       &left_pattern,
      //       &right_pattern,
      //       &Default::default(),
      //       why,
      //     );
      //   }
      //   new_goal.egraph.rebuild();
      // }
      // println!("egraph size after: {}", new_goal.egraph.total_size());
      // println!("egraph after: {}", new_goal.egraph.classes().map(|class| format!("{:?}", class)).collect::<String>());

      // if !mk_lemmas {
      //   instantiate_descendent_lhs_and_rhs(&mut new_goal.egraph, &self.lhs, &self.rhs, &new_goal.vars_descendents);
      //   new_goal.egraph.rebuild();
      // }

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
      state.proof.insert(self.name, ProofTerm::ITESplit(var_str.clone(), self.guard_exprs[&var_str].clone(), instantiated_cons_and_goals));
    // Otherwise, we are doing a case split on a variable.
    } else {
      state.proof.insert(self.name, ProofTerm::CaseSplit(var_str.clone(), instantiated_cons_and_goals));
    }
  }

  /// Save e-graph to file
  fn save_egraph(&self) {
    let filename = format!("target/{}.png", self.name);
    let verbosity = format!("-q{}", CONFIG.log_level as usize);
    let dot = self.egraph.dot();    
    dot.run_dot(&["-Tpng", verbosity.as_str(), "-o", filename.as_str()]).unwrap();
  }

  /// Given a polymorphic constructor type and a concrete instantiation of a datatype,
  /// return the concrete types of constructor arguments.
  fn instantiate_constructor(con_ty: &Type, actual: &Type) -> Vec<Type> {
    let (args, ret) = con_ty.args_ret();

    // Add the actual datatype to a fresh egraph
    let mut egraph: Eg = Default::default();
    let actual_as_expr: Expr = format!("{}", actual).parse().unwrap();
    egraph.add_expr(&actual_as_expr);
    egraph.rebuild();

    // Create a pattern from the generic return type of the constructor
    let searcher: Pat = format!("{}", ret).parse().unwrap();
    let vars = searcher.vars();
    // This pattern should have a single match in the actual datatype (at the root)
    let matches = searcher.search(&egraph);
    assert_eq!(matches.len(), 1);
    assert_eq!(matches[0].substs.len(), 1);
    let subst = &matches[0].substs[0];
    // Convert the substitution range from eclass ids to expressions
    // (each one of these eclasses stores a single expression, since we only added the actual)
    let extractor = Extractor::new(&egraph, AstSize);
    let expr_subst = vars.iter().zip(vars.iter().map(|v| extractor.find_best(*subst.get(*v).unwrap()).1)).collect::<Vec<_>>();

    let mut res = vec![];
    // For each argument, substitute all vars with their values in expr subst
    // (we do it using string replacement because RecExprs are so painful to work with;
    // I tried to do this substitution in the egraph, but that creates problems with cycles)
    for arg in args {
      let mut arg_string = format!("{}", arg);
      for (var, t) in expr_subst.iter() {
        arg_string = arg_string.replace(&format!("{}", var), &format!("{}", t));
      }
      res.push(arg_string.parse().unwrap());
    }
    res
  }

  /// Checks to see if we will prove True = False by proving this goal (or if it
  /// has already been proven).
  fn is_impossible(&self) -> bool {
    let true_symb = Symbol::from(TRUE);
    let false_symb = Symbol::from(FALSE);
    let true_e_class_opt = self.egraph.lookup(SymbolLang::leaf(true_symb));
    let false_e_class_opt = self.egraph.lookup(SymbolLang::leaf(false_symb));
    let lhs_id = self.egraph.find(self.lhs_id);
    let rhs_id = self.egraph.find(self.rhs_id);
    if let Some(true_e_class) = true_e_class_opt {
      if let Some(false_e_class) = false_e_class_opt {
        // println!("checking impossible: lhs_id:{} rhs_id:{} true_id:{} false_id:{}", lhs_id, rhs_id, true_e_class, false_e_class);
        return true_e_class == false_e_class
          || (true_e_class == lhs_id && false_e_class == rhs_id)
          || (true_e_class == rhs_id && false_e_class == lhs_id);
      }
    }
    return false;
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
  // TODO: ITE splitting (probably can just get away with having a node like
  // ITEIntro(String, Sexp, String) which we can implement as a let, e.g.
  //   let g = x <= y in ...
  // where ... corresponds to the CaseSplit goal identified by the last String.
  ITESplit(String, String, Vec<(String, String)>),
}

/// A proof state is a list of subgoals,
/// all of which have to be discharged
pub struct ProofState {
  pub goals: Vec<Goal>,
  pub solved_goal_explanations: HashMap<String, Explanation<SymbolLang>>,
  pub impossible_goals: HashSet<String>,
  pub proof: HashMap<String, ProofTerm>,
  pub start_time: Instant,
}

impl ProofState {
  // Has timeout been reached?
  pub fn timeout(&self) -> bool {
    CONFIG.timeout.is_some() && self.start_time.elapsed() > Duration::new(CONFIG.timeout.unwrap(), 0)
  }
}

/// Pretty-printed proof state
pub fn pretty_state(state: &ProofState) -> String {
  format!("[{}]", state.goals.iter().map(|g| g.name.clone()).collect::<Vec<String>>().join(", "))
}

/// Outcome of a proof attempt
#[derive(Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum Outcome {
  Valid,
  Invalid,
  Unknown,
  Timeout
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
    let child_rec_exprs: String = lhs_node.children.iter().map(|child_id|{
      let (_, best_rec_expr) = extractor.find_best(*child_id);
      best_rec_expr.to_string()
    }).collect::<Vec<String>>().join(" ");
    if child_rec_exprs.is_empty() {
      println!("({})", lhs_node);
    }
    println!("({} {})", lhs_node, child_rec_exprs);
  }
  println!("{}", "RHS Nodes".cyan());
  for rhs_node in goal.egraph[goal.rhs_id].nodes.iter() {
    let child_rec_exprs: String = rhs_node.children.iter().map(|child_id|{
      let (_, best_rec_expr) = extractor.find_best(*child_id);
      best_rec_expr.to_string()
    }).collect::<Vec<String>>().join(" ");
    if child_rec_exprs.is_empty() {
      println!("({})", rhs_node);
    }
    println!("({} {})", rhs_node, child_rec_exprs);
  }
}

/// Top-level interface to the theorem prover.
pub fn prove(mut goal: Goal, make_cyclic_lemmas: bool) -> (Outcome, ProofState) {
  // let initial_goal_name = goal.name.clone();
  let mut state = ProofState { goals: vec![goal], solved_goal_explanations: HashMap::default(), impossible_goals: HashSet::default(), proof: HashMap::default(), start_time: Instant::now() };
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
    if let Some(mut explanation) = goal.explanation {
       // This goal has been discharged, proceed to the next goal
       if CONFIG.verbose {
         println!("{} {}", "Proved case".bright_blue(), goal.name);
         println!("{}", explanation.get_flat_string());
       }
      state.solved_goal_explanations.insert(goal.name, explanation);
      continue;
    }
    if CONFIG.verbose {
      explain_goal_failure(&goal);
    }
    // if goal.is_impossible() {
    //   if CONFIG.verbose {
    //     println!("{} {}: {}", "Proved case".bright_blue(), goal.name, "IMPOSSIBLE".bright_red());
    //   }
    //   state.impossible_goals.insert(goal.name);
    //   continue;
    // }
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
    let goal_name = goal.name.clone();
    // We used to always add lemmas if the goal was the initial goal, but now we never
    // do it if make_cyclic_lemmas is false because we manually union the e-classes.
    goal.case_split(&mut state, make_cyclic_lemmas);
    if CONFIG.verbose {
      println!("{}", "Case splitting and continuing...".purple());
    }
  }
  // All goals have been discharged, so the conjecture is valid:
  (Outcome::Valid, state)
}
