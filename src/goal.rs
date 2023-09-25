use colored::Colorize;
use egg::*;
use log::warn;
use std::collections::HashSet;
use std::collections::{hash_map::Entry, HashMap, VecDeque};
use std::fmt::Display;
use std::time::{Duration, Instant};
use symbolic_expressions::{parser, Sexp};

use crate::ast::*;
use crate::config::*;
use crate::egraph::*;
use crate::parser::RawEquation;

// We will use SymbolLang for now
pub type Eg = EGraph<SymbolLang, CanonicalFormAnalysis>;
pub type Rw = Rewrite<SymbolLang, CanonicalFormAnalysis>;

/// A special scrutinee name used to signal that case split bound has been exceeded
const BOUND_EXCEEDED: &str = "__";
pub const LEMMA_PREFIX: &str = "lemma-";
pub const IH_EQUALITY_PREFIX: &str = "ih-equality-"; // TODO: remove

/// Condition that checks whether the substitution is into a smaller tuple of variable
#[derive(Clone)]
pub struct SmallerVar {
  /// Lemma's free variables
  pub free_vars: Vec<Symbol>,
  /// A substitution from free variables
  /// to the original e-classes these variables came from
  pub initial_subst: Subst,
  /// TODO: remove this
  pub ty_splits: SSubst,
  /// All premises that must hold for this lemma to apply,
  /// expressed in terms of the free variables variables
  pub premises: Vec<Equation>,
}

impl SmallerVar {
  /// Substitution as a string, for debugging purposes
  fn pretty_subst(subst: &Vec<(Symbol, Expr, Expr)>) -> String {
    let strings: Vec<String> = subst
      .iter()
      .map(|(x, orig, new)| {
        format!(
          "{} = {} -> {}",
          &x.to_string(),
          &orig.to_string(),
          &new.to_string()
        )
      })
      .collect();
    strings.join(", ")
  }

  /// Are the canonical forms of the e-classes in new_subst strictly smaller than those in orig_subst?
  /// For now implements a sound but incomplete measure,
  /// where all forms need to be no larger, and at least one has to be strictly smaller.
  fn smaller_tuple(&self, triples: &Vec<(Symbol, Expr, Expr)>) -> bool {
    let mut has_strictly_smaller = false;
    for (_, orig, new) in triples {
      match is_subterm(&new, &orig) {
        StructuralComparison::LT => {
          has_strictly_smaller = true;
        }
        StructuralComparison::Incomparable => {
          return false;
        }
        _ => (),
      }
    }
    // let info = SmallerVar::pretty_subst(subst.as_slice());
    // for (var, expr) in subst {
    //   let var_name = var.to_string();
    //   let expr_name = expr.to_string();
    //   if CONFIG.structural_comparison {
    //     // Suppose a cyclic lemma is defined over the variable l0
    //     //
    //     // Suppose also that
    //     //   - After a case split, l0 = Cons x1 l1
    //     //   - After a second case split, l1 = Cons x2 l2
    //     //
    //     // With a structural comparison, we will allow the cyclic lemma to be
    //     // used on Cons x1 Nil, because we know that Nil is always smaller than
    //     // l1.
    //     //
    //     // In practice, this is probably not often useful.
    //     let sexp = parser::parse_str(&expr_name).unwrap();
    //     if contains_function(&sexp) {
    //       return false;
    //     }
    //     let var_sexp = &fix_singletons(recursively_resolve_variable(&var_name, &self.ty_splits));
    //     let structural_comparison_result = structural_comparision(&sexp, var_sexp);
    //     // warn!("structurally comparing {} to var {} (resolved to {}), result: {:?}", sexp, var_name, var_sexp, structural_comparison_result);
    //     if let StructuralComparison::LT = structural_comparison_result {
    //       // warn!("{} is smaller than {}", sexp, var_name);
    //       has_strictly_smaller = true;
    //     } else if let StructuralComparison::Incomparable = structural_comparison_result {
    //       warn!(
    //         "cannot apply lemma with subst [{}], reason: {:?}",
    //         info, structural_comparison_result
    //       );
    //       return false;
    //     }
    //   } else {
    //     // In this branch we only check if the arguments are variables or
    //     // directly matching constructors.
    //     if is_descendant(&expr_name, &var_name) {
    //       // Target is strictly smaller than source
    //       has_strictly_smaller = true;
    //     } else if expr_name != var_name {
    //       // Target is neither strictly smaller nor equal to source
    //       // warn!("cannot apply lemma with subst [{}]", info);
    //       return false;
    //     }
    //   }
    // }
    // if has_strictly_smaller {
    //   warn!("applying lemma with subst [{}]", new_subst);
    // } else {
    //   warn!("cannot apply lemma with subst [{}]", new_subst);
    // }
    has_strictly_smaller
  }

  /// Apply subst to self.premise (if any)
  /// and check whether the resulting terms are equal in the egraph
  fn check_premise(
    premise: &Equation,
    triples: &Vec<(Symbol, Expr, Expr)>,
    egraph: &mut Eg,
  ) -> bool {
    // let info = SmallerVar::pretty_subst(triples);
    // println!("checking premise {} = {} for {}", premise.lhs.sexp, premise.rhs.sexp, info);

    // TODO: it's annoying having to convert everything to s-expressions and back
    // but substituting over RecExprs is too much of a pain
    // Convert triples to a substitution over s-expressions
    let subst: SSubst = triples
      .iter()
      .map(|(var, _, new_expr)| {
        (
          var.to_string(),
          symbolic_expressions::parser::parse_str(&new_expr.to_string()).unwrap(),
        )
      })
      .collect();

    // Perform the substitution
    let lhs: Expr = resolve_sexp(&premise.lhs.sexp, &subst)
      .to_string()
      .parse()
      .unwrap();
    let rhs: Expr = resolve_sexp(&premise.rhs.sexp, &subst)
      .to_string()
      .parse()
      .unwrap();

    // Lookup the sides of the new premise in the egraph;
    // they must be there, since we added them during grounding
    if let Some(lhs_id) = egraph.lookup_expr(&lhs) {
      if let Some(rhs_id) = egraph.lookup_expr(&rhs) {
        // println!("{} == {}", lhs_id, rhs_id);
        return lhs_id == rhs_id;
      }
    }
    // TODO: this should be a panic because we should have added all premises during grounding
    // panic!("premise {} = {} not found in egraph", lhs, rhs);
    false
  }

  /// Check all of the premises of this condition
  fn check_premises(&self, triples: &Vec<(Symbol, Expr, Expr)>, egraph: &mut Eg) -> bool {
    self
      .premises
      .iter()
      .all(|premise| SmallerVar::check_premise(premise, triples, egraph))
  }
}

impl Condition<SymbolLang, CanonicalFormAnalysis> for SmallerVar {
  /// Returns true if the substitution is into a smaller tuple of variables
  fn check(&self, egraph: &mut Eg, _eclass: Id, subst: &Subst) -> bool {
    // Create an iterator over triples: (variable, old canonical form, new canonical form)
    let triples = self
      .free_vars
      .iter()
      .map(|x| {
        let v = to_wildcard(x);
        // Subst must have all lemma variables defined
        // because we did the filtering when creating SmallerVars
        let new_id = subst.get(v).unwrap();
        let orig_id = self.initial_subst.get(v).unwrap();
        // If the actual argument of the lemma is not canonical, give up
        let new_canonical = CanonicalFormAnalysis::extract_canonical(egraph, *new_id)?;
        // Same for the original argument:
        // it might not be canonical if it's inconsistent, in which case there's no point applying any lemmas
        let orig_canonical = CanonicalFormAnalysis::extract_canonical(egraph, *orig_id)?;
        Some((x.clone(), orig_canonical, new_canonical))
      })
      .collect::<Option<Vec<(Symbol, Expr, Expr)>>>();

    match triples {
      None => false, // All actual arguments must be canonical in order to be comparable to the formals
      Some(triples) => {
        // Check that the actuals are smaller than the formals
        // and that the actual premise holds
        let terminates = self.smaller_tuple(&triples);
        // Let's not check the premises if the termination check doesn't hold:
        let sound = terminates && self.check_premises(&triples, egraph);
        // println!("trying IH with subst {}; checks: {} {}", SmallerVar::pretty_subst(&triples), terminates, sound);
        sound
      }
    }
  }
}

/// The set of constructors in an e-class.
/// The order of variants is important: since we use the derived order during the merge.
#[derive(Debug, PartialEq, PartialOrd, Eq, Ord, Clone)]
pub enum CanonicalForm {
  /// This class has neither constructors nor variables
  Stuck,
  /// This class has a variable but no constructors
  Var(SymbolLang),
  /// This class has a single constructor;
  /// because the analysis merges the children of the same constructor,
  /// there cannot be two different constructor e-nodes with the same head constructor in an e-class.
  Const(SymbolLang),
  /// This class has at least two different constructors
  /// or it contains an infinite term (this class is reachable from an argument of its constructor);
  /// in any case, this is an inconsistency.
  Inconsistent(SymbolLang, SymbolLang),
}

#[derive(Default, Clone)]
pub struct CanonicalFormAnalysis {}

impl CanonicalFormAnalysis {
  /// Extract the canonical form of an e-class if it exists.
  /// Note: this function does not check for cycles, so it should only be called
  /// after the analysis has finished.
  pub fn extract_canonical(egraph: &Eg, id: Id) -> Option<Expr> {
    match &egraph[id].data {
      CanonicalForm::Const(n) => {
        // Extract canonical forms of the children:
        let children: HashMap<Id, Expr> =
          n.children
            .iter()
            .try_fold(HashMap::new(), |mut acc, child| {
              let child_expr = Self::extract_canonical(egraph, *child)?;
              acc.insert(*child, child_expr);
              Some(acc)
            })?;
        // Join those forms into a single expression:
        let expr = n.join_recexprs(|child_id| children.get(&child_id).unwrap());
        Some(expr)
      }
      CanonicalForm::Var(n) => Some(vec![n.clone()].into()),
      _ => None,
    }
  }

  /// Check if the canonical form of eclass id (whose constructor node is n)
  /// has a cycle back to itself made up of only constructors.
  /// This means that the eclass represents an infinite term.
  fn is_canonical_cycle(egraph: &Eg, n: &SymbolLang, id: Id) -> bool {
    // We have to keep track of visited nodes because there might also be a lasso
    // (i.e. a cycle not starting at id)
    let mut visited: HashSet<Id> = HashSet::new();
    visited.insert(id);
    Self::is_reachable(egraph, n, id, &mut visited)
  }

  fn is_reachable(egraph: &Eg, n: &SymbolLang, id: Id, visited: &mut HashSet<Id>) -> bool {
    n.children.iter().any(|c| {
      let c = egraph.find(*c);
      if c == id {
        true
      } else if visited.contains(&c) {
        // We return false here because a) this might just be a DAG and
        // b) if there is a cycle at c, it will be detected in c's modify call
        false
      } else {
        visited.insert(c);
        if let CanonicalForm::Const(n2) = &egraph[c].data {
          Self::is_reachable(egraph, n2, id, visited)
        } else {
          false
        }
      }
    })
  }
}

impl Analysis<SymbolLang> for CanonicalFormAnalysis {
  type Data = CanonicalForm;

  fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
    // If we are merging classes with two different constructors,
    // record that this class is now inconsistent
    // (and remember both constructors, we'll need them to build an explanation)
    if let CanonicalForm::Const(n1) = to {
      if let CanonicalForm::Const(ref n2) = from {
        if n1.op != n2.op {
          *to = CanonicalForm::Inconsistent(n1.clone(), n2.clone());
          return DidMerge(true, true);
        }
      }
    }
    // Otherwise, just take the max constructor set
    merge_max(to, from)
  }

  fn make(_: &EGraph<SymbolLang, Self>, enode: &SymbolLang) -> Self::Data {
    if is_constructor(enode.op.into()) {
      CanonicalForm::Const(enode.clone())
    } else if enode.children.is_empty() {
      CanonicalForm::Var(enode.clone())
    } else {
      CanonicalForm::Stuck
    }
  }

  fn modify(egraph: &mut EGraph<SymbolLang, Self>, id: Id) {
    if let CanonicalForm::Const(ref n1) = egraph[id].data {
      let n1 = n1.clone();
      // We have just merged something into a constructor.
      // 1) Check if there are any other constructors in this class with the same head and union their children
      let other_constructors: Vec<SymbolLang> = egraph[id]
        .nodes
        .iter()
        .filter(|n2| n1 != **n2 && n1.op == n2.op)
        .cloned()
        .collect();

      for n2 in other_constructors {
        // The extraction is only here for logging purposes
        let extractor = Extractor::new(egraph, AstSize);
        let expr1 = extract_with_node(&n1, &extractor);
        let expr2 = extract_with_node(&n2, &extractor);
        if CONFIG.verbose && expr1.to_string() != expr2.to_string() {
          println!("INJECTIVITY {} = {}", expr1, expr2);
        }
        // Unify the parameters of the two constructors
        for (c1, c2) in n1.children.iter().zip(n2.children.iter()) {
          let c1 = egraph.find(*c1);
          let c2 = egraph.find(*c2);
          if c1 != c2 {
            egraph.union_trusted(
              c1,
              c2,
              format!("constructor-injective {} = {}", expr1, expr2),
            );
          }
        }
      }
      // 2) Check if we created a cycle made up of only constructors,
      // and if so, report inconsistency (infinite term)
      if Self::is_canonical_cycle(egraph, &n1, id) {
        // The extraction is only here for logging purposes
        let extractor = Extractor::new(egraph, AstSize);
        let n2 = extractor.find_best_node(id);
        let expr1 = extract_with_node(&n1, &extractor);
        let expr2 = extract_with_node(n2, &extractor);
        if CONFIG.verbose {
          println!("INFINITE TERM {} = {}", expr1, expr2);
        }
        egraph[id].data = CanonicalForm::Inconsistent(n1.clone(), n2.clone());
      }
    }
  }
}

/// When we do a case split we will instantiate a variable x to
/// (Cons fresh_var1 fresh_var2 ...). We need to update our prev_instantiations
/// to account for this equality. We will copy each past instantiation and add
/// a new instantiation where instead of assigning x to itself, we will assign it
/// to the sexp. We'll also add assignments of the vars in the constructor to
/// themselves.
fn add_con_app_to_prev_instantiations<I>(
  prev_instantiations: &mut Vec<SSubst>,
  var: &String,
  con_app_sexp: &Sexp,
  app_vars: I,
) where
  I: IntoIterator<Item = String> + Clone,
{
  // These instantiations are equivalent but we need to track them so that
  // we can discover all possible new instantiations when we add a variable.
  let equal_instantiations: Vec<SSubst> = prev_instantiations
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
fn resolve_instantiation(instantiation: &SSubst) -> SSubst {
  let mut resolved_instantiation = HashMap::new();
  for var in instantiation.keys() {
    resolve_var_instantiation(instantiation, &mut resolved_instantiation, var);
  }
  resolved_instantiation
}

fn resolve_var_instantiation(
  instantiation: &SSubst,
  resolved_instantiation: &mut SSubst,
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
fn instantiate_new_ih_terms(
  egraph: &mut Eg,
  prev_instantiations: &mut Vec<SSubst>,
  var: &String,
  var_ancestors: &[String],
  terms: &[&ETerm],
  // params: &[String],
) {
  let new_instantiations: Vec<SSubst> = prev_instantiations
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
    for term in terms.iter() {
      let new_term = recursively_resolve_sexp(&term.sexp, &resolved_instantiation);
      ETerm::new(&new_term, egraph);
    }
  }
  prev_instantiations.extend(new_instantiations);
}

/// A term inside the egraph;
/// we store multiple representations because they are useful for different purposes.
#[derive(Debug, Clone)]
pub struct ETerm {
  /// Term as a symbolic expression
  pub sexp: Sexp,
  /// E-class id of the term in the egraph
  id: Id,
  /// Terms as egg's RecExpr
  pub expr: Expr,
}

impl ETerm {
  /// Create a new term from a symbolic expression
  /// and add it to the egraph
  fn new(sexp: &Sexp, egraph: &mut Eg) -> ETerm {
    let expr = sexp.to_string().parse().unwrap();
    egraph.add_expr(&expr);
    let id = egraph.lookup_expr(&expr).unwrap();
    Self {
      sexp: sexp.clone(),
      id,
      expr,
    }
  }

  fn from_expr(expr: Expr, egraph: &Eg) -> Self {
    let id = egraph.lookup_expr(&expr).unwrap();
    let sexp = parser::parse_str(&expr.to_string()).unwrap();
    Self { sexp, id, expr }
  }
}

impl Display for ETerm {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.sexp)
  }
}

/// An equation is a pair of terms
#[derive(Debug, Clone)]
pub struct Equation {
  pub lhs: ETerm,
  pub rhs: ETerm,
}

impl Display for Equation {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{} === {}", self.lhs.sexp, self.rhs.sexp)
  }
}

impl Equation {
  /// Add both sides of a raw equation to the egraph,
  /// producing an equation;
  /// if assume is true, also union the the two sides
  fn new(eq: &RawEquation, egraph: &mut Eg, assume: bool) -> Self {
    let lhs = ETerm::new(&eq.lhs, egraph);
    let rhs = ETerm::new(&eq.rhs, egraph);
    if assume {
      // Assume the premise
      egraph.union_trusted(lhs.id, rhs.id, format!("premise {}={}", lhs.sexp, rhs.sexp));
      egraph.rebuild();
    }
    Self { lhs, rhs }
  }
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
  lemmas: HashMap<String, (Pat, Pat, SmallerVar)>,
  /// Universally-quantified variables of the goal
  /// (i.e. top-level parameters and binders derived from them through pattern matching)
  pub local_context: Context,
  /// Map from a variable to its split (right now we only track data constructor
  /// splits)
  ty_splits: SSubst,
  /// The top-level parameters to the goal
  pub params: Vec<String>,
  /// Variables we can case-split
  /// (i.e. the subset of local_context that have datatype types)
  scrutinees: VecDeque<Symbol>,
  /// Stores the expression each guard variable maps to. Since we only need
  /// these for proof emission, we just store the expression as a String.
  guard_exprs: HashMap<String, Expr>,
  // TODO: It almost feels like we could use an e-graph to track these past
  // instantiations, but we can't use the main e-graph because there's other stuff
  // that gets put into it.
  prev_var_instantiations: Vec<SSubst>,
  /// The equation we are trying to prove
  pub eq: Equation,
  /// If this is a conditional prop, the premises
  pub premises: Vec<Equation>,
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
    eq: &RawEquation,
    premise: &Option<RawEquation>,
    params: Vec<(Symbol, Type)>,
    env: &'a Env,
    global_context: &'a Context,
    reductions: &'a Vec<Rw>,
    defns: &'a Defns,
  ) -> Self {
    let mut egraph: Eg = EGraph::default().with_explanations_enabled();
    let eq = Equation::new(eq, &mut egraph, false);
    let premise = premise
      .as_ref()
      .map(|eq| Equation::new(eq, &mut egraph, true));

    let mut res = Self {
      name: name.to_string(),
      egraph,
      explanation: None,
      reductions,
      lemmas: HashMap::new(),
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
        .collect::<SSubst>()]
      .into(),
      eq,
      // Convert to a singleton list if the Option is Some, else the empty list
      premises: premise.into_iter().collect(),
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
      lemmas: HashMap::new(), // the lemmas will be re-generated immediately anyway
      local_context: self.local_context.clone(),
      ty_splits: self.ty_splits.clone(),
      params: self.params.clone(),
      guard_exprs: self.guard_exprs.clone(),
      scrutinees: self.scrutinees.clone(),
      prev_var_instantiations: self.prev_var_instantiations.clone(),
      eq: self.eq.clone(),
      premises: self.premises.clone(),
      env: self.env,
      global_context: self.global_context,
      // NOTE: We don't really need to clone this.
      defns: self.defns,
    }
  }

  /// Saturate the goal by applying all available rewrites
  pub fn saturate(mut self) -> Self {
    // FIXME: don't collect/clone?
    let lemmas: Vec<Rw> = self
      .lemmas
      .iter()
      .map(|(name, (lhs, rhs, cond))| {
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
    // for eclass in self.egraph.classes() {
    //   println!("{}: {:?} CANONICAL {}", eclass.id, eclass.nodes, ConstructorFolding::extract_canonical(&self.egraph, eclass.id).unwrap_or(vec![].into()));
    // }

    if self.egraph.find(self.eq.lhs.id) == self.egraph.find(self.eq.rhs.id) {
      // We have shown that LHS == RHS
      self.explanation = Some(
        self
          .egraph
          .explain_equivalence(&self.eq.lhs.expr, &self.eq.rhs.expr),
      );
    } else {
      // Check if this case in unreachable (i.e. if there are any inconsistent e-classes in the e-graph)
      let res = self.egraph.classes().find_map(|eclass| {
        if let CanonicalForm::Inconsistent(n1, n2) = &eclass.data {
          // This is here only for the purpose of proof generation:
          let extractor = Extractor::new(&self.egraph, AstSize);
          let expr1 = extract_with_node(n1, &extractor);
          let expr2 = extract_with_node(n2, &extractor);
          if CONFIG.verbose {
            println!("{}: {} = {}", "UNREACHABLE".bright_red(), expr1, expr2);
          }
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
  fn add_lemma_rewrites(
    &mut self,
    state: &ProofState,
    is_cyclic: bool,
  ) -> HashMap<String, (Pat, Pat, SmallerVar)> {
    let lhs_id = self.egraph.find(self.eq.lhs.id);
    let rhs_id = self.egraph.find(self.eq.rhs.id);
    let is_var = |v| self.local_context.contains_key(v);

    let exprs = if is_cyclic {
      // If we are doing cyclic proofs: make lemmas out of all LHS and RHS variants
      get_all_expressions(&self.egraph, vec![lhs_id, rhs_id])
    } else {
      // Otherwise, only use the original LHS and RHS
      vec![
        (lhs_id, vec![self.eq.lhs.expr.clone()]),
        (rhs_id, vec![self.eq.rhs.expr.clone()]),
      ]
      .into_iter()
      .collect()
    };

    let mut rewrites = self.lemmas.clone();
    for lhs_expr in exprs.get(&lhs_id).unwrap() {
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
        // Pick out those scrutinees that occur in the lemma;
        // this is not strictly necessary, but we'd like to get rid of junk like BOUND_EXCEEDED
        let vars: Vec<Symbol> = self
          .scrutinees
          .iter()
          .filter(|x| lhs.vars().contains(&to_wildcard(x)) || rhs.vars().contains(&to_wildcard(x)))
          .cloned()
          .collect();
        let condition = SmallerVar {
          // create initial subst by looking up the scrutinees in the egraph
          initial_subst: lookup_vars(&self.egraph, vars.iter()),
          free_vars: vars,
          // TODO: Can we take a reference instead of cloning?
          ty_splits: self.ty_splits.clone(),
          premises: self.premises.clone(),
        };
        let mut added_lemma = false;
        if rhs.vars().iter().all(|x| lhs.vars().contains(x)) {
          // if rhs has no extra wildcards, create a lemma lhs => rhs
          Goal::add_lemma(lhs.clone(), rhs.clone(), condition.clone(), &mut rewrites);
          added_lemma = true;
          if CONFIG.single_rhs {
            continue;
          };
        }
        if (is_cyclic || !added_lemma) && lhs.vars().iter().all(|x| rhs.vars().contains(x)) {
          // if lhs has no extra wildcards, create a lemma rhs => lhs;
          // in non-cyclic mode, a single direction of IH is always sufficient
          // (because grounding adds all instantiations we could possibly care about).
          Goal::add_lemma(rhs.clone(), lhs.clone(), condition, &mut rewrites);
          added_lemma = true;
          if CONFIG.single_rhs {
            continue;
          };
        }
        if !added_lemma {
          warn!("cannot create a lemma from {} and {}", lhs, rhs);
        }
        // else {
        //   println!("Lemma has premises:");
        //   self.premises.iter().for_each(|p| println!("{}", p));
        // }
      }
    }
    rewrites
  }

  /// Add a rewrite `lhs => rhs` to `rewrites` if not already present
  fn add_lemma(
    lhs: Pat,
    rhs: Pat,
    cond: SmallerVar,
    rewrites: &mut HashMap<String, (Pat, Pat, SmallerVar)>,
  ) {
    let name = format!("{}{}={}", LEMMA_PREFIX, lhs, rhs);
    // Insert the lemma into the rewrites map if it's not already there
    match rewrites.entry(name) {
      Entry::Occupied(_) => (),
      Entry::Vacant(entry) => {
        warn!("creating lemma: {} => {}", lhs, rhs);
        entry.insert((lhs, rhs, cond));
      }
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
      self.guard_exprs.insert(fresh_var.to_string(), expr);
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
  fn case_split(mut self, state: &mut ProofState<'a>, is_cyclic: bool) {
    let new_lemmas = self.add_lemma_rewrites(state, is_cyclic);

    // Get the next variable to case-split on
    let var = self.scrutinees.pop_front().unwrap();
    let var_str = var.to_string();
    warn!("case-split on {}", var);
    let var_node = SymbolLang::leaf(var);
    let var_pattern_ast: RecExpr<ENodeOrVar<SymbolLang>> = vec![ENodeOrVar::ENode(var_node)].into();
    // Get the type of the variable, and then remove the variable
    let ty = match self.local_context.get(&var) {
      Some(ty) => ty,
      None => panic!("{} not in local context", var),
    };
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
      new_goal.lemmas = new_lemmas.clone();

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

        if !is_cyclic {
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

          // Take both sides of the equality and the premise (if there is one)
          let mut sides = vec![&new_goal.eq.lhs, &new_goal.eq.rhs];
          for premise in new_goal.premises.iter() {
            sides.push(&premise.lhs);
            sides.push(&premise.rhs);
          }
          // Instantiate all sides with the new substitution
          instantiate_new_ih_terms(
            &mut new_goal.egraph,
            &mut new_goal.prev_var_instantiations,
            &fresh_var_name,
            &ancestors,
            sides.as_slice(),
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
      for (_, (_, _, smaller_var)) in new_goal.lemmas.iter_mut() {
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
        &rec_expr_to_pattern_ast(con_app.clone()),
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

      new_goal.premises = self
        .premises
        .iter()
        .map(|premise| {
          let var_instantiation = HashMap::from([(var_str.clone(), con_app_sexp.clone())]);
          let new_lhs_sexp = resolve_sexp(&premise.lhs.sexp, &var_instantiation);
          let new_rhs_sexp = resolve_sexp(&premise.rhs.sexp, &var_instantiation);
          let new_lhs = ETerm::new(&new_lhs_sexp, &mut new_goal.egraph);
          let new_rhs = ETerm::new(&new_rhs_sexp, &mut new_goal.egraph);
          let old_ids = (
            new_goal.egraph.find(premise.lhs.id),
            new_goal.egraph.find(premise.rhs.id),
          );
          // This is simply instantiating a variable to something it has been
          // unioned with, so these ids should be unchanged.
          //
          // This can be solved in the future by canonicalization.
          assert_eq!(old_ids, (new_lhs.id, new_rhs.id));
          Equation {
            lhs: new_lhs,
            rhs: new_rhs,
          }
        })
        .collect();

      // TODO: should this be only done when mk_lemmas is false?
      if var_str.starts_with(GUARD_PREFIX) {
        let lhs = ETerm::from_expr(self.guard_exprs[&var_str].clone(), &new_goal.egraph);
        let rhs = ETerm::from_expr(con_app, &new_goal.egraph);
        let eq = Equation { lhs, rhs };
        new_goal.premises.push(eq);
      }

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
          self.guard_exprs[&var_str].to_string(),
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

impl<'a> Display for Goal<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if !self.premises.is_empty() {
      let premises_string = self
        .premises
        .iter()
        .map(|premise| format!("{}", premise))
        .collect::<Vec<String>>()
        .join(", ");
      write!(f, "{} ==> ", premises_string)?;
    }
    write!(f, "{}", self.eq)
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
  for lhs_node in goal.egraph[goal.eq.lhs.id].nodes.iter() {
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
  for rhs_node in goal.egraph[goal.eq.rhs.id].nodes.iter() {
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
pub fn prove(mut goal: Goal, is_cyclic: bool) -> (Outcome, ProofState) {
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
    goal.case_split(&mut state, is_cyclic);
    if CONFIG.verbose {
      println!("{}", "Case splitting and continuing...".purple());
    }
  }
  // All goals have been discharged, so the conjecture is valid:
  (Outcome::Valid, state)
}
