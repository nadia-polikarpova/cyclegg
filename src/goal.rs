use colored::Colorize;
use egg::*;
use itertools::Itertools;
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

/// Condition that checks whether it is sound to apply a lemma
#[derive(Clone)]
pub struct Soundness {
  /// A substitution from lemma's free variables
  /// to the original e-classes these variables came from
  pub free_vars: IdSubst,
  /// All premises that must hold for this lemma to apply,
  /// expressed in terms of the free variables
  pub premises: Vec<Equation>,
}

impl Soundness {
  /// Substitution as a string, for debugging purposes
  fn _pretty_subst(subst: &Vec<(Symbol, Expr, Expr)>) -> String {
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
    has_strictly_smaller
  }

  /// Apply subst to self.premise (if any)
  /// and check whether the resulting terms are equal in the egraph
  fn check_premise(premise: &Equation, triples: &Vec<(Symbol, Expr, Expr)>, egraph: &Eg) -> bool {
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
    // This cannot happen in uncyclic mode, because we have grounded all the premises,
    // but it can happen in cyclic mode
    // panic!("premise {:?} = {:?} not found in egraph", lhs, rhs);
    false
  }

  /// Check all of the premises of this condition
  fn check_premises(&self, triples: &Vec<(Symbol, Expr, Expr)>, egraph: &Eg) -> bool {
    self
      .premises
      .iter()
      .all(|premise| Soundness::check_premise(premise, triples, egraph))
  }
}

impl SearchCondition<SymbolLang, CanonicalFormAnalysis> for Soundness {
  /// Returns true if the substitution is into a smaller tuple of variables
  fn check(&self, egraph: &Eg, _eclass: Id, subst: &Subst) -> bool {
    // Create an iterator over triples: (variable, old canonical form, new canonical form)
    let triples = self
      .free_vars
      .iter()
      .map(|(x, orig_id)| {
        let v = to_wildcard(x);
        // Subst must have all lemma variables defined
        // because we did the filtering when creating SmallerVars
        let new_id = subst.get(v).unwrap();
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

  fn new_from_expr(expr: &Expr, egraph: &mut Eg) -> ETerm {
    let sexp = parser::parse_str(&expr.to_string()).unwrap();
    egraph.add_expr(expr);
    let id = egraph.lookup_expr(expr).unwrap();
    Self {
      sexp,
      id,
      expr: expr.clone(),
    }
  }

  fn from_expr(expr: Expr, egraph: &Eg) -> Self {
    let id = egraph.lookup_expr(&expr).unwrap();
    let sexp = parser::parse_str(&expr.to_string()).unwrap();
    Self { sexp, id, expr }
  }

  /// Update variables in my expressions with their canonical forms
  fn update_variables(&self, subst: &IdSubst, egraph: &Eg) -> Self {
    let ssubst: SSubst = subst
      .iter()
      .map(|(x, id)| {
        let expr = CanonicalFormAnalysis::extract_canonical(egraph, *id).unwrap();
        (
          x.to_string(),
          symbolic_expressions::parser::parse_str(&expr.to_string()).unwrap(),
        )
      })
      .collect();
    let new_sexp = resolve_sexp(&self.sexp, &ssubst);
    let new_expr = new_sexp.to_string().parse().unwrap();
    Self {
      sexp: new_sexp,
      id: egraph.lookup_expr(&new_expr).unwrap(),
      expr: new_expr,
    }
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

  /// Update variables in my expressions with their canonical forms
  fn update_variables(&self, subst: &IdSubst, egraph: &Eg) -> Self {
    Self {
      lhs: self.lhs.update_variables(subst, egraph),
      rhs: self.rhs.update_variables(subst, egraph),
    }
  }
}

/// Proof goal
pub struct Goal<'a> {
  /// Goal name
  pub name: String,
  /// Equivalences we already proved
  pub egraph: Eg,
  /// Rewrites are split into reductions (invertible rules) and lemmas (non-invertible rules)
  reductions: &'a Vec<Rw>,
  lemmas: HashMap<String, Rw>,
  /// Mapping from all universally-quantified variables of the goal to their types
  /// (note this includes both current and old variables, which have been case-split away)
  pub local_context: Context,
  /// Mapping from all universally-quantified variables of the goal to the e-classes they are stored in
  /// (note this includes both current and old variables, which have been case-split away)
  pub var_classes: IdSubst,
  /// The top-level parameters to the goal
  pub params: Vec<Symbol>,
  /// Variables we can case-split
  /// (i.e. the subset of local_context that have datatype types)
  scrutinees: VecDeque<Symbol>,
  /// Instantiations of the induction hypothesis that are in the egraph
  grounding_instantiations: Vec<IdSubst>,
  /// The equation we are trying to prove
  pub eq: Equation,
  /// If this is a conditional prop, the premises
  pub premises: Vec<Equation>,
  /// Environment
  pub env: &'a Env,
  /// Global context (i.e. constructors and top-level bindings)
  pub global_context: &'a Context,

  /// If the goal is discharged, an explanation of the proof
  pub explanation: Option<Explanation<SymbolLang>>,
  /// Definitions in a form amenable to proof emission
  pub defns: &'a Defns,
  /// Stores the expression each guard variable maps to
  guard_exprs: HashMap<String, Expr>,
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
    let var_classes = lookup_vars(&egraph, params.iter().map(|(x, _)| x));

    let mut res = Self {
      name: name.to_string(),
      // The only instantiation we have so far is where the parameters map to themselves
      var_classes: var_classes.clone(),
      grounding_instantiations: vec![var_classes],
      egraph,
      explanation: None,
      reductions,
      lemmas: HashMap::new(),
      local_context: Context::new(),
      params: params.iter().map(|(x, _)| x.clone()).collect(),
      guard_exprs: HashMap::new(),
      scrutinees: VecDeque::new(),
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
      reductions: self.reductions,
      lemmas: HashMap::new(), // the lemmas will be re-generated immediately anyway
      local_context: self.local_context.clone(),
      var_classes: self.var_classes.clone(),
      params: self.params.clone(),
      scrutinees: self.scrutinees.clone(),
      grounding_instantiations: self.grounding_instantiations.clone(),
      eq: self.eq.clone(),
      premises: self.premises.clone(),
      env: self.env,
      global_context: self.global_context,
      // NOTE: We don't really need to clone this.
      defns: self.defns,
      // If we reach this point, I think we won't have an explanation
      explanation: None,
      guard_exprs: self.guard_exprs.clone(),
    }
  }

  /// Saturate the goal by applying all available rewrites
  pub fn saturate(mut self) -> Self {
    let rewrites = self.reductions.iter().chain(self.lemmas.values());
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
  fn add_lemma_rewrites(&mut self, state: &ProofState) -> HashMap<String, Rw> {
    let lhs_id = self.egraph.find(self.eq.lhs.id);
    let rhs_id = self.egraph.find(self.eq.rhs.id);
    let is_var = |v| self.local_context.contains_key(v);
    let is_cyclic = CONFIG.is_cyclic();

    let exprs = if is_cyclic {
      // If we are doing cyclic proofs: make lemmas out of all LHS and RHS variants
      get_all_expressions(&self.egraph, vec![lhs_id, rhs_id])
    } else {
      // In the non-cyclic case, only use the original LHS and RHS
      // and only if no other lemmas have been added yet
      let mut exprs: HashMap<Id, Vec<Expr>> = vec![(lhs_id, vec![]), (rhs_id, vec![])]
        .into_iter()
        .collect();
      if self.lemmas.is_empty() {
        exprs
          .get_mut(&lhs_id)
          .unwrap()
          .push(self.eq.lhs.expr.clone());
        exprs
          .get_mut(&rhs_id)
          .unwrap()
          .push(self.eq.rhs.expr.clone());
      }
      exprs
    };

    // Before creating a cyclic lemma with premises,
    // we need to update the variables in the premises
    // with their canonical forms in terms of the current goal variables
    let premises: Vec<Equation> = self
      .premises
      .iter()
      .map(|eq| eq.update_variables(&self.var_classes, &self.egraph))
      .collect();

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

        let lhs_vars = var_set(&lhs);
        let rhs_vars = var_set(&rhs);
        let lemma_vars = lhs_vars.union(&rhs_vars).cloned().collect();

        // If any of my premises contain variables that are not present in lhs or rhs,
        // skip because we don't know how to check such a premise
        if !premises.iter().all(|eq| {
          let premise_lhs_vars = var_set(&to_pattern(&eq.lhs.expr, is_var));
          let premise_rhs_vars = var_set(&to_pattern(&eq.rhs.expr, is_var));
          let premise_vars: HashSet<Var> =
            premise_lhs_vars.union(&premise_rhs_vars).cloned().collect();
          premise_vars.is_subset(&lemma_vars)
        }) {
          continue;
        }

        // Pick out those variables that occur in the lemma
        let lemma_var_classes: IdSubst = self
          .var_classes
          .iter()
          .filter(|(x, _)| lemma_vars.contains(&to_wildcard(x)))
          .map(|(x, id)| (x.clone(), *id))
          .collect();

        let condition = Soundness {
          free_vars: lemma_var_classes,
          premises: premises.clone(),
        };
        let mut added_lemma = false;
        if rhs_vars.is_subset(&lhs_vars) {
          // if rhs has no extra wildcards, create a lemma lhs => rhs
          Goal::add_lemma(lhs.clone(), rhs.clone(), condition.clone(), &mut rewrites);
          added_lemma = true;
          if CONFIG.single_rhs {
            continue;
          };
        }
        if (is_cyclic || !added_lemma) && lhs_vars.is_subset(&rhs_vars) {
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
      }
    }
    rewrites
  }

  /// Add a rewrite `lhs => rhs` to `rewrites` if not already present
  fn add_lemma(lhs: Pat, rhs: Pat, cond: Soundness, rewrites: &mut HashMap<String, Rw>) {
    let name = format!("{}{}={}", LEMMA_PREFIX, lhs, rhs);
    // Insert the lemma into the rewrites map if it's not already there
    match rewrites.entry(name.clone()) {
      Entry::Occupied(_) => (),
      Entry::Vacant(entry) => {
        warn!("creating lemma: {} => {}", lhs, rhs);
        let rw = Rewrite::new(
          name,
          ConditionalSearcher {
            condition: cond,
            searcher: lhs,
          },
          rhs,
        )
        .unwrap();
        entry.insert(rw);
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
    // Pattern "(ite ?g ?x ?y)"
    let searcher: Pattern<SymbolLang> = format!("({} {} ?x ?y)", *ITE, guard_var).parse().unwrap();
    let matches = searcher.search(&self.egraph);
    // Collects class IDs of all stuck guards;
    // it's a map because the same guard can match more than once, but we only want to add a new scrutinee once
    let mut stuck_guards = HashMap::new();
    for m in matches {
      for subst in m.substs {
        let guard_id = *subst.get(guard_var).unwrap();
        if let CanonicalForm::Stuck = self.egraph[guard_id].data {
          stuck_guards.insert(guard_id, subst);
        }
      }
    }
    // Iterate over all stuck guard eclasses and add a new scrutinee to each
    for (guard_id, subst) in stuck_guards {
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
  fn case_split(mut self, state: &mut ProofState<'a>) {
    let new_lemmas = self.add_lemma_rewrites(state);

    let mut blocking_vars: HashSet<_> = HashSet::default();

    for reduction in self.reductions {
      let x = reduction.searcher.get_pattern_ast().unwrap();
      let sexp = symbolic_expressions::parser::parse_str(&x.to_string()).unwrap();

      let mut new_sexps: Vec<Sexp> = self
        .analyze_sexp_for_blocking_vars(&sexp)
        .into_iter()
        .map(|x| x.to_string())
        .collect::<HashSet<_>>()
        .into_iter()
        .map(|x| symbolic_expressions::parser::parse_str(x.as_str()).unwrap())
        .collect();

      for ns in new_sexps.iter_mut() {
        *ns = self.gen_fresh_vars(ns.clone(), 1);
      }

      for new_sexp in new_sexps {
        let mod_searcher: Pattern<SymbolLang> = new_sexp.to_string().parse().unwrap();
        let bvs: Vec<Var> = mod_searcher
          .vars()
          .iter()
          .filter(|&x| x.to_string().contains("block_"))
          .cloned()
          .collect();

        let matches = mod_searcher.search(&self.egraph);

        // look at the e-class analysis for each matched e-class, if any of them has a variable, use it
        for m in matches {
          for subst in m.substs {
            for v in &bvs[0..] {
              if let Some(&ecid) = subst.get(*v) {
                match &self.egraph[ecid].data {
                  CanonicalForm::Var(n) => {
                    blocking_vars.insert(n.op);
                  }
                  _ => (),
                }
              }
            }
          }
        }
      }
    }

    // println!("blocking vars: {:?}", blocking_vars);
    // println!("scrutinees: {:?}", self.scrutinees);
    // Get the next variable to case-split on
    let blocking = self
      .scrutinees
      .iter()
      .find_position(|x| blocking_vars.contains(x));

    let var = match blocking {
      Some((i, _)) => self.scrutinees.remove(i).unwrap(),
      None => self.scrutinees.pop_front().unwrap(),
    };

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
        let id = new_goal.egraph.add(SymbolLang::leaf(fresh_var));
        new_goal.var_classes.insert(fresh_var, id);

        if !CONFIG.is_cyclic() && ty == arg_type {
          // This is a recursive constructor parameter:
          // add new grounding instantiations replacing var with fresh_var
          new_goal.add_grounding(var, fresh_var);
        }
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
      new_goal.egraph.rebuild();

      // In cyclic mode: add the guard to premises,
      if CONFIG.is_cyclic() && var_str.starts_with(GUARD_PREFIX) {
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

  fn sexp_is_constructor(&self, sexp: &Sexp) -> bool {
    match sexp {
      Sexp::String(s) => is_constructor(s),
      Sexp::List(v) => is_constructor(&v[0].string().unwrap()),
      _ => false,
    }
  }

  fn gen_fresh_vars(&self, sexp: Sexp, mut idx: i32) -> Sexp {
    let qm = "?".to_string();
    match sexp {
      Sexp::String(s) if s == qm => Sexp::String(format!("?block_{}", idx)),
      Sexp::List(v) => Sexp::List(
        v.iter()
          .map(|x| {
            idx = idx + 1;
            self.gen_fresh_vars(x.clone(), idx + 1)
          })
          .collect(),
      ),
      _ => sexp,
    }
  }

  fn analyze_sexp_for_blocking_vars(&self, sexp: &Sexp) -> Vec<Sexp> {

    let mut new_exps: Vec<Sexp> = vec![];
    new_exps.push(sexp.clone());

    if self.sexp_is_constructor(sexp) {
      let fresh_var_indicator = "?";
      new_exps.push(Sexp::String(fresh_var_indicator.to_string()));
    }

    match sexp {
      Sexp::List(v) => {
        let head = &v[0];
        let mut all_replacements: Vec<Vec<Sexp>> = vec![];
        for (_, sub_arg) in v[1..].iter().enumerate() {
          all_replacements.push(self.analyze_sexp_for_blocking_vars(sub_arg));
        }
        // now we need to create all combinations of these replacements
        let all_combinations = generate_combinations(&all_replacements);
        for mut combination in all_combinations {
          combination.insert(0, head.clone());
          new_exps.push(Sexp::List(combination));
        }
      }
      _ => {}
    };

    return new_exps;
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
    let ret = args
      .iter()
      .map(|arg| Type::new(resolve_sexp(&arg.repr, &instantiations)))
      .collect();
    ret
  }

  /// Add new grounding instantiations
  /// that replace parent with child in previous instantiations
  fn add_grounding(&mut self, parent: Symbol, child: Symbol) {
    // First gather all the terms we want to instantiate:
    // take both sides of the equation and all the premises
    let mut sides = vec![&self.eq.lhs, &self.eq.rhs];
    for premise in self.premises.iter() {
      sides.push(&premise.lhs);
      sides.push(&premise.rhs);
    }

    // Now create new instantiations from existing ones
    let mut new_instantiations = vec![];
    for inst in self.grounding_instantiations.iter() {
      let replaced_canonicals: Vec<(Symbol, ETerm, bool)> = self
        .params
        .iter()
        .map(|x| {
          // Which class was this param instantiated to?
          let id = inst.get(x).unwrap();
          // Parameters must be canonical (at least in a clean state)
          let canonical = CanonicalFormAnalysis::extract_canonical(&self.egraph, *id).unwrap();
          // Try replacing the case-split variable with its child
          let (new_expr, replaced) = replace_var(&canonical, parent, child);
          let eterm = if replaced {
            ETerm::new_from_expr(&new_expr, &mut self.egraph)
          } else {
            ETerm::from_expr(new_expr, &self.egraph)
          };
          (x.clone(), eterm, replaced)
        })
        .collect();
      // If any of the canonical forms had a replacement, add a new instantiation:
      if replaced_canonicals.iter().any(|(_, _, b)| *b) {
        let new_instantiation = replaced_canonicals
          .iter()
          .map(|(x, e, _)| (x.to_string(), e.sexp.clone()))
          .collect();
        // For each new instantiation, instantiate all the sides and add them to the egraph
        for term in sides.iter() {
          let new_term = resolve_sexp(&term.sexp, &new_instantiation);
          ETerm::new(&new_term, &mut self.egraph);
        }
        // Add the new instantiation to the list of grounding instantiations
        let new_subst = replaced_canonicals
          .iter()
          .map(|(x, e, _)| (x.clone(), e.id))
          .collect();
        new_instantiations.push(new_subst);
      }
    }

    // Add the new instantiations to the list of grounding instantiations
    self.grounding_instantiations.extend(new_instantiations);
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
pub fn prove(mut goal: Goal) -> (Outcome, ProofState) {
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
    goal.case_split(&mut state);
    if CONFIG.verbose {
      println!("{}", "Case splitting and continuing...".purple());
    }
  }
  // All goals have been discharged, so the conjecture is valid:
  (Outcome::Valid, state)
}

fn combine_options<T: Clone>(
  vector: &[Vec<T>],
  index: usize,
  current_combination: Vec<T>,
  result: &mut Vec<Vec<T>>,
) {
  if index == vector.len() {
    result.push(current_combination);
  } else {
    for option in &vector[index] {
      let mut new_combination = current_combination.clone();
      new_combination.push(option.clone());
      combine_options(vector, index + 1, new_combination, result);
    }
  }
}

fn generate_combinations<T: Clone>(vector: &[Vec<T>]) -> Vec<Vec<T>> {
  let mut result = Vec::new();
  combine_options(vector, 0, Vec::new(), &mut result);
  result
}
