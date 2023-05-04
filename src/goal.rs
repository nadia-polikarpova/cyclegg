use std::{collections::{VecDeque, HashSet}};
use egg::{*};
use log::{warn};
use colored::Colorize;
use std::time::{Instant, Duration};

#[path = "./ast.rs"] pub mod ast;
#[path = "./egraph.rs"] pub mod egraph;
#[path = "./config.rs"] pub mod config;
use ast::{*};
use egraph::{*};
use config::{*};

// We will use SymbolLang with no analysis for now
pub type Eg = EGraph<SymbolLang, ()>;
pub type Rw = Rewrite<SymbolLang, ()>;

/// A special scrutinee name used to signal that case split bound has been exceeded
const BOUND_EXCEEDED: &str = "__";

/// Condition that checks whether the substitution is into a smaller tuple of variable
struct SmallerVar(Vec<Symbol>);
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
  fn smaller_tuple(subst: &Vec<(&Symbol, Expr)>) -> bool {
    let mut has_strictly_smaller = false;
    let info = SmallerVar::pretty_subst(subst);    
    for (var, expr) in subst {
      let var_name = var.to_string();
      let expr_name = expr.to_string();
      if is_descendant(&expr_name, &var_name) {
        // Target is strictly smaller than source
        has_strictly_smaller = true;
      } else if expr_name != var_name {
        // Target is neither strictly smaller nor equal to source
        return false;
      }
    }
    if has_strictly_smaller { warn!("applying lemma with subst [{}]", info); }
    has_strictly_smaller
  }
}

impl Condition<SymbolLang, ()> for SmallerVar {
  /// Returns true if the substitution is into a smaller tuple of variables
  fn check(&self, egraph: &mut Eg, _eclass: Id, subst: &Subst) -> bool {
    let extractor = Extractor::new(egraph, AstSize);
    // Lookup all variables in the subst; some may be undefined if the lemma has fewer parameters
    let target_ids_mb = self.0.iter().map(|x| subst.get(to_wildcard(&x)));    
    let pairs = self.0.iter()
                  .zip(target_ids_mb)                                       // zip variables with their substitutions
                  .filter(|(_, mb)| mb.is_some())                           // filter out undefined variables
                  .map(|(v, mb)| (v, extractor.find_best(*mb.unwrap()).1)); // actually look up the expression by class id
    // Check that the expressions are smaller variables
    SmallerVar::smaller_tuple(&pairs.collect())
  }
}

fn rec_expr_to_pattern_ast<L: Clone>(rec_expr: RecExpr<L>) -> RecExpr<ENodeOrVar<L>> {
  let enode_or_vars: Vec<ENodeOrVar<L>> = rec_expr.as_ref().into_iter()
                                                           .cloned()
                                                           .map(|node| ENodeOrVar::ENode(node))
                                                           .collect();
  enode_or_vars.into()
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
  lemmas: Vec<Rw>,
  /// Universally-quantified variables of the goal
  /// (i.e. top-level parameters and binders derived from them through pattern matching)
  local_context: Context,
  /// Variables we can case-split
  /// (i.e. the subset of local_context that have datatype types)
  scrutinees: VecDeque<Symbol>,
  /// Our goal is to prove lhs == rhs
  pub lhs: Expr,
  pub lhs_id: Id,
  pub rhs: Expr,
  pub rhs_id: Id,
  /// Environment
  env: Env,
  /// Global context (i.e. constructors and top-level bindings)
  global_context: Context,
}

impl Goal {
  /// Create top-level goal
  pub fn top(
    name: &str,      
    lhs: &Expr,
    rhs: &Expr,
    params: Vec<(Symbol, Type)>,
    env: &Env,
    global_context: &Context,
    reductions: &[Rw],    
  ) -> Self {
    let mut egraph: Eg = EGraph::default().with_explanations_enabled();
    egraph.add_expr(&lhs);
    egraph.add_expr(&rhs);
    egraph.rebuild();
    let lhs_id = egraph.lookup_expr(lhs).unwrap();
    let rhs_id = egraph.lookup_expr(rhs).unwrap();

    let mut res = Self {
      name: name.to_string(),
      egraph,
      explanation: None,
      reductions: reductions.to_vec(),
      lemmas: vec![],
      local_context: Context::new(),
      scrutinees: VecDeque::new(),
      lhs: lhs.clone(),
      lhs_id,
      rhs: rhs.clone(),
      rhs_id,
      env: env.clone(),
      global_context: global_context.clone(),
    };
    for (name, ty) in params {
      res.add_scrutinee(name, &ty, 0);
      res.local_context.insert(name, ty);      
    }
    res
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
    let rewrites = self.reductions.iter().chain(self.lemmas.iter());
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
  fn mk_lemma_rewrites(&self, state: &ProofState) -> Vec<Rw> {
    let lhs_id = self.egraph.find(self.lhs_id);
    let rhs_id = self.egraph.find(self.rhs_id);
    let exprs = get_all_expressions(&self.egraph, vec![lhs_id, rhs_id]);
    let is_var = |v| self.local_context.contains_key(v);

    let mut rewrites = vec![];
    for lhs_expr in exprs.get(&lhs_id).unwrap() {
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
        let condition = SmallerVar(self.scrutinees.iter().cloned().collect());
        if rhs.vars().iter().all(|x| lhs.vars().contains(x)) {
          // if rhs has no extra wildcards, create a lemma lhs => rhs
          self.add_lemma(lhs.clone(), rhs, condition, &mut rewrites);
          if CONFIG.single_rhs { break };
        } else if lhs.vars().iter().all(|x| rhs.vars().contains(x)) {
          // if lhs has no extra wildcards, create a lemma rhs => lhs
          self.add_lemma(rhs, lhs.clone(), condition, &mut rewrites);
          if CONFIG.single_rhs { break };
        } else {
          warn!("cannot create a lemma from {} and {}", lhs, rhs);
        }
      }
    }
    rewrites        
  }

  /// Add a rewrite `lhs => rhs` to `rewrites` if not already present
  fn add_lemma(&self, lhs: Pat, rhs: Pat, cond: SmallerVar, rewrites: &mut Vec<Rw>) {
    let name = format!("lemma-{}={}", lhs, rhs);
    let mut existing_lemmas = self.lemmas.iter().chain(rewrites.iter());
    if !existing_lemmas.any(|r| r.name.to_string() == name) {
      // Only add the lemma if we don't already have it:
      warn!("creating lemma: {} => {}", lhs, rhs);
      let lemma = Rewrite::new(name, lhs, ConditionalApplier {condition: cond, applier: rhs}).unwrap();
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
    // it's a set because the same guard can match more than once, but we only want to add a new scrutinee once
    let mut irreducible_guards = HashSet::new();
    for m in matches {
      for subst in m.substs {
        let guard_id = subst.get(guard_var).unwrap().clone();
        // Root symbols of all enodes in guard_id's eclass
        let symbols: Vec<Symbol> = self.egraph[guard_id].nodes.iter().map(|n| n.op).collect();
        // This guard is irreducible if symbols are disjoint from reducible
        if !reducible.clone().any(|s| symbols.contains(s)) {
          irreducible_guards.insert((guard_var, subst, guard_id));
        }
      }
    }
    // Iterate over all irreducible guard eclasses and add a new scrutinee to each
    for (guard_var, subst, guard_id) in irreducible_guards {
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
      self.egraph.union_instantiations(&guard_var_pattern_ast, &new_pattern_ast, &subst, "add guard scrutinee");
    }
    self.egraph.rebuild();
  }

  /// Consume this goal and add its case splits to the proof state
  fn case_split(mut self, state: &mut ProofState) {
    let lemmas = self.mk_lemma_rewrites(state);    

    // Get the next variable to case-split on
    let var = self.scrutinees.pop_front().unwrap();
    warn!("case-split on {}", var);
    let var_node = SymbolLang::leaf(var);
    let var_rec_expr: RecExpr<SymbolLang> = vec!(var_node.clone()).into();
    let var_pattern_ast: RecExpr<ENodeOrVar<SymbolLang>> = vec!(ENodeOrVar::ENode(var_node.clone())).into();
    let var_id = self.egraph.lookup(var_node).unwrap();
    // Get the type of the variable, and then remove the variable
    let ty = self.local_context.get(&var).unwrap();
    // Convert to datatype name
    let dt = Symbol::from(ty.datatype().unwrap());
    // Get the constructors of the datatype
    let cons = self.env.get(&dt).unwrap();
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
        local_context: self.local_context.clone(),
        scrutinees: self.scrutinees.clone(),
        lhs: self.lhs.clone(),
        // lhs: var_rec_expr.clone(),
        lhs_id: self.lhs_id,
        // Putting a dummy value for now; We'll set this later once we create con_app.
        rhs: self.rhs.clone(),
        rhs_id: self.rhs_id,
        env: self.env.clone(),
        global_context: self.global_context.clone(),
      };      

      // Get the types of constructor arguments
      let con_ty = self.global_context.get(&con).unwrap();
      let con_args = Goal::instantiate_constructor(con_ty, ty);
      // For each argument: create a fresh variable and add it to the context and to scrutinees
      let mut fresh_vars = vec![];
      for i in 0..con_args.len() {
        let fresh_var_name = format!("{}-{}{}", var, self.egraph.total_size(), i);        
        let depth = var_depth(&fresh_var_name[..]);
        let fresh_var = Symbol::from(fresh_var_name);        
        fresh_vars.push(fresh_var);
        // Add new variable to context
        let arg_type = &con_args[i];
        new_goal.local_context.insert(fresh_var, arg_type.clone());
        new_goal.add_scrutinee(fresh_var, arg_type, depth);
      }

      // Create an application of the constructor to the fresh vars
      let con_app_string = format!("({} {})", con, fresh_vars.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(" "));
      let con_app: Expr = con_app_string.parse().unwrap();
      // new_goal.rhs = con_app.clone();

      new_goal.name = format!("{}{}={}", new_goal.name, var, con_app);

      // Add con_app to the new goal's egraph and union it with var
      new_goal.egraph.add_expr(&con_app);
      let con_app_id = new_goal.egraph.lookup_expr(&con_app).unwrap();
      // Not sure if it's proper to use new_goal.name here
      new_goal.egraph.union_instantiations(&var_pattern_ast.clone(), &rec_expr_to_pattern_ast(con_app), &Subst::default(), new_goal.name.clone());
      new_goal.egraph.rebuild();

      // Remove old variable from the egraph and context
      remove_node(&mut new_goal.egraph, &SymbolLang::leaf(var));
      new_goal.local_context.remove(&var);

      // Add the subgoal to the proof state
      state.goals.push(new_goal);
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
}

/// A proof state is a list of subgoals,
/// all of which have to be discharged
pub struct ProofState {
  pub goals: Vec<Goal>,
  pub solved_goal_explanations: Vec<(String, Explanation<SymbolLang>)>,
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
#[derive(Debug)]
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

/// Top-level interface to the theorem prover.
pub fn prove(mut goal: Goal) -> (Outcome, ProofState) {
  let mut state = ProofState { goals: vec![goal], solved_goal_explanations: vec![], start_time: Instant::now() };
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
    if goal.explanation.is_some() {
       // This goal has been discharged, proceed to the next goal
       state.solved_goal_explanations.push((goal.name, goal.explanation.unwrap()));
      continue;
    }
    goal.split_ite();
    if goal.scrutinees.is_empty() {
      // This goal has no more variables to case-split on, 
      // so this goal, and hence the whole conjecture, is invalid
      return (Outcome::Invalid, state);
    }
    if goal.scrutinees.front().unwrap() == &Symbol::from(BOUND_EXCEEDED) {
      // This goal could be further split, but we have reached the maximum depth,
      // we cannot prove or disprove the conjecture
      return (Outcome::Unknown, state);
    }
    goal.case_split(&mut state);
  }
  // All goals have been discharged, so the conjecture is valid:
  (Outcome::Valid, state)
}
