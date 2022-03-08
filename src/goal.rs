use std::{collections::VecDeque};
use egg::{*};
use log::{warn};
use colored::Colorize;

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
    let target_ids = self.0.iter().map(|x| subst.get(to_wildcard(x)).unwrap());
    let extractor = Extractor::new(egraph, AstSize);
    let targets = target_ids.map(|x| extractor.find_best(*x).1);
    SmallerVar::smaller_tuple(&self.0.iter().zip(targets).collect())
  }
}

/// Proof goal
pub struct Goal {
  /// Goal name
  pub name: String,
  /// Equivalences we already proved
  pub egraph: Eg,
  /// Rewrites that are valid for the current goal
  rewrites: Vec<Rw>,
  /// Context
  ctx: Context,
  /// Variables we haven't case-split on yet
  scrutinees: VecDeque<Symbol>,
  /// Our goal is to prove lhs == rhs
  lhs_id: Id,
  rhs_id: Id,
  /// Environment
  env: Env,
}

impl Goal {
  /// Create top-level goal
  pub fn top(
    name: &str,      
    lhs: &Expr,
    rhs: &Expr,
    env: &Env,
    ctx: &Context,
    rewrites: &[Rw],    
    scrutinees: &[Symbol],
  ) -> Self {
    let mut egraph: Eg = Default::default();
    egraph.add_expr(&lhs);
    egraph.add_expr(&rhs);
    egraph.rebuild();
    let lhs_id = egraph.lookup_expr(lhs).unwrap();
    let rhs_id = egraph.lookup_expr(rhs).unwrap();

    let scrs: VecDeque<Symbol> = if 0 < CONFIG.max_split_depth { 
      VecDeque::from_iter(scrutinees.iter().cloned())
    } else {
      let mut d = VecDeque::new();
      d.push_back(Symbol::from(BOUND_EXCEEDED)); 
      d
    };

    Self {
      name: name.to_string(),
      egraph,
      rewrites: rewrites.to_vec(),
      ctx: ctx.clone(),
      scrutinees: scrs,
      lhs_id,
      rhs_id,
      env: env.clone(),
    }}

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
    let runner = Runner::default().with_egraph(self.egraph).run(self.rewrites.iter());
    self.egraph = runner.egraph;
    self
  }

  /// Create a rewrite `lhs => rhs` which will serve as the lemma ("induction hypothesis") for a cycle in the proof;
  /// here lhs and rhs are patterns, created by replacing all scrutinees with wildcards;
  /// soundness requires that the pattern only apply to variable tuples smaller than the current scrutinee tuple.
  fn mk_lemma_rewrites(&self) -> Vec<Rw> {
    let lhs_id = self.egraph.find(self.lhs_id);
    let rhs_id = self.egraph.find(self.rhs_id);
    let exprs = get_all_expressions(&self.egraph, vec![lhs_id, rhs_id]);

    // println!("All LHS expressions:");
    // for le in exprs.get(&lhs_id).unwrap() {
    //   println!("{}", le);
    // }
    // println!("All RHS expressions:");
    // for re in exprs.get(&rhs_id).unwrap() {
    //   println!("{}", re);
    // }

    let mut rewrites = vec![];
    for lhs_expr in exprs.get(&lhs_id).unwrap() {
      for rhs_expr in exprs.get(&rhs_id).unwrap() {
        // TODO: perhaps just take the first right-hand side?
        let name = format!("lemma-{}={}", lhs_expr, rhs_expr);
        let is_var = |v| self.scrutinees.contains(v);
        let lhs: Pattern<SymbolLang> = to_pattern(lhs_expr, is_var);
        let rhs: Pattern<SymbolLang> = to_pattern(rhs_expr, is_var);
        let condition = SmallerVar(self.scrutinees.iter().cloned().collect());

        if rhs.vars().iter().all(|x| lhs.vars().contains(x)) {
          // if rhs has no extra wildcards, create a lemma lhs => rhs
          warn!("creating lemma: {} => {}", lhs, rhs);
          let lemma = Rewrite::new(name, lhs, ConditionalApplier {condition: condition, applier: rhs}).unwrap();
          rewrites.push(lemma);
        } else if lhs.vars().iter().all(|x| rhs.vars().contains(x)) {
          // otherwise if lhs has no extra wildcards, create a lemma rhs => lhs
          warn!("creating lemma: {} => {}", rhs, lhs);
          let lemma = Rewrite::new(name, rhs, ConditionalApplier {condition: condition, applier: lhs}).unwrap();
          rewrites.push(lemma);
        } else {
          warn!("cannot create a lemma from {} and {}", lhs, rhs);
        }
      }
    }
    rewrites        
  }

  /// Consume this goal and add its case splits to the proof state
  fn case_split(mut self, state: &mut ProofState) {
    let lemmas = self.mk_lemma_rewrites();

    // Get the next variable to case-split on
    let var = self.scrutinees.pop_front().unwrap();
    warn!("case-split on {}", var);
    let var_id = self.egraph.lookup(SymbolLang::leaf(var)).unwrap();
    // Get the type of the variable
    let ty = self.ctx.get(&var).unwrap();
    // Convert to datatype name
    let dt = Symbol::from(ty.datatype().unwrap());
    // Get the constructors of the datatype
    let cons = self.env.get(&dt).unwrap();
    // For each constructor, create a new goal and push it onto the proof state
    // (we process constructors in reverse order so that base case end up at the top of the stack)
    for &con in cons.iter().rev() {
      let mut new_goal = Goal {
        name: if self.name == "top" { String::default() } else { format!("{}:", self.name) },
        egraph: self.egraph.clone(),
        rewrites: self.rewrites.clone(),
        ctx: self.ctx.clone(),
        scrutinees: self.scrutinees.clone(),
        lhs_id: self.lhs_id,
        rhs_id: self.rhs_id,
        env: self.env.clone(),
      };

      // Get the types of constructor arguments
      let con_args = self.ctx.get(&con).unwrap().args();
      // For each argument: create a fresh variable and add it to the context and to scrutinees
      let mut fresh_vars = vec![];
      for i in 0..con_args.len() {
        let fresh_var_name = format!("{}-{}{}", var, self.egraph.total_size(), i);        
        let depth = var_depth(&fresh_var_name[..]);
        let fresh_var = Symbol::from(fresh_var_name);        
        fresh_vars.push(fresh_var);
        // Add new variable to context
        new_goal.ctx.insert(fresh_var, con_args[i].clone());
        // Only add new variable to scrutinees if its depth doesn't exceed the bound
        if depth < CONFIG.max_split_depth {
          new_goal.scrutinees.push_back(fresh_var);
        } else {
          new_goal.scrutinees.push_back(Symbol::from(BOUND_EXCEEDED));
        }               
      }

      // Create an application of the constructor to the fresh vars
      let con_app_string = format!("({} {})", con, fresh_vars.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(" "));
      let con_app: Expr = con_app_string.parse().unwrap();

      new_goal.name = format!("{}{}={}", new_goal.name, var, con_app);

      // Add con_app to the new goal's egraph and union it with var
      new_goal.egraph.add_expr(&con_app);
      let con_app_id = new_goal.egraph.lookup_expr(&con_app).unwrap();
      new_goal.egraph.union(var_id, con_app_id);
      new_goal.egraph.rebuild();

      // Remove old variable from the egraph
      remove_node(&mut new_goal.egraph, &SymbolLang::leaf(var));

      // If the constructor has parameters, add all lemmas to the new goal's rewrites
      if !fresh_vars.is_empty() {
        new_goal.rewrites.extend(lemmas.clone());
      }

      // Add the subgoal to the proof state
      state.push(new_goal);
    }
  }

  /// Save e-graph to file
  fn save_egraph(&self) {
    let filename = format!("target/{}.png", self.name);
    let verbosity = format!("-q{}", CONFIG.log_level as usize);
    let dot = self.egraph.dot();    
    dot.run_dot(&["-Tpng", verbosity.as_str(), "-o", filename.as_str()]).unwrap();
  }
}

/// A proof state is a list of subgoals,
/// all of which have to be discharged
pub type ProofState = Vec<Goal>;

/// Pretty-printed proof state
pub fn pretty_state(state: &ProofState) -> String {
  format!("[{}]", state.iter().map(|g| g.name.clone()).collect::<Vec<String>>().join(", "))
}

/// Outcome of a proof attempt
pub enum Outcome {
  Valid,
  Invalid,
  Unknown,
}

impl std::fmt::Display for Outcome {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match *self {
      Outcome::Valid => write!(f, "{}", "VALID".green()),
      Outcome::Invalid => write!(f, "{}", "INVALID".red()),
      Outcome::Unknown => write!(f, "{}", "UNKNOWN".yellow()),
    }
  }
}

/// Top-level interface to the theorem prover.
pub fn prove(mut goal: Goal) -> Outcome {
  let mut state = vec![goal];
  while !state.is_empty() {
    // TODO: This should be info! but I don't know how to suppress all the info output from egg
    warn!("PROOF STATE: {}", pretty_state(&state));
    // Pop the first subgoal
    goal = state.pop().unwrap();
    // Saturate the goal
    goal = goal.saturate();
    if CONFIG.save_graphs {
      goal.save_egraph();
    }
    if goal.done() { 
       // This goal has been discharged, proceed to the next goal
      continue;
    } 
    if goal.scrutinees.is_empty() {
      // This goal has no more variables to case-split on, 
      // so this goal, and hence the whole conjecture, is invalid
      return Outcome::Invalid;
    }
    if goal.scrutinees.front().unwrap() == &Symbol::from(BOUND_EXCEEDED) {
      // This goal could be further split, but we have reached the maximum depth,
      // we cannot prove or disprove the conjecture
      return Outcome::Unknown;
    }
    goal.case_split(&mut state);
  }
  // All goals have been discharged, so the conjecture is valid:
  Outcome::Valid
}
