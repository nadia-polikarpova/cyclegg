use std::{collections::HashMap};
use egg::{*};

#[path = "./types.rs"] mod types;
use types::{*};

pub type Expr = RecExpr<SymbolLang>;

// We will use SymbolLang e-graphs with no analysis for now
pub type Eg = EGraph<SymbolLang, ()>;
pub type Rw = Rewrite<SymbolLang, ()>;

// Environment: for now just a map from datatype names to constructor names
pub type Env = HashMap<Symbol, Vec<Symbol>>;

// Type context
pub type Context = HashMap<Symbol, Type>;

// Proof goal
pub struct Goal<'a> {
  // Equivalences we already proved
  egraph: Eg,
  // Rewrites that are valid for the current goal
  rewrites: Vec<Rw>,
  // Context
  ctx: Context,
  // Variables we haven't case-split on yet
  scrutinees: Vec<Symbol>,
  // Our goal is to prove lhs == rhs
  lhs: &'a Expr,
  rhs: &'a Expr,
  // Environment
  env: &'a Env,
}

// A proof state is a list of subgoals,
// all of which have to be discharged
pub type ProofState<'a> = Vec<Goal<'a>>;

impl<'a> Goal<'a> {
  // Have we proven that lhs == rhs?
  pub fn done(&self) -> bool {
    let lhs_id = self.egraph.lookup_expr(self.lhs).unwrap();
    let rhs_id = self.egraph.lookup_expr(self.rhs).unwrap();
    lhs_id == rhs_id
  }

  // Saturate the goal by applying all available rewrites
  pub fn saturate(mut self) -> Self {
    let runner = Runner::default().with_egraph(self.egraph).run(self.rewrites.iter());
    self.egraph = runner.egraph;
    self
  }

  // Consume this goal and add its case splits to the proof state
  pub fn case_split(mut self, state: &mut ProofState) {
    // Get the next variable to case-split on
    let var = self.scrutinees.pop().unwrap();
    // Get the type of the variable
    let ty = self.ctx.get(&var).unwrap();
    // Get the constructors of the datatype
    let cons = self.env.get(&var).unwrap();
    // For each constructor,
    for &con in cons {
      // Get the type of the constructor
      let con_ty = self.ctx.get(&con).unwrap();
      // Create a new subgoal
      // let mut new_goal = Goal {
      //   lhs: goal.lhs.clone(),
      //   rhs: goal.rhs.clone(),
      //   egraph: goal.egraph.clone(),
      //   rewrites: goal.rewrites.clone(),
      //   ctx: goal.ctx.clone(),
      //   scrutinees: goal.scrutinees.clone(),
      // };
      // Add a rewrite to the subgoal
      // new_goal.rewrites.push(rw::CaseSplit(var, con));
      // Add the subgoal to the proof state
      // state.push(new_goal);
    }

  }
}
