use std::{collections::VecDeque};
use egg::{*};

#[path = "./ast.rs"] pub mod ast;
use ast::{*};

// We will use SymbolLang e-graphs with no analysis for now
pub type Eg = EGraph<SymbolLang, ()>;
pub type Rw = Rewrite<SymbolLang, ()>;

// How many times can a variable be case-split?
const MAX_SPLIT_DEPTH: usize = 2;

// Proof goal
pub struct Goal<'a> {
  pub name: String,
  // Equivalences we already proved
  pub egraph: Eg,
  // Rewrites that are valid for the current goal
  rewrites: Vec<Rw>,
  // Context
  ctx: Context,
  // Variables we haven't case-split on yet
  scrutinees: VecDeque<Symbol>,
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
  pub fn top(      
    lhs: &'a Expr,
    rhs: &'a Expr,
    env: &'a Env,
    ctx: &Context,
    rewrites: &[Rw],    
    scrutinees: &[Symbol],
  ) -> Self {
    let mut egraph: Eg = Default::default();
    egraph.add_expr(&lhs);
    egraph.add_expr(&rhs);
    egraph.rebuild();
    Self {
      name: "top".to_string(),
      egraph,
      rewrites: rewrites.to_vec(),
      ctx: ctx.clone(),
      scrutinees: scrutinees.to_vec().into_iter().collect(),
      lhs,
      rhs,
      env,
    }}

  // Have we proven that lhs == rhs?
  pub fn done(&self) -> bool {
    let lhs_id = self.egraph.lookup_expr(self.lhs).unwrap();
    let rhs_id = self.egraph.lookup_expr(self.rhs).unwrap();
    lhs_id == rhs_id
  }

  pub fn can_split(&self) -> bool {
    !self.scrutinees.is_empty()
  }

  // Saturate the goal by applying all available rewrites
  pub fn saturate(mut self) -> Self {
    let runner = Runner::default().with_egraph(self.egraph).run(self.rewrites.iter());
    self.egraph = runner.egraph;
    self
  }

  // Consume this goal and add its case splits to the proof state
  pub fn case_split(mut self, state: &mut ProofState<'a>) {
    // Get the next variable to case-split on
    let var = self.scrutinees.pop_front().unwrap();
    println!("case-split on {}", var);
    let var_id = self.egraph.lookup(SymbolLang::leaf(var)).unwrap();
    // Get the type of the variable
    let ty = self.ctx.get(&var).unwrap();
    // Convert to datatype name
    let dt = Symbol::from(ty.datatype().unwrap());
    // Get the constructors of the datatype
    let cons = self.env.get(&dt).unwrap();
    // For each constructor in reverse order (so that base case is processed first)
    for &con in cons.iter().rev() {
      let mut new_goal = Goal {
        name: if self.name == "top" { String::default() } else { format!("{}:", self.name) },
        egraph: self.egraph.clone(),
        rewrites: self.rewrites.clone(),
        ctx: self.ctx.clone(),
        scrutinees: self.scrutinees.clone(),
        lhs: self.lhs,
        rhs: self.rhs,
        env: self.env,
      };

      // Get the type of the constructor
      let con_ty = self.ctx.get(&con).unwrap();
      let con_args = con_ty.args();
      // For each argument: create a fresh variable and add it to the context and to scrutinees
      let mut fresh_vars = vec![];
      for i in 0..con_args.len() {
        let fresh_var_name = format!("{}-{}{}", var, self.egraph.total_size(), i);
        let depth = fresh_var_name.matches("-").count();
        let fresh_var = Symbol::from(fresh_var_name);
        fresh_vars.push(fresh_var);
        // Add new variable to context
        new_goal.ctx.insert(fresh_var, con_args[i].clone());
        // Only add new variable to scrutinees if its depth doesn't exceed MAX_DEPTH        
        if depth < MAX_SPLIT_DEPTH {
          new_goal.scrutinees.push_back(fresh_var);
        }                
      }

      // Create an application of the constructor to the fresh vars
      let con_app_string = format!("({} {})", con, fresh_vars.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(" "));
      let con_app: Expr = con_app_string.parse().unwrap();

      new_goal.name = format!("{}{}={}", new_goal.name, var, con_app);

      // Add con_app to the new goal's egraph and Union union it with var
      new_goal.egraph.add_expr(&con_app);
      let con_app_id = new_goal.egraph.lookup_expr(&con_app).unwrap();
      new_goal.egraph.union(var_id, con_app_id);
      new_goal.egraph.rebuild();

      // Add the subgoal to the proof state
      state.push(new_goal);
    }

  }
}

pub fn pretty_state(state: &ProofState) -> String {
  format!("[{}]", state.iter().map(|g| g.name.clone()).collect::<Vec<String>>().join(", "))
}
