use egg::{*, rewrite as rw};
use symbolic_expressions::{Sexp, SexpError};
use std::{collections::HashMap, str::FromStr, fmt::Display};

mod types;
use types::{*};

// Both expressions and types are just SymbolLang expressions for now
type Expr = RecExpr<SymbolLang>;


// We will use SymbolLang e-graphs with no analysis for now
type Eg = EGraph<SymbolLang, ()>;
type Rw = Rewrite<SymbolLang, ()>;

// Environment: for now just a map from datatype names to constructor names
type Env = HashMap<Symbol, Vec<Symbol>>;

// Type context
type Context = HashMap<Symbol, Type>;

// Proof goal
struct Goal<'a> {
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
// A proof state is a list of subgoals,
// all of which have to be discharged
type ProofState<'a> = Vec<Goal<'a>>;

fn proof_step(state: &mut ProofState) {
  // Pop the first subgoal
  let mut goal = state.pop().unwrap();
  // Saturate the goal
  goal = goal.saturate();
  if goal.done() {
    // If this goal has been discharged, we're done
    return
  } else {
    // Otherwise, we need to case-split on a variable
    goal.case_split(state)
  }
}

// fn case_split(
//     mut egraph: Eg,
//     e: &Expr,
//     ctx: &Context,
//     env: &Env,
// ) -> Vec<Eg> {
//   let c = egraph.lookup_expr(e).unwrap();
//   let mut esucc = egraph.clone();

//   let c0 = egraph.add(SymbolLang::leaf("zero"));  
//   egraph.union(c, c0);
//   egraph.rebuild();

//   let pat = format!("(succ x{})", egraph.total_size());
//   let c1 = esucc.add_expr(&pat.parse().unwrap());
//   esucc.union(c, c1);
//   esucc.rebuild();

//   vec![egraph, esucc]
// }

fn main() {
  let context = Context::from([
    (Symbol::from("x"), "Nat".parse().unwrap()),
    (Symbol::from("zero"), "Nat".parse().unwrap()),
    (Symbol::from("succ"), "(-> (Nat) Nat)".parse().unwrap()),
    (Symbol::from("add"), "(-> (Nat Nat) Nat)".parse().unwrap()),
  ]);

  println!("arity of Nat: {:?}", &context.get(&Symbol::from("x")).unwrap().args());
  println!("arity of Nat -> Nat: {:?}", &context.get(&Symbol::from("succ")).unwrap().args());
  println!("arity of Nat -> Nat -> Nat: {:?}", &context.get(&Symbol::from("add")).unwrap().args());
  

  let constructor = Env::from([
    (Symbol::from("Nat"), vec![Symbol::from("zero"), Symbol::from("succ")]),
  ]);

  let rules: &[Rw] = &[
    rw!("add-zero"; "(add zero ?y)" => "?y"),
    rw!("add-succ"; "(add (succ ?x) ?y)" => "(succ (add ?x ?y))"),
    rw!("triv-zero"; "(triv zero)" => "true"),
    rw!("triv-succ"; "(triv (succ ?x))" => "true"),
  ];

  let rules1: Vec<Rw> = vec![
    rw!("add-zero"; "(add zero ?y)" => "?y"),
    rw!("add-succ"; "(add (succ ?x) ?y)" => "(succ (add ?x ?y))"),
    rw!("triv-zero"; "(triv zero)" => "true"),
    rw!("triv-succ"; "(triv (succ ?x))" => "true"),
  ];

  // let lhs: Expr = "(add (succ (succ zero)) (succ (succ zero)))".parse().unwrap();
  // let rhs: Expr = "(succ (succ (succ (succ zero))))".parse().unwrap();
  // let lhs: RecExpr<SymbolLang> = "(add (succ (succ zero)) x)".parse().unwrap();
  // let rhs: RecExpr<SymbolLang> = "(succ (succ x))".parse().unwrap();
  let lhs: RecExpr<SymbolLang> = "(triv x)".parse().unwrap();
  let rhs: RecExpr<SymbolLang> = "true".parse().unwrap();


  let mut egraph: Eg = Default::default();
  egraph.add_expr(&lhs);
  egraph.add_expr(&rhs);

  // let runner = Runner::default().with_egraph(egraph).run(rules);
  let runner = Runner::default().with_egraph(egraph).run(rules1.iter());
  println!("e-graph size: {}", runner.egraph.number_of_classes());
  println!("{} == {}", runner.egraph.lookup_expr(&lhs).unwrap(), runner.egraph.lookup_expr(&rhs).unwrap());

  // let scrutinee = "x".parse().unwrap();
  // let (egraph, esucc) = case_split(runner.egraph, &scrutinee, &context, &constructor);
  // let runner1 = Runner::default().with_egraph(egraph).run(rules);
  // let runner2 = Runner::default().with_egraph(esucc).run(rules);

  // println!("e-graph size: {}", runner1.egraph.number_of_classes());
  // println!("{} == {}", runner1.egraph.lookup_expr(&lhs).unwrap(), runner1.egraph.lookup_expr(&rhs).unwrap());
  // println!("e-graph size: {}", runner2.egraph.number_of_classes());
  // println!("{} == {}", runner2.egraph.lookup_expr(&lhs).unwrap(), runner2.egraph.lookup_expr(&rhs).unwrap());
}
