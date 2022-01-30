use egg::{*, rewrite as rw};

pub mod goal;
use goal::{*, ast::*};

// Prove a goal.
// Return true iff proof succeeded.
fn prove(mut goal: Goal) -> bool {
  let mut state = vec![goal];
  while !state.is_empty() {
    println!("Proof state: {}", pretty_state(&state));
    // Pop the first subgoal
    goal = state.pop().unwrap();
    // Saturate the goal
    goal = goal.saturate();
    goal.egraph.dot().to_png(format!("target/{}.png", goal.name)).unwrap();
    if !goal.done() {
      // We need to case-split on a variable
      if goal.can_split() {
        goal.case_split(&mut state);        
      } else {
        // No more variables to case-split on: this goal is unsolvable
        return false;
      }    
    }  
  }
  true
}

fn main() {
  let context = mk_context(&[
    ("x", "Nat"),
    ("zero", "Nat"),
    ("succ", "(-> (Nat) Nat)"),
    ("true", "Bool"),
    ("false", "Bool"),
    ("add", "(-> (Nat Nat) Nat)"),
    ("triv", "(-> (Nat) Bool)"),
  ]);

  let env = mk_env(&[
    ("Nat", "zero succ"),
    ("Bool", "true false"),
  ]);

  let rules: &[Rw] = &[
    rw!("add-zero"; "(add zero ?y)" => "?y"),
    rw!("add-succ"; "(add (succ ?x) ?y)" => "(succ (add ?x ?y))"),
    rw!("triv-zero"; "(triv zero)" => "true"),
    // rw!("triv-succ"; "(triv (succ ?x))" => "true"),
    rw!("triv-succ-zero"; "(triv (succ zero))" => "true"),
    rw!("triv-succ-succ"; "(triv (succ (succ ?x))))" => "true"),
  ];

  
  // let lhs: Expr = "(add (succ (succ zero)) (succ (succ zero)))".parse().unwrap();
  // let rhs: Expr = "(succ (succ (succ (succ zero))))".parse().unwrap();
  // let lhs: Expr = "(add (succ (succ zero)) x)".parse().unwrap();
  // let rhs: Expr = "(succ (succ x))".parse().unwrap();
  let lhs: Expr = "(triv x)".parse().unwrap();
  let rhs: Expr = "true".parse().unwrap();

  println!("Conjecture: {} = {}", lhs, rhs);

  let goal = Goal::top(
    &lhs,
    &rhs,
    &env,
    &context,
    rules,
    &[Symbol::from("x")],
  );

  let result = prove(goal);
  if result {
    println!("Proved!");
  } else {
    println!("Who knows?");
  }
}
