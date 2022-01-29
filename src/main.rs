use egg::{*, rewrite as rw};

mod goal;
use goal::{*};

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


fn main() {
  let context = Context::from([
    (Symbol::from("x"), "Nat".parse().unwrap()),
    (Symbol::from("zero"), "Nat".parse().unwrap()),
    (Symbol::from("succ"), "(-> (Nat) Nat)".parse().unwrap()),
    (Symbol::from("add"), "(-> (Nat Nat) Nat)".parse().unwrap()),
    (Symbol::from("triv"), "(-> (Nat) Bool)".parse().unwrap()),
  ]);

  let env = Env::from([
    (Symbol::from("Nat"), vec![Symbol::from("zero"), Symbol::from("succ")]),
  ]);

  let rules: &[Rw] = &[
    rw!("add-zero"; "(add zero ?y)" => "?y"),
    rw!("add-succ"; "(add (succ ?x) ?y)" => "(succ (add ?x ?y))"),
    rw!("triv-zero"; "(triv zero)" => "true"),
    rw!("triv-succ"; "(triv (succ ?x))" => "true"),
  ];

  
  let lhs: Expr = "(add (succ (succ zero)) (succ (succ zero)))".parse().unwrap();
  let rhs: Expr = "(succ (succ (succ (succ zero))))".parse().unwrap();
  // let lhs: Expr = "(add (succ (succ zero)) x)".parse().unwrap();
  // let rhs: Expr = "(succ (succ x))".parse().unwrap();
  // let lhs: Expr = "(triv x)".parse().unwrap();
  // let rhs: Expr = "true".parse().unwrap();

  println!("Proving: {} = {}", lhs, rhs);

  let goal = Goal::top(
    &lhs,
    &rhs,
    &env,
    &context,
    rules,
    &[Symbol::from("x")],
  );

  let mut state = vec![goal];

  while !state.is_empty() {
    println!("Subgoals left: {}", state.len());
    proof_step(&mut state);
  }

  println!("Verified");
}
