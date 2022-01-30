use egg::{*, rewrite as rw};

pub mod goal;
use goal::{*, ast::*, config::CONFIG};


fn main() {
  simple_logger::init_with_level(CONFIG.log_level).unwrap();

  let context = mk_context(&[
    ("x", "Nat"),
    ("y", "Nat"),
    ("zero", "Nat"),
    ("succ", "(-> (Nat) Nat)"),
    // ("true", "Bool"),
    // ("false", "Bool"),
    ("add", "(-> (Nat Nat) Nat)"),
    // ("triv", "(-> (Nat) Bool)"),
  ]);

  let env = mk_env(&[
    ("Nat", "zero succ"),
    // ("Bool", "true false"),
  ]);

  let rules: &[Rw] = &[
    rw!("add-zero"; "(add zero ?y)" => "?y"),
    rw!("add-succ"; "(add (succ ?x) ?y)" => "(succ (add ?x ?y))"),
    // rw!("triv-zero"; "(triv zero)" => "true"),
    // rw!("triv-succ"; "(triv (succ ?x))" => "true"),
    // rw!("triv-succ-zero"; "(triv (succ zero))" => "true"),
    // rw!("triv-succ-succ"; "(triv (succ (succ ?x))))" => "true"),
  ];

  
  // let lhs: Expr = "(add (succ (succ zero)) (succ (succ zero)))".parse().unwrap();
  // let rhs: Expr = "(succ (succ (succ (succ zero))))".parse().unwrap();
  // let lhs: Expr = "(add (succ (succ zero)) x)".parse().unwrap();
  // let rhs: Expr = "(succ (succ x))".parse().unwrap();
  // let lhs: Expr = "(triv x)".parse().unwrap();
  // let rhs: Expr = "true".parse().unwrap();
  let lhs: Expr = "(add x y)".parse().unwrap();
  let rhs: Expr = "(add y x)".parse().unwrap();

  println!("Conjecture: {} = {}", lhs, rhs);

  let goal = Goal::top(
    &lhs,
    &rhs,
    &env,
    &context,
    rules,
    &[Symbol::from("x"), Symbol::from("y")],
  );

  let result = prove(goal);
  if result {
    println!("Proved!");
  } else {
    println!("Who knows?");
  }
}
