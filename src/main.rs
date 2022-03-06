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
    ("true", "Bool"),
    ("false", "Bool"),
    ("add", "(-> (Nat Nat) Nat)"),
    ("sub", "(-> (Nat Nat) Nat)"),
    ("lt", "(-> (Nat Nat) Bool)"),
  ]);

  let env = mk_env(&[
    ("Nat", "zero succ"),
    ("Bool", "true false"),
  ]);

  let rules: &[Rw] = &[
    rw!("add-zero"; "(add zero ?y)" => "?y"),
    rw!("add-succ"; "(add (succ ?x) ?y)" => "(succ (add ?x ?y))"),
    rw!("sub-zero-1"; "(sub ?x zero)" => "?x"),
    rw!("sub-zero-2"; "(sub zero ?y)" => "zero"),
    rw!("sub-succ"; "(sub (succ ?x) (succ ?y))" => "(sub ?x ?y)"),
    rw!("lt-zero"; "(lt ?x zero)" => "false"),
    rw!("lt-zero-succ"; "(lt zero (succ ?y))" => "true"),
    rw!("lt-succ-succ"; "(lt (succ ?x) (succ ?y))" => "(lt ?x ?y)"),
  ];
  
  let lhs: Expr = "(add x y)".parse().unwrap();
  let rhs: Expr = "(add y x)".parse().unwrap();

  let goal = Goal::top(
    &lhs,
    &rhs,
    &env,
    &context,
    rules,
    &[Symbol::from("x"), Symbol::from("y")],    
  );

  println!("conjecture: {} = {}", lhs, rhs);
  let result = prove(goal);
  println!("{}", result);
}
