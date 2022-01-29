use egg::{*, rewrite as rw};
use std::collections::HashMap;

type Type = RecExpr<SymbolLang>;
type Expr = RecExpr<SymbolLang>;
type Eg = EGraph<SymbolLang, ()>;

// Constructors is a map from datatype names to constructor names
type Constructors = HashMap<Symbol, Vec<Symbol>>;

// Type context
type Context = HashMap<Symbol, Type>;

fn case_split(
    mut egraph: Eg,
    e: &Expr,
    ctx: &Context,
    constructors: &Constructors,
) -> (Eg, Eg) {
  let c = egraph.lookup_expr(e).unwrap();
  let mut esucc = egraph.clone();

  let c0 = egraph.add(SymbolLang::leaf("zero"));  
  egraph.union(c, c0);
  egraph.rebuild();

  let pat = format!("(succ x{})", egraph.total_size());
  let c1 = esucc.add_expr(&pat.parse().unwrap());
  esucc.union(c, c1);
  esucc.rebuild();

  (egraph, esucc)
}

fn main() {
  let context = Context::from([
    (Symbol::from("x"), "Nat".parse().unwrap()),
    (Symbol::from("zero"), "Nat".parse().unwrap()),
    (Symbol::from("succ"), "(-> Nat Nat)".parse().unwrap()),
    (Symbol::from("add"), "(-> Nat (-> Nat Nat))".parse().unwrap()),
  ]);

  let constructor = Constructors::from([
    (Symbol::from("Nat"), vec![Symbol::from("zero"), Symbol::from("succ")]),
  ]);

  let rules: &[Rewrite<SymbolLang, ()>] = &[
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

  let runner = Runner::default().with_egraph(egraph).run(rules);
  println!("e-graph size: {}", runner.egraph.number_of_classes());
  println!("{} == {}", runner.egraph.lookup_expr(&lhs).unwrap(), runner.egraph.lookup_expr(&rhs).unwrap());

  let scrutinee = "x".parse().unwrap();
  let (egraph, esucc) = case_split(runner.egraph, &scrutinee, &context, &constructor);
  let runner1 = Runner::default().with_egraph(egraph).run(rules);
  let runner2 = Runner::default().with_egraph(esucc).run(rules);

  println!("e-graph size: {}", runner1.egraph.number_of_classes());
  println!("{} == {}", runner1.egraph.lookup_expr(&lhs).unwrap(), runner1.egraph.lookup_expr(&rhs).unwrap());
  println!("e-graph size: {}", runner2.egraph.number_of_classes());
  println!("{} == {}", runner2.egraph.lookup_expr(&lhs).unwrap(), runner2.egraph.lookup_expr(&rhs).unwrap());
}
