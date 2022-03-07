pub mod parser;
use parser::{*, goal::*, config::{CONFIG, ARGS}};

fn main() {
  simple_logger::init_with_level(CONFIG.log_level).unwrap();

  let goals = parse_file(&ARGS.filename).unwrap();

  for goal in goals {
    println!("Proving {}: {} = {}", goal.name, goal.lhs, goal.rhs);
    let result = prove(goal);
    println!("{}", result);
  }
}
