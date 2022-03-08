use std::time::{Instant};
pub mod parser;
use parser::{*, goal::*, config::{CONFIG, ARGS}};

fn main() {
  simple_logger::init_with_level(CONFIG.log_level).unwrap();

  let goals = parse_file(&ARGS.filename).unwrap();

  for goal in goals {
    println!("Proving {}: {} = {}", goal.name, goal.get_lhs(), goal.get_rhs());
    let start = Instant::now();
    let result = prove(goal);
    let duration = start.elapsed();
    println!("{} ({:.2} sec)", result, duration.as_secs_f32());
  }
}
