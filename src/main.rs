use std::time::{Instant};
use std::fs::{*};
use std::io::Write;
pub mod parser;
use parser::{*, goal::*, config::{CONFIG, ARGS}};

fn main() -> std::io::Result<()> {
  simple_logger::init_with_level(CONFIG.log_level).unwrap();

  let goals = parse_file(&ARGS.filename).unwrap();

  let mut result_file = if CONFIG.save_results {
    Some(File::create("target/results.csv")?)
  } else {
    None
  };

  for goal in goals {
    let goal_name = goal.name.clone();
    println!("Proving {}: {} = {}", goal.name, goal.get_lhs(), goal.get_rhs());
    let start = Instant::now();
    let result = prove(goal);
    let duration = start.elapsed();
    println!("{} ({:.2} sec)", result, duration.as_secs_f32());

    if let Some(ref mut file) = result_file {
      let line = format!("{},{:?},{}\n", goal_name, result, duration.as_secs_f32());
      file.write_all(line.as_bytes())?;
    }
  }
  Ok(())
}
