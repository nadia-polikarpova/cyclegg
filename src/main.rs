use std::time::{Instant};
use std::fs::{*};
use std::io::Write;
pub mod parser;
use parser::{*, goal::*, config::{CONFIG, ARGS}};
use colored::Colorize;

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
    println!("{} {}: {} = {}", "Proving".blue(), goal.name.blue(), goal.get_lhs(), goal.get_rhs());
    let start = Instant::now();
    let (result, proof_state) = prove(goal);
    let duration = start.elapsed();
    println!("{} ({:.2} sec)", result, duration.as_secs_f32());
    for (goal_name, mut explanation) in proof_state.solved_goal_explanations {
      println!("{} {}", "Proved case".bright_blue(), goal_name);
      println!("{}", explanation.get_flat_string());
    }

    if let Some(ref mut file) = result_file {
      let line = format!("{},{:?},{}\n", goal_name, result, duration.as_secs_f32());
      file.write_all(line.as_bytes())?;
    }
  }
  Ok(())
}
