use std::time::Instant;
use std::fs::*;
use std::io::Write;
use colored::Colorize;

pub mod ast;
pub mod parser;
pub mod goal;
pub mod config;
pub mod egraph;
pub mod explain;

use parser::{*};
use config::{CONFIG, ARGS};
use explain::explain_top;

fn main() -> std::io::Result<()> {
  simple_logger::init_with_level(CONFIG.log_level).unwrap();

  let goals = parse_file(&ARGS.filename).unwrap();

  let mut result_file = if CONFIG.save_results {
    Some(File::create("target/results.csv")?)
  } else {
    None
  };

  for mut goal in goals {
    let goal_name = goal.name.clone();
    let goal_vars = goal.local_context.clone();
    let goal_lhs = goal.lhs.clone();
    let goal_rhs = goal.rhs.clone();
    println!("{} {}: {} = {}", "Proving begin".blue(), goal_name.blue(), goal_lhs, goal_rhs);
    let start = Instant::now();
    let (result, mut proof_state) = goal::prove(goal.clone(), false);
    goal.name = format!("{}_no_cyclic", goal_name);
    // let (result_without_cyclic, _proof_state_without_cyclic) = goal::prove(goal.clone(), false);
    let duration = start.elapsed();
    if CONFIG.verbose {
      println!("{} {}: {} = {}", "Proving end".blue(), goal_name.blue(), goal_lhs, goal_rhs);
    }
    // if result != result_without_cyclic {
    //   println!("{}: with cyclic {}, without cyclic {} ", "Differing results".red(), result, result_without_cyclic);
    // }
    println!("{} = {} ({:.2} sec)", goal_name.blue(), result, duration.as_secs_f32());
    if CONFIG.explain_results && !CONFIG.verbose {
      // for (goal_name, explanation) in &proof_state.solved_goal_explanations {
      //   println!("{} {}", "Proved case".bright_blue(), goal_name);
      //   println!("{}", explanation.get_string());
      // }
      if let goal::Outcome::Valid = result {
        println!("{}", explain_top(goal_name.clone(), &mut proof_state, goal_lhs, goal_rhs, goal_vars));
      }
    }
    if let Some(ref mut file) = result_file {
      let line = format!("{},{:?},{}\n", goal_name, result, duration.as_secs_f32());
      file.write_all(line.as_bytes())?;
    }
  }
  Ok(())
}
