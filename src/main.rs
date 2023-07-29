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
    let start_cyclic = Instant::now();
    let (result, mut proof_state) = goal::prove(goal.clone(), true);
    let duration_cyclic = start_cyclic.elapsed();
    let goal_name_without_cyclic = format!("{}_no_cyclic", goal_name);
    goal.name = goal_name_without_cyclic.clone();
    let start_non_cyclic = Instant::now();
    let (result_without_cyclic, mut proof_state_without_cyclic) = goal::prove(goal.clone(), false);
    let duration_non_cyclic = start_non_cyclic.elapsed();
    if CONFIG.verbose {
      println!("{} {}: {} = {}", "Proving end".blue(), goal_name.blue(), goal_lhs, goal_rhs);
    }
    if result != result_without_cyclic {
      println!("{}: with cyclic {}, without cyclic {} ", "Differing results".red(), result, result_without_cyclic);
    }
    println!("{} = {} (cyclic: {:.2} ms, non cyclic: {:.2} ms)", goal_name.blue(), result, duration_cyclic.as_millis(), duration_non_cyclic.as_millis());
    if CONFIG.explain_results && !CONFIG.verbose {
      // for (goal_name, explanation) in &proof_state.solved_goal_explanations {
      //   println!("{} {}", "Proved case".bright_blue(), goal_name);
      //   println!("{}", explanation.get_string());
      // }
      if let goal::Outcome::Valid = result {
        println!("Cyclic proof:");
        println!("{}", explain_top(goal_name.clone(), &mut proof_state, goal_lhs.clone(), goal_rhs.clone(), goal_vars.clone()));
      }
      if let goal::Outcome::Valid = result_without_cyclic {
        println!("Uncycled proof:");
        println!("{}", explain_top(goal_name_without_cyclic.clone(), &mut proof_state_without_cyclic, goal_lhs, goal_rhs, goal_vars));
      }
    }
    if let Some(ref mut file) = result_file {
      let line = format!("{},{:?},{}\n", goal_name, result, duration_cyclic.as_secs_f32());
      file.write_all(line.as_bytes())?;
    }
  }
  Ok(())
}
