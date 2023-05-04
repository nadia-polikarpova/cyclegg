use std::time::{Instant};
use std::fs::{*};
use std::io::Write;
pub mod parser;
use egg::AstSize;
use parser::{*, config::{CONFIG, ARGS}};
use colored::Colorize;
use crate::goal::Goal;

fn explain_goal_failure(goal: Goal) {
  println!("{} {}", "Could not prove".red(), goal.name);
  println!("{}", "LHS Nodes".cyan());
  let extractor = egg::Extractor::new(&goal.egraph, AstSize);
  for lhs_node in goal.egraph[goal.lhs_id].nodes.iter() {
    let child_rec_exprs: String = lhs_node.children.iter().map(|child_id|{
      let (_, best_rec_expr) = extractor.find_best(*child_id);
      best_rec_expr.to_string()
    }).collect::<Vec<String>>().join(" ");
    if child_rec_exprs.is_empty() {
      println!("({})", lhs_node);
    }
    println!("({} {:?})", lhs_node, child_rec_exprs);
  }
  println!("{}", "RHS Nodes".cyan());
  for rhs_node in goal.egraph[goal.rhs_id].nodes.iter() {
    let child_rec_exprs: String = rhs_node.children.iter().map(|child_id|{
      let (_, best_rec_expr) = extractor.find_best(*child_id);
      best_rec_expr.to_string()
    }).collect::<Vec<String>>().join(" ");
    if child_rec_exprs.is_empty() {
      println!("({})", rhs_node);
    }
    println!("({} {})", rhs_node, child_rec_exprs);
  }
}

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
    let (result, proof_state) = goal::prove(goal);
    let duration = start.elapsed();
    println!("{} ({:.2} sec)", result, duration.as_secs_f32());
    if CONFIG.explain_results {
      for (goal_name, mut explanation) in proof_state.solved_goal_explanations {
        println!("{} {}", "Proved case".bright_blue(), goal_name);
        println!("{}", explanation.get_flat_string());
      }
      for goal in proof_state.goals {
        explain_goal_failure(goal);
      }
    }
    if let Some(ref mut file) = result_file {
      let line = format!("{},{:?},{}\n", goal_name, result, duration.as_secs_f32());
      file.write_all(line.as_bytes())?;
    }
  }
  Ok(())
}
