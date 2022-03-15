use lazy_static::lazy_static;
use log::Level;
use clap::Parser;

#[derive(Parser)]
pub struct Args {
  pub filename: String,
  #[clap(short = 'd', long = "max-depth", default_value = "3")]
  pub max_split_depth: usize,
  #[clap(short = 'k', long = "keep-used")]
  pub keep_used_scrutinees: bool,
  #[clap(short = 's', long = "single-rhs")]
  pub single_rhs: bool,
  #[clap(short = 'i', long = "irreducible")]
  pub irreducible_only: bool,
  // timeout
  #[clap(short = 't', long = "timeout", default_value = "0")]
  pub timeout: u64,
  // logging
  #[clap(short = 'l', long = "log", default_value = "ERROR")]
  pub log_level: String,
  #[clap(short = 'g', long = "save-graphs")]
  pub save_graphs: bool,
  #[clap(short = 'r', long = "save-results")]
  pub save_results: bool,
}

pub struct Config {
  pub max_split_depth: usize,
  pub keep_used_scrutinees: bool,
  pub single_rhs: bool,
  pub irreducible_only: bool,
  // timeout
  pub timeout: Option<u64>,
  // logging
  pub log_level: Level,
  pub save_graphs: bool,
  pub save_results: bool
}

impl Config {
  fn from_args(args: &Args) -> Self {
    Self {
      max_split_depth: args.max_split_depth,
      keep_used_scrutinees: args.keep_used_scrutinees,
      single_rhs: args.single_rhs,
      irreducible_only: args.irreducible_only,
      timeout: if args.timeout == 0 { None } else { Some(args.timeout) },
      log_level: args.log_level.parse().unwrap(),
      save_graphs: args.save_graphs,
      save_results: args.save_results
    }
  }
}

lazy_static!{
  pub static ref ARGS: Args = Args::parse();
  pub static ref CONFIG: Config = Config::from_args(&ARGS);
}