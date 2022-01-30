use lazy_static::lazy_static;
use log::LevelFilter;

pub struct Config {
  pub max_split_depth: usize,
  // logging
  pub log_level: LevelFilter,
  pub save_graphs: bool
}

impl Default for Config {
  fn default() -> Self {
    Self {
      max_split_depth: 2,
      log_level: LevelFilter::Info,
      save_graphs: false
    }
  }
}

lazy_static!{
  pub static ref CONFIG: Config = Config::default();
}