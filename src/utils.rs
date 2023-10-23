use egg::*;

fn cartesian_product_helper<T: Clone>(
  vector: &[Vec<T>],
  index: usize,
  current_combination: Vec<T>,
  result: &mut Vec<Vec<T>>,
) {
  if index == vector.len() {
    result.push(current_combination);
  } else {
    for elem in &vector[index] {
      let mut new_combination = current_combination.clone();
      new_combination.push(elem.clone());
      cartesian_product_helper(vector, index + 1, new_combination, result);
    }
  }
}

/// Given a vector of vectors, generates the "cartesian product" of all the vectors.
/// TODO: figure out how to use multi_cartesian_product from itertools instead of writing our own
pub fn cartesian_product<T: Clone>(vector: &[Vec<T>]) -> Vec<Vec<T>> {
  let mut result = Vec::new();
  cartesian_product_helper(vector, 0, Vec::new(), &mut result);
  result
}

/// prints all the expressions in the eclass with the given id
pub fn print_expressions_in_eclass<L: egg::Language + std::fmt::Display, N: egg::Analysis<L>>(
  egraph: &EGraph<L, N>,
  id: Id,
) {
  let extractor = egg::Extractor::new(&egraph, AstSize);

  for node in egraph[id].nodes.iter() {
    let child_rec_exprs: String = node
      .children()
      .iter()
      .map(|child_id| {
        let (_, best_rec_expr) = extractor.find_best(*child_id);
        best_rec_expr.to_string()
      })
      .collect::<Vec<String>>()
      .join(" ");
    if child_rec_exprs.is_empty() {
      println!("({})", node);
    } else {
      println!("({} {})", node, child_rec_exprs);
    }
  }
}
