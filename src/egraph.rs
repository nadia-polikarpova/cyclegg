use egg::*;
use std::collections::HashMap;

// Denotation of an egraph (or its subgraph)
// is a map from eclass ids to sets of expressions
type Denotation<L> = HashMap<Id, Vec<RecExpr<L>>>;

// Compute the denotation of all roots in egraph, ignoring cycles
pub fn get_all_expressions<L: Language, A: Analysis<L>>(
  egraph: &EGraph<L, A>,
  roots: Vec<Id>,
) -> Denotation<L> {
  let mut memo = HashMap::new();
  for root in roots {
    collect_expressions(egraph, root, &mut memo);
  }
  memo
}

// Compute the denotation of eclass ignoring cycles and store it in memo
fn collect_expressions<L: Language, A: Analysis<L>>(
  egraph: &EGraph<L, A>,
  eclass: Id,
  memo: &mut Denotation<L>,
) {
  if memo.get(&eclass).is_some() {
    // Already visited
  } else {
    // Initialize the memo entry for this eclass with an empty denotation,
    // collect denotations in a separate vector and update the map only at the end;
    // this guarantees that we are not following cycles
    memo.insert(eclass, vec![]);
    let mut denotations: Vec<RecExpr<L>> = vec![];
    // Join denotations of every node in the eclass
    for node in egraph[eclass].iter() {
      if node.is_leaf() {
        // If this node is a leaf, its denotation is itself
        let expr = RecExpr::from(vec![node.clone()]);
        denotations.push(expr);
      } else {
        // Otherwise, recursively collect the denotations of its children
        // and create a new expression from each tuple of their cross product.
        // Each products[i] stores the product of denotation sizes of all nodes from i+1 onwards
        let mut products: HashMap<Id, usize> = HashMap::new();
        for (i, c) in node.children().iter().enumerate() {
          collect_expressions(egraph, *c, memo);
          products.insert(*c, 1);
          for j in 0..i {
            products
              .entry(node.children()[j])
              .and_modify(|p| *p *= memo[c].len());
          }
        }
        // Now create the new expressions
        let c0 = &node.children()[0];
        // First compute the size of the cross product; we almost have it in products[c0]; just the size of c0's denotation is missing
        let cross_product_size = products[c0] * memo[c0].len();
        for k in 0..cross_product_size {
          // For the k-th element of the cross product, which element from the denotation of id should we take?
          // The formula is: k / (the product of all following denotation sizes) % this denotation size
          let lookup_id = |id: Id| k / products[&id] % memo[&id].len();
          let expr = node.join_recexprs(|id| memo.get(&id).unwrap()[lookup_id(id)].clone());
          denotations.push(expr);
        }
      }
    }
    memo.insert(eclass, denotations);
  }
}

// Remove node from egraph
pub fn remove_node<L: Language, A: Analysis<L>>(egraph: &mut EGraph<L, A>, node: &L) {
  for c in egraph.classes_mut() {
    c.nodes.retain(|n| n != node);
  }
}
