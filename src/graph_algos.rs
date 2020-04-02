use petgraph::visit::{EdgeRef, NodeCompactIndexable, IntoEdges, IntoEdgeReferences};
use std::ops::{Add, AddAssign};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Color(pub usize);

impl Add<usize> for Color { type Output = Color; fn add(self, rhs: usize) -> Color { Color(self.0 + rhs) } }
impl AddAssign<usize> for Color { fn add_assign(&mut self, rhs: usize) { *self = *self + rhs } }

/// O(n + m), where n is g's number of nodes and  m is g's number of edges
pub fn is_valid_coloring<G>(g: G, k: usize, candidate: &[Color]) -> bool 
    where G: NodeCompactIndexable + IntoEdgeReferences {
    assert_eq!(g.node_bound(), candidate.len());
    for node in 0..g.node_bound() {
        if candidate[node].0 >= k {
            return false;
        }
    }
    for edge in g.edge_references() {
        let i = g.to_index(edge.source());
        let j = g.to_index(edge.target());
        if candidate[i] == candidate[j] {
            return false;
        }
    }
    true
}

pub fn increment_permutation<T: Copy + Ord + AddAssign<usize>>(x: &mut [T], lo: T, hi: T) -> bool {
    let mut i = 0;
    x[i] += 1;
    while x[i] > hi {
        x[i] = lo;
        i += 1;
        if i >= x.len() {
            return true;
        }
        x[i] += 1;
    }
    false
}

#[test]
fn test_increment_permutation() {
    const N: usize = 5;
    const K: usize = 3;
    let mut tmp = vec![0; N];
    let mut i: usize = 0;
    while !increment_permutation(&mut tmp, 0, K) {
        i += 1;
        println!("{:?}", tmp);
        for j in 0..N {
            assert_eq!(tmp[j], (i / (K+1).pow(j as _)) % (K+1));
        }
    }
}

/// O((n+m)*(k^n)), where k is the maximum number of colors to use, n is the number of nodes, m is the number of 
/// k^n term from looping over all possible \mathbb Z_{k}^{n} vectors
/// (n+m) multiplicand from calling is_valid_coloring within that loop
pub fn brute_force_colors<G>(g: G, max_colors: usize) -> Option<Vec<Color>>
    where G: NodeCompactIndexable + IntoEdgeReferences {
    let mut coloring = vec![Color(0); g.node_bound()];

    loop {
        if is_valid_coloring(g, max_colors, &coloring) {
            return Some(coloring);
        }
        if increment_permutation(&mut coloring, Color(0), Color(max_colors)) {
            break;
        }
    }
    None
}

#[test]
fn test_brute_force_colors() {
    use petgraph::{Graph, dot::{Dot, Config}};
    let mut g = Graph::<_, ()>::new();
    g.add_node("A");
    g.add_node("B");
    g.add_node("C");
    g.add_node("D");
    g.extend_with_edges(&[(0, 1), (1, 2), (2, 3), (3, 0)]);
    println!("{:?}", Dot::new(&g));
    let coloring = brute_force_colors(&g, 2);
    println!("{:?}", coloring);
}
