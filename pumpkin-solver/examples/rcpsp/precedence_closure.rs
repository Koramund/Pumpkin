use std::collections::BTreeMap;

use itertools::Itertools;
use petgraph::algo::floyd_warshall;
use petgraph::algo::NegativeCycle;
use petgraph::Directed;
use petgraph::Graph;

use crate::rcpsp_instance::Precedence;
use crate::rcpsp_instance::RcpspInstance;

pub(crate) struct PrecedenceClosure {
    precedences: BTreeMap<usize, BTreeMap<usize, Precedence>>,
    processing_times: Vec<u32>,
}

impl PrecedenceClosure {
    pub(crate) fn new(rcpsp_instance: &RcpspInstance) -> Option<Self> {
        let precedence_closure = match distance_closure(
            rcpsp_instance.processing_times.len(),
            &rcpsp_instance
                .dependencies
                .iter()
                .flat_map(|(_, v)| v.iter())
                .cloned()
                .collect_vec(),
        ) {
            Ok(closure) => Some(closure),
            Err(NegativeCycle(_)) => {
                println!("Unsatisfiable");
                None
            }
        }?;
        let mut precedences = BTreeMap::<usize, BTreeMap<usize, Precedence>>::new();
        for precedence_entry in precedence_closure {
            precedences
                .entry(precedence_entry.successor)
                .or_default()
                .insert(precedence_entry.predecessor, precedence_entry);
        }
        Some(Self {
            precedences,
            processing_times: rcpsp_instance.processing_times.to_vec(),
        })
    }

    pub(crate) fn num_edges(&self) -> usize {
        self.precedences
            .iter()
            .map(|(_, precedences)| {
                precedences
                    .iter()
                    .filter(|(_, precedence)| {
                        // Simply check whether the precedence relation is large enough to be
                        // disjoint
                        precedence.gap >= self.processing_times[precedence.successor] as i32
                    })
                    .count()
            })
            .sum()
    }

    pub(crate) fn contains_edge(&self, node1: usize, node2: usize) -> bool {
        if let Some(precedence) = self.precedences.get(&node1).and_then(|e| e.get(&node2)) {
            precedence.gap >= self.processing_times[precedence.predecessor] as i32
        } else if let Some(precedence) = self.precedences.get(&node2).and_then(|e| e.get(&node1)) {
            precedence.gap >= self.processing_times[precedence.predecessor] as i32
        } else {
            false
        }
    }

    // TODO I could not figure out how to please borrow checker
    pub(crate) fn get_incoming_edges(&self, node: usize) -> impl Iterator<Item = Precedence> {
        let incoming = self.precedences.get(&node).cloned();
        incoming
            .into_iter()
            .flatten()
            .map(|(_, precedence)| precedence)
            .filter(|precedence| precedence.gap.is_positive())
    }
}

fn distance_closure(
    n_tasks: usize,
    dependencies: &[Precedence],
) -> Result<Vec<Precedence>, NegativeCycle> {
    let mut graph = Graph::<usize, i32, Directed>::new();
    let nodes = (0..n_tasks).map(|ix| graph.add_node(ix)).collect_vec();
    for &d in dependencies {
        let _ = graph.add_edge(nodes[d.predecessor], nodes[d.successor], -d.gap);
    }
    let closure = floyd_warshall(&graph, |edge| *edge.weight())?;
    let mut result = vec![];
    for ((from, to), weight) in closure {
        let predecessor = graph
            .node_weight(from)
            .cloned()
            .expect("cannot find the graph node index");
        let successor = graph
            .node_weight(to)
            .cloned()
            .expect("cannot find the graph node index");
        result.push(Precedence {
            predecessor,
            successor,
            gap: -weight,
        });
    }
    Ok(result)
}
