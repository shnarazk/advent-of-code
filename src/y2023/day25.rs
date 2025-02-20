//! <https://adventofcode.com/2023/day/25>
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        progress,
    },
    itertools::Itertools,
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet},
    },
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: HashMap<String, Vec<String>>,
    link: Vec<(usize, usize)>,
    hash: HashMap<usize, Vec<(usize, usize)>>,
    names: HashSet<String>,
}

#[aoc_at(2023, 25)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn parse_block(&mut self, block: &str) -> Result<(), ParseError> {
        let b = block.split(": ").collect::<Vec<&str>>();
        let others = b[1].split(' ').map(|s| s.to_string()).collect::<Vec<_>>();
        self.names.insert(b[0].to_string());
        for name in others.iter() {
            self.names.insert(name.to_string());
        }
        self.line.insert(b[0].to_string(), others);
        Ok(())
    }
    fn end_of_data(&mut self) {
        let names = self
            .names
            .iter()
            .sorted()
            .cloned()
            .enumerate()
            .map(|(n, s)| (s, n))
            .collect::<HashMap<String, usize>>();
        for (from, tos) in self.line.iter() {
            for to in tos.iter() {
                let f = *names.get(from).unwrap();
                let t = *names.get(to).unwrap();
                self.link.push((f.min(t), f.max(t)));
            }
        }
        for (i, (from, to)) in self.link.iter().enumerate() {
            self.hash.entry(*from).or_default().push((i, *to));
            self.hash.entry(*to).or_default().push((i, *from));
        }
    }
    fn serialize(&self) -> Option<String> {
        serde_json::to_string(&self.link).ok()
    }
    //   1. pick up a pair of nodes and find a path between them, then delete the path.
    //   2. repeat above gain until finding a pair which are unreachable.
    //   4. they make a small link set that includes the answer set.
    //   5. find the triplet that makes the graph bigraph.
    fn part1(&mut self) -> Self::Output1 {
        let num_nodes = self.names.len();
        let mut forbidden_links: Vec<usize> = Vec::new();
        let mut used_nodes: Vec<usize> = Vec::new();
        while self.is_a_graph(&forbidden_links) {
            let unused_nodes = (0..num_nodes)
                .filter(|n| !used_nodes.contains(n))
                .collect::<Vec<_>>();
            let a = unused_nodes[0];
            let b = unused_nodes[unused_nodes.len() - 1];
            used_nodes.push(a);
            used_nodes.push(b);
            if let Some(mut v) = self.path_between(a, b, &forbidden_links) {
                forbidden_links.append(&mut v);
            }
        }
        let n_cands = forbidden_links.len();
        let n_combs = n_cands * (n_cands - 1) * (n_cands - 2);
        for i in 0..n_cands {
            for j in i + 1..n_cands {
                progress!((i * n_cands + j) as f64 / n_combs as f64);
                for k in j + 1..n_cands {
                    let v = self.edge_connectivity(&[
                        forbidden_links[i],
                        forbidden_links[j],
                        forbidden_links[k],
                    ]);
                    if v.len() == 2 {
                        return v.iter().product();
                    }
                }
            }
        }
        unreachable!()
    }
    fn part2(&mut self) -> Self::Output2 {
        "Happy holiday!".to_string()
    }
}
impl Puzzle {
    fn is_a_graph(&self, forbidden_links: &[usize]) -> bool {
        let len = self.names.len();
        let mut used_nodes: HashSet<usize> = HashSet::new();
        let mut to_visit: Vec<usize> = Vec::new();
        let remain = (0..len).find(|x| !used_nodes.contains(x)).unwrap();
        to_visit.push(remain);
        while let Some(n) = to_visit.pop() {
            if used_nodes.contains(&n) {
                continue;
            }
            used_nodes.insert(n);
            if let Some(v) = self.hash.get(&n) {
                for (link, to) in v.iter() {
                    if forbidden_links.contains(link) {
                        continue;
                    }
                    if !used_nodes.contains(to) {
                        to_visit.push(*to);
                    }
                }
            }
        }
        used_nodes.len() == len
    }
    fn edge_connectivity(&self, forbidden_edges: &[usize]) -> Vec<usize> {
        let len = self.names.len();
        let mut result: Vec<usize> = vec![];
        let mut used: HashSet<usize> = HashSet::new();
        let mut ng = 0;
        while result.iter().sum::<usize>() < len {
            let mut to_visit: Vec<usize> = Vec::new();
            let remain = (0..len).find(|x| !used.contains(x)).unwrap();
            to_visit.push(remain);
            while let Some(n) = to_visit.pop() {
                if used.contains(&n) {
                    continue;
                }
                used.insert(n);
                ng += 1;
                if let Some(v) = self.hash.get(&n) {
                    for (i, to) in v.iter() {
                        if forbidden_edges.contains(i) {
                            continue;
                        }
                        if !used.contains(to) {
                            to_visit.push(*to);
                        }
                    }
                }
            }
            result.push(ng);
            if 2 < result.len() {
                return vec![];
            }
            ng = 0;
        }
        result
    }
    fn path_between(
        &self,
        from_node: usize,
        to_node: usize,
        forbidden_links: &[usize],
    ) -> Option<Vec<usize>> {
        type OrderedRoute = (usize, Vec<(usize, usize)>);
        let mut used_links: HashSet<usize> = HashSet::new();
        let mut to_visit: BinaryHeap<Reverse<OrderedRoute>> = BinaryHeap::new();
        to_visit.push(Reverse((0, vec![(usize::MAX, from_node)])));
        while let Some(Reverse((len, r))) = to_visit.pop() {
            let last_link_node = *r.last().unwrap();
            if last_link_node.1 == to_node {
                return Some(r.iter().skip(1).map(|(link, _)| *link).collect::<Vec<_>>());
            }
            if used_links.contains(&last_link_node.0) {
                continue;
            }
            used_links.insert(last_link_node.0);
            for link_to in self.hash.get(&last_link_node.1).unwrap().iter() {
                if forbidden_links.contains(&link_to.0) {
                    continue;
                }
                if !used_links.contains(&link_to.0) {
                    let mut cand = r.clone();
                    cand.push(*link_to);
                    to_visit.push(Reverse((len + 1, cand)));
                }
            }
        }
        None
    }
}
