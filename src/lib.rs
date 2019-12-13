#[macro_use]
extern crate itertools;

use std::collections::{HashMap, VecDeque};
use std::convert::TryInto;
use std::ops::{BitAnd, BitOr};
use std::{fmt, iter};

use itertools::Itertools;
use unicode_segmentation::UnicodeSegmentation;

const DEBUG: bool = false;

// TODO: move to naïve arbitrary-sized bit sets using some bitvec/bitfield/bitset crate or rustc's HybridBitSet
// TODO: move to advanced arbitrary-sized bit sets, e.g. idlset/hibitset/vod
//       that maybe even support compression/simd/... (Bitmap index compression)
// TODO: check if we really need a fast hamming weight implementation
// TODO: (nested) log2 (small)vec for faster constant time access instead of HashMaps
// TODO: reason about whether it's better to store the 2^n and calculate log2(2^n) on-the-fly
//       or if we should store n and calculate 2^n on-the-fly (simple bitshift -> better?)

// TODO: use newtypes
// TODO: derive_more to also derive &, &=, |, and |= or just implement manually
//#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Copy, Clone, Debug)]
//struct UnclassifiedRelation(u32);
//#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Copy, Clone, Debug)]
//struct BaseRelation(u32);
//#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Copy, Clone, Debug)]
//struct ComposedRelation(u32);
//#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Copy, Clone, Debug)]

#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Copy, Clone, Debug)]
pub enum Relation {
    // TODO: This distinction is really just for nicer display for now and adds unnecessary computation
    BaseRelation(u32),
    ComposedRelation(u32),
}

impl From<Relation> for u32 {
    fn from(relation: Relation) -> Self {
        match relation {
            Relation::BaseRelation(inner) | Relation::ComposedRelation(inner) => inner,
        }
    }
}

impl From<u32> for Relation {
    fn from(value: u32) -> Self {
        if value.count_ones() <= 1 {
            Relation::BaseRelation(value) // incl EMPTY_RELATION
        } else {
            Relation::ComposedRelation(value) // incl UNIVERSE
        }
    }
}

const EMPTY_SET: &str = "∅";
const UNIVERSE: &str = "𝓤";

#[derive(Debug)]
pub struct QualitativeCalculus {
    relation_symbols: HashMap<Relation, String>,
    relations: HashMap<String, Relation>,
    converses: HashMap<Relation, Relation>,
    // TODO: Use something better than a tuple key / use an actual table?
    compositions: HashMap<(Relation, Relation), Relation>,
    empty_relation: Relation,
    universe_relation: Relation,
}

impl fmt::Display for QualitativeCalculus {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "QualitativeCalculus:")?;
        writeln!(f, "relation encodings:")?;
        for (symbol, rel) in self.relations.iter().sorted() {
            writeln!(
                f,
                "{0:1$}: {2:3$b}",
                symbol,
                self.max_symbol_len(),
                u32::from(*rel),
                self.max_encoding_len()
            )?;
        }
        writeln!(f, "converses:")?;
        for (rel1, rel2) in self.converses.iter().sorted() {
            writeln!(
                f,
                "{}: {}",
                self.relation_symbols.get(rel1).unwrap(),
                self.relation_symbols.get(rel2).unwrap()
            )?;
        }
        writeln!(f, "compositions:")?;
        for ((rel1, rel2), &res) in self.compositions.iter().sorted() {
            writeln!(
                f,
                "{} ⋄ {} ≡ {}",
                self.relation_symbols.get(rel1).unwrap(),
                self.relation_symbols.get(rel2).unwrap(),
                self.relation_to_symbol(res.into())
            )?;
        }
        Ok(())
    }
}

impl QualitativeCalculus {
    // TODO: Buffered Reader(?)
    // TODO: iterate only once; maybe take any Iterator?
    pub fn new(calculus_definition: &str) -> QualitativeCalculus {
        // TODO: Consider not copying the string slices (cost: lifetime bound to argument)
        let mut relation_symbols: HashMap<Relation, String> = HashMap::new();
        let empty_relation = 0.into();
        relation_symbols.insert(empty_relation, EMPTY_SET.to_owned());
        let mut last_shl = 0;
        for line in calculus_definition
            .lines()
            .skip_while(|&l| !l.contains("relations"))
        {
            if !line.is_empty() && !line.contains("relations") {
                for (relation, i) in line.split_ascii_whitespace().zip(0u32..) {
                    relation_symbols.insert(
                        1u32.checked_shl(i)
                            .expect("Number of relations must be <= 30.")
                            .into(),
                        relation.to_owned(),
                    );
                    last_shl = i;
                }
                break; // only one line
            }
        }
        let universe_relation = (1u32
            .checked_shl(last_shl + 1)
            .expect("Number of relations must be <= 30.")
            - 1)
        .into();
        relation_symbols.insert(universe_relation, UNIVERSE.to_owned());

        let relations: HashMap<String, Relation> = relation_symbols
            .iter()
            .map(|(&k, v)| (v.clone(), k))
            .collect();

        let converses = calculus_definition
            .lines()
            .skip_while(|&l| !l.contains("converses"))
            .skip(1)
            .take_while(|&l| !l.is_empty())
            .map(|l| {
                let (first, second): (Relation, Relation) = l
                    .split_ascii_whitespace()
                    .map(|rel| {
                        *relations
                            .get(rel)
                            .expect("Bitset for relation '{}' not found")
                    })
                    .next_tuple()
                    .expect("Converse must be tuples of size 2.");
                (first, second)
            })
            .collect();

        let compositions = calculus_definition
            .lines()
            .skip_while(|&l| !l.contains("composition"))
            .skip(1)
            .take_while(|&l| !l.is_empty())
            .map(|l| {
                let (args, res_str) = l.splitn(2, '(').next_tuple().unwrap();
                let (first, second) = args
                    .split_ascii_whitespace()
                    .map(|rel| {
                        *relations
                            .get(rel)
                            .expect("Bitset for relation '{}' not found")
                    })
                    .next_tuple()
                    .expect("Composition argument must be a tuple of size 2.");
                let result = fold_union(
                    res_str.trim_end_matches(')').split_ascii_whitespace().map(
                        |rel| match relations.get(rel) {
                            Some(Relation::BaseRelation(value))
                            | Some(Relation::ComposedRelation(value)) => *value,
                            _ => panic!("Unexpected relation {} found in composition table", rel),
                        },
                    ),
                );
                ((first, second), result)
            })
            .collect();

        QualitativeCalculus {
            relation_symbols,
            relations,
            converses,
            compositions,
            empty_relation,
            universe_relation,
        }
    }

    fn max_symbol_len(&self) -> usize {
        self.relations
            .keys()
            .map(|s| s.graphemes(true).count())
            .max()
            .unwrap()
    }

    fn max_encoding_len(&self) -> usize {
        u32::from(self.universe_relation)
            .count_ones()
            .try_into()
            .unwrap()
    }

    #[inline]
    pub fn symbol_to_base_relation(&self, relation_symbol: &str) -> Option<Relation> {
        match self.relations.get(relation_symbol) {
            Some(&base_relation) => Some(base_relation),
            None => None,
        }
    }

    // Splits at ASCII whitespaces
    pub fn symbol_to_relation(&self, relation_symbol: &str) -> Relation {
        if let Some(base_rel) = self.symbol_to_base_relation(relation_symbol) {
            base_rel
        } else {
            relation_symbol
                .split_ascii_whitespace()
                .filter_map(move |g| match self.symbol_to_base_relation(g) {
                    Some(rel) => Some(u32::from(rel)),
                    None => None, // silently drop anything not a base relation (e.g. commas)
                })
                .fold(0, |acc, rel| acc | rel)
                .into()
        }
    }

    // TODO: drop this (unused)
    // Splits at ASCII whitespaces
    /* pub fn symbol_to_relations<'a, 'b, 'c: 'ab>(
        &'a self,
        relation_symbol: &'b str,
    ) -> Box<dyn Iterator<Item = Relation> + 'a + 'b> {
        if let Some(base_rel) = self.symbol_to_base_relation(relation_symbol) {
            Box::new(iter::once(base_rel))
        } else {
            Box::new(
                relation_symbol
                    .split_ascii_whitespace()
                    .filter_map(move |g| match self.symbol_to_base_relation(g) {
                        Some(rel) => Some(rel),
                        None => None, // drop anything not a base relation
                    }),
            )
        }
    }*/

    pub fn relation_to_symbol(&self, relation: u32) -> String {
        if relation == self.empty_relation.into() {
            return EMPTY_SET.to_owned();
        } else if relation == self.universe_relation.into() {
            return UNIVERSE.to_owned();
        }
        let mut symbols = Vec::new();
        let mut remaining_relations = relation;
        while remaining_relations != 0 {
            let single_base_relation = 1u32 << remaining_relations.trailing_zeros();
            match self.relation_symbols.get(&single_base_relation.into()) {
                Some(symbol) => symbols.push(symbol),
                None => {
                    panic!(
                        "Symbol for base relation '{:b}' (part of '{:b}') not found!",
                        single_base_relation, relation
                    );
                }
            }
            remaining_relations ^= single_base_relation;
        }
        symbols.into_iter().join(",")
    }

    pub fn relation_to_base_relations(&self, relation: Relation) -> Vec<Relation> {
        if relation == self.empty_relation || relation == self.universe_relation {
            return vec![relation];
        }
        let mut res = Vec::new();
        let mut remaining_relations: u32 = relation.into();
        while remaining_relations != 0 {
            let lsb = 1u32 << remaining_relations.trailing_zeros(); // extract lsb
            remaining_relations ^= lsb; // remove lsb
            res.push(lsb.into());
        }
        res
    }

    // just prototyping laziness in return type
    #[allow(dead_code)]
    fn relation_to_base_relation_iter(
        &self,
        relation: Relation,
    ) -> Box<dyn Iterator<Item = Relation>> {
        if relation == self.empty_relation || relation == self.universe_relation {
            Box::new(iter::once(relation))
        } else {
            let mut remaining_relations: u32 = relation.into();
            Box::new(
                // TODO: investigate if providing size_hint leads to better compilation
                iter::from_fn(move || {
                    if remaining_relations != 0 {
                        let lsb = 1u32 << remaining_relations.trailing_zeros(); // extract lsb
                        remaining_relations ^= lsb; // remove lsb
                        Some(lsb.into())
                    } else {
                        None
                    }
                })
                .fuse(),
            )
        }
    }

    // just prototyping laziness in return type
    #[allow(dead_code)]
    fn relation_to_base_relation_iter2(
        &self,
        relation: Relation,
    ) -> impl Iterator<Item = Relation> {
        let mut first = true;
        let mut finished = false;
        let mut remaining_relations: u32 = relation.into();
        let empty_rel = u32::from(self.empty_relation);
        let universe = u32::from(self.universe_relation);
        iter::from_fn(move || {
            if first && (remaining_relations == empty_rel || remaining_relations == universe) {
                first = false;
                finished = true;
                Some(relation)
            } else if !finished && remaining_relations != 0 {
                first = false;
                let lsb = 1u32 << remaining_relations.trailing_zeros(); // extract lsb
                remaining_relations ^= lsb; // remove lsb
                Some(lsb.into())
            } else {
                first = false;
                finished = true;
                None
            }
        })
        .fuse()
    }

    pub fn converse_str(&self, relation: &str) -> Relation {
        match self.relations.get(relation) {
            Some(&base_relation) => self.converse(base_relation),
            None => self.converse(self.symbol_to_relation(relation)),
        }
    }

    #[inline]
    pub fn converse(&self, relation: Relation) -> Relation {
        match self.converses.get(&relation) {
            Some(&rel) => rel,
            None =>
            // TODO: persist converse if not cheap?
            {
                // TODO: other converse fast paths possible?
                if relation == self.empty_relation {
                    self.universe_relation
                } else if relation == self.universe_relation {
                    self.empty_relation
                } else {
                    let mut res = Vec::new();
                    for rel in self.relation_to_base_relations(relation) {
                        res.push(self.converses.get(&rel).unwrap()); //  TODO: unreachable!()
                    }
                    res.into_iter()
                        .fold(0, |acc, &rel| acc | u32::from(rel))
                        .into()
                }
            }
        }
    }

    pub fn compose_str(&self, relation1: &str, relation2: &str) -> Relation {
        self.compose(
            self.symbol_to_relation(relation1),
            self.symbol_to_relation(relation2),
        )
    }

    //pub fn compose_simple(&self, relations1: Relation, relations2: Relation) -> Relation {
    //}

    pub fn compose(&self, relations1: Relation, relations2: Relation) -> Relation {
        let (rel1, rel2): (u32, u32) = (relations1.into(), relations2.into());
        if false {
            println!(
                "compose({}, {})",
                self.relation_to_symbol(rel1),
                self.relation_to_symbol(rel2)
            );
        }
        let universe_ones = u32::from(self.universe_relation).count_ones();
        match (rel1.count_ones(), rel2.count_ones()) {
            // Any EMPTY_SET => Empty Set
            (0, _) | (_, 0) => self.empty_relation,
            // Any UNIVERSAL => universal
            (rel1_popcnt, rel2_popcnt)
                if rel1_popcnt == universe_ones || rel2_popcnt == universe_ones =>
            {
                self.universe_relation
            }
            // Both base relations => Table lookup
            (1, 1) => match self.compositions.get(&(relations1, relations2)) {
                Some(&result) => result,
                None => {
                    panic!(
                        "Composition of base relations '{} {}' not in composition table",
                        self.relation_to_symbol(rel1),
                        self.relation_to_symbol(rel2)
                    );
                }
            },
            // At least one relation is not a base relation
            // => Apply RA5 (distributivity of composition)
            (1, _) => {
                // union(compose(relation1, rel) for rel in relation2)
                fold_union(
                    self.relation_to_base_relations(relations2)
                        .iter()
                        .map(|&rel2| self.compose(relations1, rel2).into()),
                )
            }
            (_, 1) => {
                // union(compose(rel, relation2) for rel in relation1)
                fold_union(
                    self.relation_to_base_relations(relations1)
                        .iter()
                        .map(|&rel1| self.compose(rel1, relations2).into()),
                )
            }
            // Both sides are not base relations
            (_, _) => {
                // union(compose(rel1, rel2) for rel1 in relation1 for rel2 in relation2)
                fold_union(
                    iproduct!(
                        self.relation_to_base_relations(relations1),
                        self.relation_to_base_relations(relations2)
                    )
                    .map(|(rel1, rel2)| self.compose(rel1, rel2).into()),
                )
            }
        }
    }
}

pub enum ThreeConsistency {}

#[derive(Debug)]
pub struct Solver<'a> {
    calculus: &'a QualitativeCalculus,
    largest_number: u32,
    // TODO: Node(u32)
    relation_instances: HashMap<(u32, u32), Relation>,
    pub comment: String,
}

impl<'a> fmt::Display for Solver<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !f.alternate() {
            writeln!(f, "largest_number: {}", self.largest_number)?;
        }
        writeln!(f, "relation_instances:")?;
        for ((from, to), &rel) in self.relation_instances.iter().sorted() {
            writeln!(
                f,
                "{} → {} ≡ {}",
                from,
                to,
                self.calculus.relation_to_symbol(rel.into())
            )?;
        }
        Ok(())
    }
}

// TODO(all closure algs): Take relation_instances by deep cloned value?
impl<'a> Solver<'a> {
    // CalculusInstanceSolver / ConstraintReasoner
    // TODO: sanity-check largest_number
    pub fn new(calculus: &'a QualitativeCalculus, input: &str) -> Solver<'a> {
        let mut relation_instances: HashMap<(u32, u32), Relation> = HashMap::new();
        let mut lines = input.lines().skip_while(|&l| l.is_empty());
        let mut header = lines.next().expect("Expected header").split('#');
        let largest_number = header
            .next()
            .expect("Expected largest node number")
            .trim()
            .parse::<u32>()
            .expect("The largest number representing a variable must be a positive integer.");
        let comment = header.next().expect("Expected comment").trim().to_owned();

        for line in lines {
            if line == "." || line.is_empty() {
                break;
            }
            let (args_str, relation_str) = line
                .splitn(2, '(')
                .next_tuple()
                .expect("Expected relation instance tuple");

            let (first, second) = args_str
                .split_ascii_whitespace()
                .map(|arg| arg.parse::<u32>().unwrap())
                .next_tuple()
                .expect("Expected tuple of nodes");
            let relations: Vec<String> = relation_str
                .trim_end_matches(')')
                .split_ascii_whitespace()
                .map(str::to_ascii_uppercase)
                .collect();

            let relation = relations
                .iter()
                .map::<u32, _>(|r| {
                    calculus
                        .symbol_to_base_relation(r)
                        .unwrap_or_else(|| panic!("Could not find symbol '{}' in calculus", r))
                        .into()
                })
                .fold(0, u32::bitor)
                .into();
            if let Some(previous_instance) = relation_instances.insert((first, second), relation) {
                assert_eq!(
                    previous_instance, relation,
                    "Previous instance ({},{}):{:?} conflicts with new instance {:?}",
                    first, second, previous_instance, relation
                );
            }
            // also, insert the converse and sanity-check against any included converse
            let derived_converse = relations
                .into_iter()
                .map::<u32, _>(|r| calculus.converse_str(&r).into())
                .fold(0, u32::bitor)
                .into();
            if let Some(included_converse) =
                relation_instances.insert((second, first), derived_converse)
            {
                assert_eq!(
                    included_converse, derived_converse,
                    "Included converse ({},{}):{:?} conflicts with derived converse {:?}",
                    second, first, included_converse, derived_converse
                );
            }
        }

        if relation_instances.is_empty() {
            panic!("No relation instances found!");
        }

        let &max_node = relation_instances
            .keys()
            .map(|(a, b)| a.max(b))
            .max()
            .unwrap();
        if max_node > largest_number {
            panic!(
                "Largest number wrong! (Is {}, but comment says {})",
                max_node, largest_number
            );
        }

        Solver {
            calculus,
            largest_number,
            relation_instances,
            comment,
        }
    }

    #[inline]
    fn lookup(&self, first: u32, second: u32) -> Relation {
        match self.relation_instances.get(&(first, second)) {
            Some(&res) => res,
            None => self.calculus.universe_relation,
        }
    }

    // TODO: do tuple arguments compile as well as primitives?
    #[inline]
    fn set(&mut self, key: (u32, u32), relation: Relation) {
        let _prev_rel = self.relation_instances.insert(key, relation);
        // also, update reverse relation
        let _prev_conv = self
            .relation_instances
            .insert((key.1, key.0), self.calculus.converse(relation));
        /*
        // This sanity check is wrong(?)
        if DEBUG {
            if let (Some(p), Some(pc)) = (prev_rel, prev_conv) {
                assert_eq!(p, self.calculus.converse(pc), "set revealed previous inconsistency with regards to converse on key {:?}", key);
            }
        }
        */
    }

    fn trivially_inconsistent(&self) -> Result<(), String> {
        if self
            .relation_instances
            .values()
            .any(|&rel| rel == self.calculus.empty_relation)
        {
            Err("Trivially inconsistent.".to_owned())
        } else {
            Ok(())
        }
    }

    pub fn a_closure_v1(&mut self) -> Result<(), String> {
        self.trivially_inconsistent()?;
        let mut s = true;
        while s {
            s = false;
            for (i, j, k) in itertools::iproduct!(
                0..=self.largest_number,
                0..=self.largest_number,
                0..=self.largest_number
            ) {
                if i == j || k == i || k == j {
                    continue;
                }

                let c_ik = self.lookup(i, k);
                let c_ij = self.lookup(i, j);
                let c_jk = self.lookup(j, k);
                match self.refine(i, j, k, c_ik, c_ij, c_jk, None) {
                    Ok(true) => s = true, // need to re-loop
                    Ok(false) => {}, // do nothing
                    Err(msg) => return Err(msg),
                };
            }
        }
        Ok(())
    }

    // TODO: idempotency of converse optimization?
    pub fn a_closure_v2(&mut self) -> Result<(), String> {
        self.trivially_inconsistent()?;
        // TODO: better deque? Priority? Implement priority (+version)!
        // TODO: skip all i <= j
        // TODO: skip edges that only have adjacent universal relations
        // TODO: skip if i == j == UNIVERSE (worth it? or is the compose-fast-path good enough?)
        let mut queue: VecDeque<(u32, u32)> =
            iproduct!(0..=self.largest_number, 0..=self.largest_number).collect();
        if DEBUG {
            println!("Initial queue size: {}", queue.len());
        }
        while !queue.is_empty() {
            let (i, j) = queue.pop_front().unwrap(); // TODO: i==j?
            for k in 0..=self.largest_number {
                if i == j || k == i || k == j {
                    continue;
                }
                let c_ik = self.lookup(i, k);
                let c_ij = self.lookup(i, j);
                let c_jk = self.lookup(j, k);

                self.refine(i, j, k, c_ik, c_ij, c_jk, Some(&mut queue))?;

                let c_kj = self.lookup(k, j);
                let c_ki = self.lookup(k, i);
                let c_ij = self.lookup(i, j); // TODO: can we skip this lookup?

                self.refine(k, i, j, c_kj, c_ki, c_ij, Some(&mut queue))?;
            }
        }
        if DEBUG {
            println!("End queue size: {}", queue.len());
        }
        Ok(())
    }

    //noinspection GrazieInspection
    #[allow(clippy::too_many_arguments)]
    #[inline]
    fn refine(
        &mut self,
        i: u32,
        j: u32,
        k: u32,
        c_ik: Relation,
        c_ij: Relation,
        c_jk: Relation,
        mut queue: Option<&mut VecDeque<(u32, u32)>>,
    ) -> Result<bool, String> {
        // i,k = intersect(c_ik, compose(c_ij, c_jk))
        let composed = self.calculus.compose(c_ij, c_jk);
        let refined_ik: Relation = intersect(c_ik.into(), composed.into()).into();

        if c_ik != refined_ik {
            let tuple = (i, k);
            self.set(tuple, refined_ik);
            queue = if let Some(q) = queue {
                if !q.contains(&tuple) {
                    q.push_back(tuple);
                }
                Some(q)
            } else {
                None
            };
            if refined_ik == self.calculus.empty_relation || DEBUG {
                let msg = format!(
                    "\
Refined ({0},{2}):{3} over ({0},{1}):{4} and ({1},{2}):{5} to ({0},{2}):{6}
    c_ik = {7:010$b}
    c_ij = {8:010$b}
    c_jk = {9:010$b}
    {13}
    comp = {12:010$b}
    c_ik = {11:010$b}",
                    i,
                    j,
                    k,
                    self.calculus.relation_to_symbol(c_ik.into()),
                    self.calculus.relation_to_symbol(c_ij.into()),
                    self.calculus.relation_to_symbol(c_jk.into()),
                    self.calculus.relation_to_symbol(refined_ik.into()),
                    u32::from(c_ik),
                    u32::from(c_ij),
                    u32::from(c_jk),
                    self.calculus.max_encoding_len(),
                    u32::from(refined_ik),
                    u32::from(composed),
                    "‒".repeat(self.calculus.max_encoding_len() + 7)
                );
                if refined_ik == self.calculus.empty_relation {
                    return Err(msg);
                } else if DEBUG {
                    println!("{}", msg);
                }
                if u32::from(refined_ik) > u32::from(c_ik) {
                    panic!("Refined to a more general relation!");
                }
            }
            // refined successfully
            return Ok(true);
        }
        // did not refine
        Ok(false)
    }

    // TODO: Universal A-Closure with priorities
    //fn universal_a_closure(&mut self) -> Result<(), String> {
    //    unimplemented!()
    //}
}

// TODO: refinement search
// TODO: bookkeeping of network changes to "undo" dynamically (less memory / no copies)
// TODO: implement custom inline refinement a-closure

#[inline]
fn intersect(rel1: u32, rel2: u32) -> u32 {
    rel1.bitand(rel2)
}

#[inline]
fn fold_union(relations_iter: impl Iterator<Item = u32>) -> Relation {
    relations_iter.fold(0, |acc, rel| acc | rel).into()
}

// TODO: MOAR TESTS!
#[cfg(test)]
#[allow(dead_code)]
mod tests {
    use std::fs;

    use super::*;

    fn setup_calculus() -> QualitativeCalculus {
        QualitativeCalculus::new(
            &fs::read_to_string("allen.txt").expect("Failed to read test file."),
        )
    }

    fn setup_easy_solvers(calculus: &QualitativeCalculus) -> Vec<Solver> {
        let input = fs::read_to_string("pc_test1.csp").expect("Failed to read test file.");
        let mut solvers = Vec::new();
        for pc in input.split(".\n\n").into_iter() {
            solvers.push(Solver::new(&calculus, pc));
        }
        solvers
    }

    fn setup_hard_solver1(calculus: &QualitativeCalculus) -> Solver {
        let input =
            fs::read_to_string("30x500_m_3_allen_eq1.csp").expect("Failed to read test file.");
        Solver::new(&calculus, &input)
    }

    #[test]
    fn test_converse() {
        let calculus = setup_calculus();
        assert_eq!(
            calculus.relation_to_symbol(u32::from(calculus.converse_str("EQ"))),
            "EQ"
        );

        /*
        assert_eq!(calculus.converse_str("B"), "BI");
        assert_eq!(calculus.converse_str("BI"), "B");
        assert_eq!(calculus.converse_str("D"), "DI");
        assert_eq!(calculus.converse_str("DI"), "D");
        assert_eq!(calculus.converse_str("O"), "OI".to_owned());
        assert_eq!(calculus.converse_str("OI"), "O".to_owned());
        assert_eq!(calculus.converse_str("M"), "MI".to_owned());
        assert_eq!(calculus.converse_str("MI"), "M".to_owned());
        assert_eq!(calculus.converse_str("S"), "SI".to_owned());
        assert_eq!(calculus.converse_str("SI"), "S".to_owned());
        assert_eq!(calculus.converse_str("F"), "FI");
        assert_eq!(calculus.converse_str("FI"), "F");
        */

        assert_eq!(
            calculus.relation_to_symbol(u32::from(
                calculus.converse_str(&format!("EQ {}", EMPTY_SET))
            )),
            "EQ"
        );
    }

    #[test]
    fn test_compose() {
        let calculus = setup_calculus();
        assert_eq!(
            calculus.compose_str("EQ", "EQ"),
            calculus.symbol_to_base_relation("EQ").unwrap()
        );
        assert_eq!(
            calculus.relation_to_symbol(u32::from(calculus.compose_str("EQ", EMPTY_SET))),
            EMPTY_SET
        );
        assert_eq!(
            calculus.relation_to_symbol(u32::from(calculus.compose_str("EQ", UNIVERSE))),
            UNIVERSE
        );
    }

    #[test]
    fn test_relation_to_relations() {
        let calculus = setup_calculus();
        assert_eq!(
            calculus.relation_to_base_relations(calculus.symbol_to_relation("EQ B")),
            vec![
                calculus.symbol_to_relation("EQ"),
                calculus.symbol_to_relation("B")
            ]
        );
    }

    #[test]
    fn test_rel_to_rel_str() {
        let calculus = setup_calculus();
        assert_eq!(calculus.relation_to_symbol(0), EMPTY_SET);
        assert_eq!(
            calculus.relation_to_symbol(u32::from(calculus.universe_relation)),
            UNIVERSE
        );
    }
}
