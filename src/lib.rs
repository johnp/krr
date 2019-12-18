#[macro_use]
extern crate itertools;

use std::{fmt, iter};
use std::convert::TryInto;
use std::ops::{BitAnd, BitOr};
use std::num::NonZeroU32;

use itertools::Itertools;
use unicode_segmentation::UnicodeSegmentation;

#[cfg(not(any(feature="map-indexmap", feature="map-hashbrown")))]
use std::collections::HashMap;
#[cfg(feature="map-indexmap")]
use indexmap::IndexMap as HashMap;
#[cfg(feature="map-hashbrown")]
use hashbrown::HashMap;

use keyed_priority_queue::HashKeyedPriorityQueue;
use std::cmp::{Reverse};

const DEBUG: bool = true;
const TRACE_REFINEMENTS: bool = true;

// TODO: move to naïve arbitrary-sized bit sets using some bitvec/bitfield/bitset crate or rustc's HybridBitSet
// TODO: move to advanced arbitrary-sized bit sets, e.g. idlset/hibitset/vod
//       that maybe even support compression/simd/... (Bitmap index compression)
// TODO: check if we really need a fast hamming weight implementation
// TODO: (nested) log2 (small)vec for faster constant time access instead of HashMaps
// TODO: reason about whether it's better to store the 2^n and calculate log2(2^n) on-the-fly
//       or if we should store n and calculate 2^n on-the-fly (simple bitshift -> better?)
// TODO: parallelization via rayon

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
    //       (we could add EmptyRelation/UniverseRelation and make use of this in compose()…)
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
    // TODO: improve converse storage (TzcntVec?)
    converses: HashMap<Relation, Relation>,
    // TODO: would it be possible to flatten this?
    compositions: TzcntTable,
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
        /*
        for ((rel1, rel2), &res) in self.compositions.iter().sorted() {
            writeln!(
                f,
                "{} ⋄ {} ≡ {}",
                self.relation_symbols.get(rel1).unwrap(),
                self.relation_symbols.get(rel2).unwrap(),
                self.relation_to_symbol(res.into())
            )?;
        }*/
        Ok(())
    }
}

impl QualitativeCalculus {
    // TODO: Buffered Reader(?)
    // TODO: iterate only once; maybe take any Iterator?
    // TODO: support reading in priorities
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

        let composition_map: HashMap<(Relation, Relation), Relation> = calculus_definition
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

        let mut compositions: TzcntTable = TzcntTable::with_size(200);  // TODO: correct size
        for ((rel1, rel2), res) in composition_map.into_iter() {
            let i = u32::from(rel1).trailing_zeros() as usize;
            let j = u32::from(rel2).trailing_zeros() as usize;

            if let Some(inner) = compositions.0.get_mut(i) {
                if let Some(combined) = inner.get_mut(j) {
                    //let prev = (*combined).unwrap_or(0.into());
                    //*combined = Some((u32::from(prev) | u32::from(res)).into());
                    match *combined {
                        Some(prev) => *combined = Some(NonZeroU32::new(u32::from(prev) | u32::from(res)).expect("Non-NonZeroU32 (with prev)!")),
                        None => *combined = Some(NonZeroU32::new(u32::from(res)).expect("Non-NonZeroU32!")),
                    }
                } else {
                    panic!("Could not get inner mut reference");
                }
            } else {
                panic!("Could not get inner mut vector");
            }
        }
        /*
        for (i, row) in compositions.iter().enumerate() {
            for (j, &column) in row.iter().enumerate() {
                if column.is_some() {
                    println!("{} ⋄ {} ≡ {:?}", relation_symbols.get(&(1 << i).into()).unwrap(), relation_symbols.get(&(1 << j).into()).unwrap(), column);
                }
            }
        }*/

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
            match self.relation_symbols.get(&Relation::from(single_base_relation)) {
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

    // TODO: consider inlining explicitly?
    // TODO: bench tzcnt+btc+shlx vs blsi+bslr vs blsi+xor: https://godbolt.org/z/CAqCbZ
    fn relation_to_base_relations(&self, relation: Relation) -> Vec<Relation> {
        if relation == self.empty_relation || relation == self.universe_relation {
            return vec![relation];
        }
        let mut res = Vec::new();
        let mut remaining_relations: u32 = relation.into();
        while remaining_relations != 0 {
            // compiles to tzcnt+btc/xor+shlx
            let lsb = 1u32 << remaining_relations.trailing_zeros(); // extract lsb
            remaining_relations ^= lsb; // remove lsb
            res.push(lsb.into());
        }
        res
    }

    #[allow(dead_code)]
    fn relation_to_base_relations_blsi_blsr(&self, relation: Relation) -> Vec<Relation> {
        if relation == self.empty_relation || relation == self.universe_relation {
            return vec![relation];
        }
        let mut res = Vec::new();
        let mut remaining_relations: u32 = relation.into();
        while remaining_relations != 0 {
            // compiles to blsi+blsr
            let lsb = remaining_relations & remaining_relations.overflowing_neg().0; // extract lsb
            remaining_relations &= remaining_relations - 1; // remove lsb
            res.push(lsb.into());
        }
        res
    }

    #[allow(dead_code)]
    fn relation_to_base_relations_blsi_xor(&self, relation: Relation) -> Vec<Relation> {
        if relation == self.empty_relation || relation == self.universe_relation {
            return vec![relation];
        }
        let mut res = Vec::new();
        let mut remaining_relations: u32 = relation.into();
        while remaining_relations != 0 {
            // compiles to bsli+xor
            let lsb = remaining_relations & remaining_relations.overflowing_neg().0; // extract lsb
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
                // TODO: investigate if providing size_hint leads to better results
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
                    // TODO: directly fold the converses without any vectors
                    let mut res = Vec::new();
                    for rel in self.relation_to_base_relations(relation) {
                        res.push(self.converses.get(&rel).unwrap()); //  TODO: unreachable!()
                    }
                    res.into_iter()
                        .fold(0, |acc, &rel| acc | u32::from(rel))
                        .into()

                    /*
                    let mut remaining_relations: u32 = relation.into();
                    iter::from_fn(move || {
                        if remaining_relations != 0 {
                            let tzcnt = remaining_relations.trailing_zeros();
                            let lsb = 1u32 << tzcnt; // extract lsb
                            remaining_relations ^= lsb; // remove lsb
                            Some(self.converses.get_by_tzcnt(tzcnt))
                        } else {
                            None
                        }
                    }).fuse()...
                    */
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

    pub fn compose(&self, relations1: Relation, relations2: Relation) -> Relation {
        let (rel1, rel2): (u32, u32) = (relations1.into(), relations2.into());
        if false {
            println!(
                "compose({}, {})",
                self.relation_to_symbol(rel1),
                self.relation_to_symbol(rel2)
            );
        }
        let universe_ones = u32::from(self.universe_relation).count_ones(); // TODO: extract?
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
            (1, 1) => match self.compositions.get(relations1, relations2) {
                Some(result) => (u32::from(result)).into(),
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

/*
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
struct Edge {
    i: u32,
    j: u32,
    priority: usize
}

impl Ord for Edge {
    fn cmp(&self, other: &Self) -> Ordering {
        self.priority.cmp(&other.priority).then_with(|| self.i.cmp(&other.i)).then_with(|| self.j.cmp(&other.j))
    }
}

impl PartialOrd for Edge {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
*/

#[derive(Debug, Clone)]
pub struct Solver<'a> {
    calculus: &'a QualitativeCalculus,
    largest_number: u32,
    // TODO: drop Option and just fill <no_info> with UNIVERSE directly
    //       (should have the size of the table; u32 instead of Relation might save another 50%)
    //       (unless (and this is likely) both are optimized into a single u32, in which case we
    //        *have* to do both to save 50% total)
    // TODO: rename to `edges` ?
    relation_instances: Vec<Vec<Option<Relation>>>, // includes the reverse relations
    priorities: Vec<u32>,
    pub comment: String,
}

impl<'a> fmt::Display for Solver<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !f.alternate() {
            writeln!(f, "largest_number: {}", self.largest_number)?;
        }
        //writeln!(f, "relation_instances:")?;
        /*
        for ((from, to), &rel) in self.relation_instances.iter().sorted() {
            writeln!(
                f,
                "{} → {} ≡ {}",
                from,
                to,
                self.calculus.relation_to_symbol(rel.into())
            )?;
        }
        */
        Ok(())
    }
}

impl<'a> Solver<'a> {
    // CalculusInstanceSolver / ConstraintReasoner
    // TODO: .lines() iterator allocates String for every line
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

        let mut instances: Vec<Vec<Option<Relation>>> = vec![vec![None; (largest_number + 1) as usize]; (largest_number + 1) as usize];
        for ((from, to), &rel) in relation_instances.iter().sorted() {
            let (i, j) = (*from as usize, *to as usize);
            if let Some(inner) = instances.get_mut(i) {
                if let Some(Some(prev)) = inner.get(j) {
                    inner[j] = Some(Relation::from(u32::from(*prev) | u32::from(rel)));
                } else {
                    inner[j] = Some(rel)
                }
                //let prev: Relation = inner.get(j).unwrap().unwrap_or(calculus.empty_relation);
                //inner[j] = Some(Relation::from(u32::from(prev) | u32::from(rel)));
            } else {
                panic!("Inner vec not initialized!");
                //instances[i] = Vec::with_capacity(largest_number as usize);
                //instances[i][j] = Some(rel);
            }
        }

        // TODO: move priorities into calculus (?)
        let max_relation: u32 = calculus.universe_relation.into();
        let max_relation_ones = max_relation.count_ones();
        let mut priorities: Vec<u32> = Vec::with_capacity((max_relation + 1) as usize);
        // TODO: implement & consider base relation priorities (e.g. "=" stronger than ">")
        for any_relation in 0..=max_relation {
            let wrapped_relation = Relation::from(any_relation);
            // pushes to index [any_relation as usize]
            priorities.push(match wrapped_relation {
                Relation::BaseRelation(rel) if rel.count_ones() == 0 => {
                    // empty relation => Maximum priority (shouldn't ever happen(?))
                    std::u32::MIN
                },
                Relation::ComposedRelation(rel) if rel.count_ones() == max_relation_ones => {
                    // universe relation => Minimum priority
                    std::u32::MAX
                },
                // TODO: is the direction relevant / correct here ?
                Relation::BaseRelation(_) if false => {
                    // any other base relation => derive from composition table
                    let compositions = calculus.compositions.get_all(wrapped_relation);
                    (compositions.fold(1f32, |acc, (j, res)| {
                        acc * (1f32 / u32::from(res).count_ones() as f32) // TODO: FIX THIS!!!!!!!!!
                    }) * 1000f32) as u32
                },
                Relation::ComposedRelation(_) | Relation::BaseRelation(_) => {
                    // any other composed relation => calculate via tightness formula
                    calculus.relation_to_base_relations(wrapped_relation).into_iter().fold(0, |acc, base_relation| {
                        acc + calculus.relations.values().fold(0, |acc, &other_base_relation| {
                            acc + u32::from(calculus.compose(base_relation, other_base_relation)).count_ones()
                            + u32::from(calculus.compose(calculus.converse(other_base_relation), calculus.converse(base_relation))).count_ones()
                        })
                    })
                },
            });
        }
        //println!("{:?}", priorities.iter().enumerate().collect_vec());

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
        } else if max_node < largest_number {
            println!("[WARNING] Largest number {0} is greater than actual largest number {1}. Clamping to {1}.", largest_number, max_node);
        }

        Solver {
            calculus,
            largest_number,
            relation_instances: instances,
            priorities,
            comment,
        }
    }

    #[inline]
    fn lookup(&self, first: u32, second: u32) -> Relation {
        match self.relation_instances.get(first as usize) {
            Some(inner) => match inner.get(second as usize) {
                Some(Some(rel)) => *rel,
                None => self.calculus.universe_relation,
                _ => self.calculus.universe_relation,
            },
            None => self.calculus.universe_relation,
        }
    }

    // TODO: do tuple arguments compile as well as primitives?
    #[inline]
    fn set_with_reverse(&mut self, key: (u32, u32), relation: Relation) {
        let _prev_rel = self.relation_instances[key.0 as usize][key.1 as usize] = Some(relation);
        // also, update reverse relation
        let _prev_conv = self.relation_instances[key.1 as usize][key.0 as usize] = Some(self.calculus.converse(relation));
        /*
        // This sanity check is wrong(?)
        if DEBUG {
            if let (Some(p), Some(pc)) = (prev_rel, prev_conv) {
                assert_eq!(p, self.calculus.converse(pc), "set() revealed previous inconsistency regarding converse on key {:?}", key);
            }
        }
        */
    }

    #[inline]
    fn get_priority(&self, r: Relation) -> u32 {
        self.priorities[u32::from(r) as usize]
    }

    fn trivially_inconsistent(&self) -> Result<(), String> {
        for (i, inner) in self.relation_instances.iter().enumerate() {
            for (j, maybe_rel) in inner.iter().enumerate() {
                if let Some(rel) = maybe_rel {
                    if *rel == self.calculus.empty_relation {
                        return Err(format!("Trivially inconsistent at ({}, {}).", i, j));
                    }
                }
            }
        }
        Ok(())
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
                    Ok(false) => {}       // do nothing
                    Err(msg) => return Err(msg),
                };
            }
        }
        Ok(())
    }


    pub fn a_closure_v2(&mut self) -> Result<(), String> {
        self.trivially_inconsistent()?;
        // TODO: Maximum size of queue hint to avoid re-allocation
        // TODO: skip edges that only have adjacent universal relations
        // TODO: skip if i == j == UNIVERSE (worth it? or is the compose-fast-path good enough?)
        let mut queue: HashKeyedPriorityQueue<(u32, u32), Reverse<u32>> =
            iproduct!(0..=self.largest_number, 0..=self.largest_number)
                // TODO: Idempotency of converse is not always guaranteed!
                .filter(|&(i, j)| i < j)
                .map(|(i, j)| ((i, j), Reverse(self.get_priority(self.lookup(i, j)))))
                .collect();
        if DEBUG {
            println!("Initial queue size: {}", queue.len());
        }
        while let Some((&(i, j), _p)) = queue.pop() {
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

    //
    // Triangulation:
    //
    // Identify sub-graph compute (triangulation = NP-Complete)
    // restrict operations to sub-graph
    // heuristic to spend time
    // ddg: SARISSA

    // TODO: A Universal A-Closure (with laws; triangulation?)
    pub fn universal_a_closure(&mut self) -> Result<(), String> {
        unimplemented!()
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
        queue: Option<&mut HashKeyedPriorityQueue<(u32, u32), Reverse<u32>>>,
    ) -> Result<bool, String> {
        // refined_ik = intersect(c_ik, compose(c_ij, c_jk))
        let composed = self.calculus.compose(c_ij, c_jk);
        let refined_ik = intersect(c_ik.into(), composed.into()).into();

        if c_ik != refined_ik {
            let tuple = (i, k);
            self.set_with_reverse(tuple, refined_ik);

            // TODO: ensure these if-conditions are coalesced in !DEBUG mode (1 less branch)
            // TODO: Optimally, DEBUG mode still inlines the format! into the lower if-branches
            if refined_ik == self.calculus.empty_relation || DEBUG {
                // TODO: it may be better to extract this format! to an #[inline(never)] function
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
                } else if DEBUG && TRACE_REFINEMENTS {
                    println!("{}", msg); // TODO: lock stdout for this?
                }
            }
            if let Some(q) = queue {
                q.set((i, k), Reverse(self.get_priority(refined_ik)));
            }
            // refined successfully
            return Ok(true);
        }
        // did not refine
        Ok(false)
    }

    // TODO: this could be **SO** much nicer
    fn non_base_relations_to_fix(&self) -> Vec<(u32, u32)> {
        let mut res = Vec::new();
        for (i, inner) in self.relation_instances.iter().enumerate() {
            for (j, maybe_rel) in inner.iter().enumerate() {
                if let Some(rel) = maybe_rel {
                    if u32::from(*rel).count_ones() > 1 {
                        res.push((i as u32, j as u32))
                    }
                }
            }
        }
        res
    }

    // TODO: bookkeeping of network changes to "undo" dynamically (no expensive cloning)
    // TODO: count levels going down and going up for DEBUG information for
    // Reasonable: about 10 to 50 variables in reasonable time
    pub fn refinement_search_v1(&mut self) -> Result<(), String> {
        if let Err(msg) = self.a_closure_v2() {
            if DEBUG {
                println!("Refinement search subtree failed: {}", msg);
            }
            return Err(msg);
        }
        if self.relation_instances.iter().all(|inner| inner.iter().all(|rel| {
            // TODO: can rel ever be None here?
            rel.is_some() && u32::from(rel.unwrap()).count_ones() == 1
        })) {
            if DEBUG {
                println!("Refinement search: A-closure resulted in base relations only => Success!");
            }
            return Ok(());
        }

        for (i, j) in self.non_base_relations_to_fix() {
            let composed_relation = self.lookup(i, j);
            let base_relations = self.calculus.relation_to_base_relations(composed_relation);
            if DEBUG {
                println!("Refinement search: {{{:?}}} at ({}, {})", self.calculus.relation_to_symbol(u32::from(composed_relation)), i, j);
            }
            for base_relation in base_relations {
                if DEBUG {
                    println!("Refinement search: Fixing '{}' at ({}, {})", self.calculus.relation_to_symbol(u32::from(base_relation)), i, j);
                }

                let mut cloned_solver = self.clone();
                cloned_solver.set_with_reverse((i, j), base_relation);
                if cloned_solver.refinement_search_v1().is_ok() {
                    return Ok(());
                }
            }
        }
        Err("Refinement search failed to find a solution".to_owned())
    }

    // TODO: other, improved refinement search versions
}

#[inline]
fn intersect(rel1: u32, rel2: u32) -> u32 {
    rel1.bitand(rel2)
}

// TODO: check if this vectorizes
#[inline]
fn fold_union(relations_iter: impl Iterator<Item = u32>) -> Relation {
    relations_iter.fold(0, |acc, rel| acc | rel).into()
}

#[derive(Debug)]
struct TzcntTable(pub Vec<Vec<Option<NonZeroU32>>>);

impl TzcntTable {
    fn with_size(n: usize) -> Self {
        TzcntTable(vec![vec![None; n]; n])
    }
}

// ~"Log2Map" (except for EMPTY/UNIVERSE)
// TODO: Implement "unsafe" direct array indexing without Option<>?
impl TzcntTable {
    pub fn get_by_tzcnt(&self, left_tzcnt: u32, right_tzcnt: u32) -> Option<NonZeroU32> {
        let inner = self.0.get(left_tzcnt as usize)?;
        Option::from(*inner.get(right_tzcnt as usize)?)
    }

    pub fn get(&self, rel1: Relation, rel2:Relation) -> Option<NonZeroU32> {
        let inner = self.0.get(u32::from(rel1).trailing_zeros() as usize)?;
        Option::from(*inner.get(u32::from(rel2).trailing_zeros() as usize)?)
    }

    pub fn get_all(&self, rel1: Relation) -> impl Iterator<Item = (u32, NonZeroU32)> + '_ {
        let inner: &Vec<Option<NonZeroU32>> = self.0.get(u32::from(rel1).trailing_zeros() as usize)
            .unwrap_or_else(|| panic!("Table row for {:?} is None!", rel1));
        inner.iter().enumerate().filter(|(_, &o)| o.is_some()).map(|(i, &o)| (1 << i, o.unwrap())).fuse()
    }
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
