#[macro_use]
extern crate itertools;
#[macro_use]
extern crate smallvec;
extern crate derive_more;

use std::cmp::Reverse;
use std::convert::{From, Into};
use std::iter::Fuse;
use std::mem::size_of;
use std::{fmt, iter};

use derive_more::{Binary, BitAnd, BitOr, BitOrAssign, BitXor, BitXorAssign, Display, From, Into};
use itertools::Itertools;
use smallvec::SmallVec;
use unicode_width::UnicodeWidthStr;

#[cfg(feature = "map-hashbrown")]
use hashbrown::HashMap;
#[cfg(all(feature = "map-indexmap", not(feature = "map-hashbrown")))]
use indexmap::IndexMap as HashMap;
#[cfg(not(any(feature = "map-indexmap", feature = "map-hashbrown")))]
use std::collections::HashMap;

use keyed_priority_queue::HashKeyedPriorityQueue;

const DEBUG: bool = false;
const TRACE_REFINEMENTS: bool = false;

// TODO: move to naïve arbitrary-sized bit sets using some bitvec/bitfield/bitset crate or rustc's HybridBitSet
// TODO: move to advanced arbitrary-sized bit sets, e.g. idlset/hibitset/vod
//       that maybe even support compression/simd/... (Bitmap index compression)
// TODO: instead of the above two options, const generics and generic associated types should get us to u128 quite easily
// TODO: check if we really need a fast hamming weight implementation
// TODO: parallelization via rayon
// TODO: consider the possibility of flattening some of the tables
// TODO: const generic over the number of base relations could allow for more efficient raw arrays

#[derive(
    Eq,
    PartialEq,
    Ord,
    PartialOrd,
    Hash,
    Clone,
    Copy,
    Debug,
    Display,
    Binary,
    From,
    Into,
    BitAnd,
    BitOr,
    BitXor,
    BitOrAssign,
    BitXorAssign,
)]
#[display(fmt = "{:b}", "_0")]
pub struct Relation(u32);

impl Relation {
    #[inline(always)]
    fn count_ones(self) -> u32 {
        self.0.count_ones()
    }
    #[inline(always)]
    fn trailing_zeros(self) -> u32 {
        self.0.trailing_zeros()
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
    universe_popcnt: u32,
}

impl fmt::Display for QualitativeCalculus {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "QualitativeCalculus:")?;
        writeln!(f, "relation encodings:")?;
        let max_symbol_len = self.max_symbol_len();
        let max_encoding_len = self.max_encoding_len();
        for (symbol, rel) in self.relations.iter().sorted() {
            // Workaround for fonts rendering EMPTY_SET as two columns wide
            // (just make everything else one column wider)
            let current_symbol_len = max_symbol_len + (symbol != EMPTY_SET) as usize;
            writeln!(
                f,
                "{0:1$}: {2:3$b}",
                symbol, current_symbol_len, rel, max_encoding_len
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
        for (i, outer) in self.compositions.0.iter().enumerate() {
            for (j, res) in outer.iter().enumerate() {
                writeln!(
                    f,
                    "{} ⋄ {} ≡ {}",
                    self.relation_symbols
                        .get(&Relation(2u32.pow(i as u32)))
                        .unwrap(),
                    self.relation_symbols
                        .get(&Relation(2u32.pow(j as u32)))
                        .unwrap(),
                    self.relation_to_symbol(Relation(*res))
                )?;
            }
        }
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
        let empty_relation: Relation = Relation(0);
        relation_symbols.insert(empty_relation, EMPTY_SET.to_owned());
        let mut last_shl = 0;
        for line in calculus_definition
            .lines()
            .skip_while(|&l| !l.contains("relations"))
        {
            if !line.is_empty() && !line.contains("relations") {
                for (relation, i) in line.split_ascii_whitespace().zip(0u32..) {
                    relation_symbols.insert(
                        Relation(
                            1u32.checked_shl(i)
                                .expect("Number of relations must be <= 30."),
                        ),
                        relation.to_owned(),
                    );
                    last_shl = i;
                }
                break; // only one line
            }
        }
        let universe_relation = Relation(
            1u32.checked_shl(last_shl + 1)
                .expect("Number of relations must be <= 30.")
                - 1,
        );
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

        // TODO: directly fill compositions TzcntTable
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
                            Some(value) => *value,
                            _ => panic!("Unexpected relation {} found in composition table", rel),
                        },
                    ),
                );
                ((first, second), result)
            })
            .collect();

        let mut compositions = TzcntTable::with_size(relations.len() - 2);
        for ((rel1, rel2), res) in composition_map.into_iter() {
            let i = rel1.trailing_zeros() as usize;
            let j = rel2.trailing_zeros() as usize;

            if let Some(inner) = compositions.0.get_mut(i) {
                if let Some(combined) = inner.get_mut(j) {
                    let prev = *combined;
                    *combined = prev | u32::from(res);
                } else {
                    panic!("Could not get inner mut reference");
                }
            } else {
                panic!("Could not get inner mut vector");
            }
        }

        QualitativeCalculus {
            relation_symbols,
            relations,
            converses,
            compositions,
            empty_relation,
            universe_relation,
            universe_popcnt: universe_relation.count_ones(),
        }
    }

    fn max_symbol_len(&self) -> usize {
        self.relations.keys().map(|s| s.width()).max().unwrap()
    }

    fn max_encoding_len(&self) -> usize {
        self.universe_popcnt as usize
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
                    Some(rel) => Some(rel),
                    None => None, // silently drop anything not a base relation (e.g. commas)
                })
                // TODO: If all are None we return Relation(0), which may be fine?
                .fold(Relation(0), |acc, rel| acc | rel)
        }
    }

    pub fn relation_to_symbol(&self, relation: Relation) -> String {
        if relation == self.empty_relation {
            return EMPTY_SET.to_owned();
        } else if relation == self.universe_relation {
            return UNIVERSE.to_owned();
        }
        let mut symbols = Vec::new();
        let mut remaining_relations = relation;
        while remaining_relations != Relation(0) {
            let single_base_relation = 1u32 << remaining_relations.trailing_zeros();
            match self.relation_symbols.get(&Relation(single_base_relation)) {
                Some(symbol) => symbols.push(symbol),
                None => {
                    panic!(
                        "Symbol for base relation '{:b}' (part of '{:b}') not found!",
                        single_base_relation, relation
                    );
                }
            }
            remaining_relations ^= Relation(single_base_relation);
        }
        symbols.into_iter().join(",")
    }

    // TODO: bench tzcnt+btc+shlx vs blsi+bslr vs blsi+xor: https://godbolt.org/z/CAqCbZ
    #[allow(dead_code)]
    fn relation_to_base_relations_old(
        &self,
        relation: Relation,
    ) -> SmallVec<[Relation; size_of::<u32>() * 8]> {
        let mut res = SmallVec::with_capacity(self.relations.len());
        let mut remaining_relations: u32 = relation.into();
        while remaining_relations != 0 {
            // compiles to tzcnt+btc/xor+shlx
            let lsb = 1u32 << remaining_relations.trailing_zeros(); // extract lsb
            remaining_relations ^= lsb; // remove lsb
            res.push(Relation(lsb));
        }
        res
    }

    #[inline]
    fn relation_to_base_relations(
        &self,
        relation: Relation,
    ) -> SmallVec<[Relation; size_of::<u32>() * 8]> {
        let mut res = SmallVec::with_capacity(self.relations.len());
        let mut remaining_relations: u32 = relation.into();
        while remaining_relations != 0 {
            // compiles to blsi+blsr
            let lsb = remaining_relations & remaining_relations.overflowing_neg().0; // extract lsb
            remaining_relations &= remaining_relations - 1; // remove lsb
            res.push(Relation(lsb));
        }
        res
    }

    #[inline(always)]
    fn composed_relation_to_base_relations_iter(
        &self,
        relation: Relation,
    ) -> Fuse<impl Iterator<Item = Relation> + Clone> {
        let mut remaining_relations: u32 = relation.into();
        // TODO: investigate if providing size_hint leads to better results
        iter::from_fn(move || {
            if remaining_relations != 0 {
                // compiles to blsi+blsr (around 10% faster than tzcnt+btc/xor+shlx when hot)
                let lsb = remaining_relations & remaining_relations.overflowing_neg().0; // extract lsb
                remaining_relations &= remaining_relations - 1; // remove lsb
                Some(Relation(lsb))
            } else {
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
            // TODO: persist converses if not cheap?
            {
                // TODO: other converse fast paths possible?
                if relation == self.empty_relation {
                    self.universe_relation
                } else if relation == self.universe_relation {
                    self.empty_relation
                } else {
                    self.composed_relation_to_base_relations_iter(relation)
                        .map(|rel| self.converses.get(&rel).unwrap())
                        .fold(Relation(0), |acc, &rel| acc | rel)
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

    #[inline(always)] // ~850ms to 650ms
    fn get_composition(&self, relation1: Relation, relation2: Relation) -> Relation {
        unsafe { Relation(self.compositions.unchecked_get(relation1, relation2)) }
    }

    #[inline(always)] //  ~650ms to 550ms
    pub fn compose(&self, relation1: Relation, relation2: Relation) -> Relation {
        if false {
            println!(
                "compose({}, {})",
                self.relation_to_symbol(relation1),
                self.relation_to_symbol(relation2)
            );
        }
        /* // TODO: extracting these from the match to avoid popcnt doesn't actually seem to make a difference
           //       (may even regress performance slightly...)
        if relation1 == self.empty_relation || relation2 == self.empty_relation {
            return self.empty_relation;
        } else if relation1 == self.universe_relation || relation2 == self.universe_relation {
            return self.universe_relation;
        }*/
        match (relation1.count_ones(), relation2.count_ones()) {
            // Any EMPTY_SET => Empty Set
            (0, _) | (_, 0) => self.empty_relation,
            // Any UNIVERSAL => universal
            (rel1_popcnt, rel2_popcnt)
                if rel1_popcnt == self.universe_popcnt || rel2_popcnt == self.universe_popcnt =>
            {
                self.universe_relation
            }
            // Both base relations => Table lookup
            (1, 1) => self.get_composition(relation1, relation2),
            // Exactly one relation is a base relation
            // => Apply RA5 (distributivity of composition)
            (1, _) => {
                // union(compose(relation1, rel) for rel in relation2)
                fold_union(
                    self.composed_relation_to_base_relations_iter(relation2)
                        .map(|rel2| self.get_composition(relation1, rel2)),
                )
            }
            (_, 1) => {
                // union(compose(rel, relation2) for rel in relation1)
                fold_union(
                    self.composed_relation_to_base_relations_iter(relation1)
                        .map(|rel1| self.get_composition(rel1, relation2)),
                )
            }
            // Both sides are identical composed relations
            // TODO: measure if this fast-path is worth it
            (_, _) if relation1 == relation2 => {
                // union(compose(rel1, rel2) for rel1 in relation1 for rel2 in relation2)
                let v = self.relation_to_base_relations(relation1);

                let mut res = Relation(0);
                for &a in v.iter() {
                    for &b in v.iter() {
                        res |= self.get_composition(a, b);
                    }
                }
                res

                /* // TODO: measure
                fold_union(iproduct!(iter, cloned_iter)
                        .map(|(rel1, rel2)| {
                            self.get_composition(rel1, rel2)
                        }),
                )*/
            }
            // Both sides are composed relations
            (_, _) => {
                // union(compose(rel1, rel2) for rel1 in relation1 for rel2 in relation2)
                let v = self.relation_to_base_relations(relation2);
                // TODO: generate-once + clone vs .iter() always ? memcpy iter? (https://github.com/rust-lang/rust/pull/21846#issuecomment-110526401)
                //       (or is this all irrelevant since the compiler will unroll it anyways? ref: size_hint)
                let inner = v.iter();

                let mut res = Relation(0);
                for a in self.composed_relation_to_base_relations_iter(relation1) {
                    for &b in inner.clone() {
                        res |= self.get_composition(a, b);
                    }
                }
                res

                /* // TODO: measure
                fold_union(
                    iproduct!(
                        self.composed_relation_to_base_relations_iter(relation1),
                        self.composed_relation_to_base_relations_iter(relation2)
                    )
                    .map(|(rel1, rel2)| {
                        self.get_composition(rel1, rel2)
                    }),
                )*/
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Solver<'a> {
    calculus: &'a QualitativeCalculus,
    largest_number: u32,
    // TODO: rename to `edges` ?
    relation_instances: Vec<Vec<Relation>>, // includes the reverse relations
    priorities: Vec<u32>,
    pub comment: String,
}

impl<'a> fmt::Display for Solver<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "largest_number: {}", self.largest_number)?;
        if f.alternate() {
            // include graph
            writeln!(f, "relation_instances:")?;
            for (from, inner) in self.relation_instances.iter().enumerate() {
                for (to, &rel) in inner.iter().enumerate() {
                    writeln!(
                        f,
                        "{} → {} ≡ {}",
                        from,
                        to,
                        self.calculus.relation_to_symbol(rel)
                    )?;
                }
            }
        }
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
                .map::<Relation, _>(|r| {
                    calculus
                        .symbol_to_base_relation(r)
                        .unwrap_or_else(|| panic!("Could not find symbol '{}' in calculus", r))
                })
                .fold(Relation(0), |acc, rel| acc | rel);
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
                .map::<Relation, _>(|r| calculus.converse_str(&r))
                .fold(Relation(0), |acc, rel| acc | rel);
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

        // Convert HashMap to 2D-Vector
        // TODO: Omit the initial HashMap and directly parse into flattened 1D-Vector
        let mut instances: Vec<Vec<Relation>> =
            vec![
                vec![calculus.universe_relation; (largest_number + 1) as usize];
                (largest_number + 1) as usize
            ];
        for ((from, to), &rel) in relation_instances.iter().sorted() {
            let (i, j) = (*from as usize, *to as usize);
            instances[i][j] = rel;
        }

        // Calculate priorities
        // TODO: move priorities into calculus (?)
        let max_relation = calculus.universe_relation;
        let max_relation_ones = max_relation.count_ones();
        let mut priorities: Vec<u32> = Vec::with_capacity((u32::from(max_relation) + 1) as usize);
        // TODO: implement & consider base relation priorities (e.g. "=" stronger than ">")
        for any_relation in 0..=max_relation.into() {
            let wrapped_relation = Relation(any_relation);
            // pushes to index [any_relation as usize]
            priorities.push(match wrapped_relation {
                // TODO: extract these two cases (only happen each once)
                rel if rel.count_ones() == 0 => {
                    // empty relation => Maximum priority (shouldn't ever happen(?))
                    std::u32::MIN
                }
                rel if rel.count_ones() == max_relation_ones => {
                    // universe relation => Minimum priority
                    std::u32::MAX
                }
                // TODO: is the direction relevant / correct here ?
                _ if false => {
                    // any other base relation => derive from composition table
                    /*
                    let compositions = calculus.compositions.get_all(wrapped_relation);
                    (compositions.fold(1f32, |acc, (j, res)| {
                        acc * (1f32 / u32::from(res).count_ones() as f32) // TODO: FIX THIS!!
                    }) * 1000f32) as u32
                    */
                    1
                }
                //_ if true => { 1 }
                _ => {
                    // any other composed relation => calculate via tightness formula
                    calculus
                        .composed_relation_to_base_relations_iter(wrapped_relation)
                        .fold(0, |acc, first_relation| {
                            acc + calculus
                                .relations
                                .values()
                                .fold(0, |acc, &second_relation| {
                                    acc + calculus
                                        .compose(first_relation, second_relation)
                                        .count_ones()
                                        + calculus
                                            .compose(
                                                calculus.converse(second_relation),
                                                calculus.converse(first_relation),
                                            )
                                            .count_ones()
                                })
                        })
                }
            });
        }
        //println!("{:?}", priorities.iter().enumerate().collect_vec());

        match relation_instances.keys().map(|(a, b)| a.max(b)).max() {
            Some(&max_node) if max_node > largest_number =>
                panic!(
                    "Largest number wrong! (Is {}, but comment says {})",
                    max_node, largest_number
                ),
            Some(&max_node) if max_node < largest_number =>
                println!("[WARNING] Largest number {0} is greater than actual largest number {1}. Clamping to {1}.", largest_number, max_node),
            _ => {}
        }

        Solver {
            calculus,
            largest_number,
            relation_instances: instances,
            priorities,
            comment,
        }
    }

    #[inline(always)]
    fn lookup(&self, from: u32, to: u32) -> Relation {
        *unsafe {
            self.relation_instances
                .get_unchecked(from as usize)
                .get_unchecked(to as usize)
        }
    }

    #[inline(always)]
    fn set_with_reverse(&mut self, from: u32, to: u32, relation: Relation) {
        // TODO: bench unsafe get_unchecked_mut here vs safe variant
        *unsafe {
            self.relation_instances
                .get_unchecked_mut(from as usize)
                .get_unchecked_mut(to as usize)
        } = relation;
        *unsafe {
            self.relation_instances
                .get_unchecked_mut(to as usize)
                .get_unchecked_mut(from as usize)
        } = self.calculus.converse(relation);
        // safe variant
        //self.relation_instances[from as usize][to as usize] = relation;
        //self.relation_instances[to as usize][from as usize] = self.calculus.converse(relation);
    }

    #[inline(always)]
    fn get_priority(&self, r: Relation) -> u32 {
        *unsafe { self.priorities.get_unchecked(u32::from(r) as usize) }
        //self.priorities[u32::from(r) as usize]
    }

    fn only_has_base_relations(&self) -> bool {
        self.relation_instances.iter().all(|inner| {
            inner.iter().all(|rel| {
                let popcnt = rel.count_ones();
                // TODO: make sure universe is a base relation in this context
                popcnt == 1 || popcnt == self.calculus.universe_popcnt
            })
        })
    }

    // TODO: make sure that in the refinement algorithm we don't call this after the first time
    #[inline(never)]
    fn trivially_inconsistent(&self) -> Result<(), String> {
        for (i, inner) in self.relation_instances.iter().enumerate() {
            for (j, &rel) in inner.iter().enumerate() {
                if rel == self.calculus.empty_relation {
                    return Err(format!("Trivially inconsistent at ({}, {}).", i, j));
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
        self.a_closure_v2q(None)
    }

    fn a_closure_v2q(
        &mut self,
        queue: Option<HashKeyedPriorityQueue<(u32, u32), Reverse<u32>>>,
    ) -> Result<(), String> {
        self.trivially_inconsistent()?;
        // TODO: Maximum size of queue hint to avoid re-allocation
        // TODO: Consider radix-heap crate
        // TODO: skip edges that only have adjacent universal relations
        // TODO: skip if i == j == UNIVERSE (worth it? or is the compose-fast-path good enough?)
        let mut queue = queue.unwrap_or_else(|| {
            iproduct!(0..=self.largest_number, 0..=self.largest_number)
                // TODO: Idempotency of converse is not always guaranteed!
                .filter(|&(i, j)| i < j)
                .map(|(i, j)| ((i, j), Reverse(self.get_priority(self.lookup(i, j)))))
                .collect()
        });
        if DEBUG {
            println!("Initial queue size: {}", queue.len());
        }
        while let Some((&(i, j), _p)) = queue.pop() {
            // TODO: pre-compute & restart iterator? this range is about ~10% runtime cost for fast problems
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
                //let c_ij = self.lookup(i, j); // TODO: can we skip this lookup?

                self.refine(k, i, j, c_kj, c_ki, c_ij, Some(&mut queue))?;
            }
        }
        if DEBUG {
            println!("End queue size: {}", queue.len());
        }
        Ok(())
    }

    // TODO: A Universal A-Closure (with laws; triangulation?)
    //
    // Triangulation:
    //
    // Identify sub-graph compute (triangulation = NP-Complete)
    // restrict operations to sub-graph
    // heuristic to spend time
    // ddg: SARISSA
    pub fn universal_a_closure(&mut self) -> Result<(), String> {
        todo!("Universal A-Closure")
    }

    //noinspection GrazieInspection
    #[allow(clippy::too_many_arguments)]
    #[inline(always)]
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
        let refined_ik = intersect(c_ik, self.calculus.compose(c_ij, c_jk));

        if c_ik != refined_ik {
            self.set_with_reverse(i, k, refined_ik);

            // TODO: ensure these if-conditions are coalesced in !DEBUG mode (1 less branch (~2.8%))
            // TODO: Optimally, DEBUG mode still inlines the format! into the lower if-branches
            if refined_ik == self.calculus.empty_relation || DEBUG {
                // TODO: it may be better to extract this format! to an #[inline(never)] function or a macro
                // TODO: THIS COSTS ABOUT 100ms (~450ms to ~350ms) ?!?! (over 10 seconds in ref1_5)
                let msg = format!(
                    "\
Refined ({0},{2}):{3} over ({0},{1}):{4} and ({1},{2}):{5} to ({0},{2}):{6}
    c_ik = {7:010$b}
    c_ij = {8:010$b}
    c_jk = {9:010$b}
    {12}
    c_ik = {11:010$b}",
                    i,
                    j,
                    k,
                    self.calculus.relation_to_symbol(c_ik),
                    self.calculus.relation_to_symbol(c_ij),
                    self.calculus.relation_to_symbol(c_jk),
                    self.calculus.relation_to_symbol(refined_ik),
                    c_ik,
                    c_ij,
                    c_jk,
                    self.calculus.max_encoding_len(),
                    refined_ik,
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
    fn nodes_with_non_base_relations_to_fix(&self) -> Vec<(u32, u32)> {
        let mut res = Vec::new();
        for (i, inner) in self.relation_instances.iter().enumerate() {
            for (j, &rel) in inner.iter().enumerate() {
                if rel.count_ones() > 1 {
                    res.push((i as u32, j as u32))
                }
            }
        }
        res
    }

    pub fn refinement_search_v1(&mut self) -> Result<(), String> {
        if let Err(msg) = self.a_closure_v2() {
            if DEBUG {
                println!("Refinement search subtree failed: {}", msg);
            }
            return Err(msg);
        }
        if self.only_has_base_relations() {
            if DEBUG {
                println!(
                    "Refinement search: A-closure resulted in base relations only => Success!"
                );
            }
            return Ok(());
        }

        for (i, j) in self.nodes_with_non_base_relations_to_fix() {
            let composed_relation = self.lookup(i, j);
            let base_relations = self.calculus.relation_to_base_relations(composed_relation);
            if DEBUG {
                println!(
                    "Refinement search: {{{:?}}} at ({}, {})",
                    self.calculus.relation_to_symbol(composed_relation),
                    i,
                    j
                );
            }
            for base_relation in base_relations {
                if DEBUG {
                    println!(
                        "Refinement search: Fixing '{}' at ({}, {})",
                        self.calculus.relation_to_symbol(base_relation),
                        i,
                        j
                    );
                }

                let mut cloned_solver = self.clone();
                cloned_solver.set_with_reverse(i, j, base_relation);
                if cloned_solver.refinement_search_v1().is_ok() {
                    return Ok(());
                }
            }
        }
        Err("Refinement search failed to find a solution".to_owned())
    }

    pub fn refinement_search_v1_5(&mut self) -> Result<(), String> {
        self.refinement_search_v1_5q(None)
    }

    fn refinement_search_v1_5q(
        &mut self,
        queue: Option<HashKeyedPriorityQueue<(u32, u32), Reverse<u32>>>,
    ) -> Result<(), String> {
        if let Err(msg) = self.a_closure_v2q(queue) {
            if DEBUG {
                println!("Refinement search subtree failed: {}", msg);
            }
            return Err(msg);
        }

        if self.only_has_base_relations() {
            if DEBUG {
                println!(
                    "Refinement search: A-closure resulted in base relations only => Success!"
                );
            }
            return Ok(());
        }

        for (i, j) in self.nodes_with_non_base_relations_to_fix() {
            let composed_relation = self.lookup(i, j);
            let base_relations = self.calculus.relation_to_base_relations(composed_relation);
            if DEBUG {
                println!(
                    "Refinement search: {{{:?}}} at ({}, {})",
                    self.calculus.relation_to_symbol(composed_relation),
                    i,
                    j
                );
            }
            for base_relation in base_relations {
                if DEBUG {
                    println!(
                        "Refinement search: Fixing '{}' at ({}, {})",
                        self.calculus.relation_to_symbol(base_relation),
                        i,
                        j
                    );
                }

                let mut cloned_solver = self.clone();
                cloned_solver.set_with_reverse(i, j, base_relation);
                let q = iter::once(((i, j), Reverse(1))).collect();
                if cloned_solver.refinement_search_v1_5q(Some(q)).is_ok() {
                    return Ok(());
                }
            }
        }
        Err("Refinement search failed to find a solution".to_owned())
    }

    // TODO: bookkeeping of network changes to "undo" dynamically (no expensive cloning)
    // TODO: count levels going down and going up the tree with DEBUG
    // TODO: cost of sub-algebra?
    // Reasonable: about 10 to 50 variables in reasonable time
    pub fn refinement_search_v2(&mut self) -> Result<(), String> {
        // A-tractable sub-algebras
        todo!()
    }
}

#[inline(always)]
fn intersect(rel1: Relation, rel2: Relation) -> Relation {
    rel1 & rel2
}

// TODO: check if this vectorizes
#[inline]
fn fold_union(relations_iter: impl Iterator<Item = Relation>) -> Relation {
    relations_iter.fold(Relation(0), |acc, rel| acc | rel)
}

#[derive(Debug)]
struct TzcntTable(pub Vec<Vec<u32>>);

impl TzcntTable {
    fn with_size(n: usize) -> Self {
        TzcntTable(vec![vec![0; n]; n])
    }
}

// ~"Log2Map" (except for EMPTY/UNIVERSE)
impl TzcntTable {
    #[allow(unused)]
    #[inline(always)]
    unsafe fn unchecked_get_by_tzcnt(&self, left_tzcnt: u32, right_tzcnt: u32) -> u32 {
        *self
            .0
            .get_unchecked(left_tzcnt as usize)
            .get_unchecked(right_tzcnt as usize)
    }

    #[inline(always)]
    unsafe fn unchecked_get(&self, rel1: Relation, rel2: Relation) -> u32 {
        *self
            .0
            .get_unchecked(rel1.trailing_zeros() as usize)
            .get_unchecked(rel2.trailing_zeros() as usize)
    }

    #[allow(unused)]
    #[inline]
    fn get(&self, rel1: Relation, rel2: Relation) -> u32 {
        let inner = self.0.get(rel1.trailing_zeros() as usize).unwrap();
        *inner.get(rel2.trailing_zeros() as usize).unwrap()
    }
    /*
        #[inline]
        fn get_all(&self, rel1: Relation) -> impl Iterator<Item = (u32, NonZeroU32)> + '_ {
            let inner: &Vec<Option<NonZeroU32>> = self
                .0
                .get(rel1.trailing_zeros() as usize)
                .unwrap_or_else(#[cold]|| panic!("Table row for {:?} is None!", rel1));
            inner
                .iter()
                .enumerate()
                .filter(|(_, &o)| o.is_some())
                .map(|(i, &o)| (1 << i, o.unwrap()))
                .fuse()
        }
    */
}

pub fn parse_comment(comment: &str) -> Option<bool> {
    if comment.contains("NOT consistent") || comment.contains("inconsistent") {
        Some(false)
    } else if comment.contains("consistent") || (DEBUG && comment.contains("1-scale-free")) {
        // technically "None" 1-scale-free is considered Some(true) because I test with it frequently
        Some(true)
    } else {
        None
    }
}

// TODO: MOAR TESTS!
#[cfg(test)]
#[allow(dead_code)]
mod tests {
    use std::fs;

    use super::*;

    // Calculi

    fn setup_linear_calculus() -> QualitativeCalculus {
        QualitativeCalculus::new(&fs::read_to_string("linear.txt").unwrap())
    }

    fn setup_allen_calculus() -> QualitativeCalculus {
        QualitativeCalculus::new(&fs::read_to_string("allen.txt").unwrap())
    }

    fn setup_allen2_calculus() -> QualitativeCalculus {
        QualitativeCalculus::new(&fs::read_to_string("allen2.txt").unwrap())
    }

    // Calculus tests

    #[test]
    fn test_converse() {
        let calculus = setup_allen_calculus();
        assert_eq!(
            calculus.relation_to_symbol(calculus.converse_str("EQ")),
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
            calculus.relation_to_symbol(calculus.converse_str(&format!("EQ {}", EMPTY_SET))),
            "EQ"
        );
    }

    #[test]
    fn test_compose() {
        let calculus = setup_allen_calculus();
        assert_eq!(
            calculus.compose_str("EQ", "EQ"),
            calculus.symbol_to_base_relation("EQ").unwrap()
        );
        assert_eq!(
            calculus.relation_to_symbol(calculus.compose_str("EQ", EMPTY_SET)),
            EMPTY_SET
        );
        assert_eq!(
            calculus.relation_to_symbol(calculus.compose_str("EQ", UNIVERSE)),
            UNIVERSE
        );
    }

    #[test]
    fn test_relation_to_relations() {
        let calculus = setup_allen_calculus();
        assert_eq!(
            calculus
                .relation_to_base_relations(calculus.symbol_to_relation("EQ B"))
                .into_vec(),
            vec![
                calculus.symbol_to_relation("EQ"),
                calculus.symbol_to_relation("B")
            ]
        );
    }

    #[test]
    fn test_rel_to_rel_str() {
        let calculus = setup_allen_calculus();
        assert_eq!(calculus.relation_to_symbol(Relation(0)), EMPTY_SET);
        assert_eq!(
            calculus.relation_to_symbol(calculus.universe_relation),
            UNIVERSE
        );
    }

    // Solvers

    fn setup_easy_solvers(calculus: &QualitativeCalculus) -> Vec<Solver> {
        let input = fs::read_to_string("pc_test1.csp").unwrap();
        let mut solvers = Vec::new();
        for pc in input.split(".\n\n").into_iter() {
            solvers.push(Solver::new(&calculus, pc));
        }
        solvers
    }

    fn setup_medium6_solvers(calculus: &QualitativeCalculus) -> Vec<Solver> {
        let input = fs::read_to_string("ia_test_instances_6.txt").unwrap();
        let mut solvers = Vec::new();
        for pc in input.split(".\n\n").into_iter() {
            solvers.push(Solver::new(&calculus, pc));
        }
        solvers
    }

    fn setup_hard_solver1(calculus: &QualitativeCalculus) -> Solver {
        let input = fs::read_to_string("30x500_m_3_allen_eq1.csp").unwrap();
        Solver::new(&calculus, &input)
    }

    fn setup_hard_solvers(calculus: &QualitativeCalculus) -> Vec<Solver> {
        let input = fs::read_to_string("30x500_m_3_allen.csp").unwrap();
        let mut solvers = Vec::new();
        for pc in input.split(".\n\n").into_iter() {
            solvers.push(Solver::new(&calculus, pc));
        }
        solvers
    }

    fn setup_inconsistent_but_closed_solver(calculus: &QualitativeCalculus) -> Solver {
        let input = fs::read_to_string("inconsistent_but_closed.csp").unwrap();
        Solver::new(&calculus, &input)
    }

    // Solver tests

    macro_rules! try_verify {
        ($solver:expr, $alg:expr) => {
            let result = $alg;
            match parse_comment(&$solver.comment) {
                Some(true) if result.is_ok() => {}   // fine
                Some(false) if result.is_err() => {} // fine
                None => println!("[WARNING] test case is missing target value"), // indeterminable
                Some(true) if result.is_err() => panic!("False negative test case result!"),
                Some(false) if result.is_ok() => panic!("False positive test case result!"),
                _ => unreachable!(),
            }
        };
    }

    #[test]
    fn test_v1_easy() {
        let calculus = setup_linear_calculus();
        let mut solvers = setup_easy_solvers(&calculus);
        for solver in solvers.iter_mut() {
            try_verify!(solver, solver.a_closure_v1());
        }
    }

    #[test]
    fn test_v2_easy() {
        let calculus = setup_linear_calculus();
        let mut solvers = setup_easy_solvers(&calculus);
        for solver in solvers.iter_mut() {
            try_verify!(solver, solver.a_closure_v2());
        }
    }

    #[test]
    fn test_v2_medium6() {
        let calculus = setup_allen_calculus();
        let mut solvers = setup_medium6_solvers(&calculus);
        for solver in solvers.iter_mut() {
            try_verify!(solver, solver.a_closure_v2());
        }
    }

    #[test]
    fn test_v2_hard1() {
        let calculus = setup_allen_calculus();
        let mut solver = setup_hard_solver1(&calculus);
        assert!(solver.a_closure_v2().is_ok())
    }

    #[test]
    fn test_v2_inconsistent_but_closed() {
        let calculus = setup_allen_calculus();
        let mut solver = setup_inconsistent_but_closed_solver(&calculus);
        assert!(solver.a_closure_v2().is_ok()) // wrong result expected
    }

    #[test]
    fn test_ref1_5_inconsistent_but_closed() {
        let calculus = setup_allen_calculus();
        let mut solver = setup_inconsistent_but_closed_solver(&calculus);
        try_verify!(solver, solver.refinement_search_v1_5());
    }
}
