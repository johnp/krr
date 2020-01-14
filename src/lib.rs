#[macro_use]
extern crate itertools;
extern crate derive_more;
extern crate smallvec;

use std::cmp::{Ordering, Reverse};
use std::convert::{From, Into};
use std::hash::Hash;
use std::mem::size_of;
use std::ops::Add;
use std::{fmt, iter, iter::Fuse};

use derive_more::{Binary, BitAnd, BitOr, BitOrAssign, BitXor, BitXorAssign, Display, From, Into};
use itertools::Itertools;
use num_traits::Zero;
use smallvec::SmallVec;
use unicode_width::UnicodeWidthStr;

#[cfg(feature = "map-hashbrown")]
use hashbrown::{HashMap, HashSet};
#[cfg(all(feature = "map-indexmap", not(feature = "map-hashbrown")))]
use indexmap::{IndexMap as HashMap, IndexSet as HashSet};
#[cfg(not(any(feature = "map-indexmap", feature = "map-hashbrown")))]
use std::collections::{HashMap, HashSet};

use keyed_priority_queue::HashKeyedPriorityQueue;
use pathfinding::directed::dijkstra::dijkstra_all;

const DEBUG: bool = false;
const DEBUG_PRIORITIES: bool = false;
const DEBUG_A_TRACTABLE: bool = false;
const DEBUG_A_CLOSURE: bool = false;
const TRACE_REFINEMENTS: bool = false;

// Long-term:
// TODO: move to naïve arbitrary-sized bit sets using some bitvec/bitfield/bitset crate or rustc's HybridBitSet
// TODO: move to advanced arbitrary-sized bit sets, e.g. idlset/hibitset/vod
//       that maybe even support compression/simd/... (Bitmap index compression)
// TODO: instead of the above two options, const generics and generic associated types should get us to u128 quite easily
// TODO: const generic over the number of base relations could simplify some code and may allow for more efficient raw arrays and better unrolling

// "Near"-term:
// TODO: Figure out why priorities aren't having the expected effect (~0 perf impact (even Reverse()'d))
// TODO: Flatten 2D-Vectors / Tables to 1D
// TODO: debug_println! macro
// TODO: parallelization via rayon (at first just, e.g. clone&divide at top of search tree)
// TODO: size SmallVec types according to |B|, once |B| is a const generic

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
pub struct Relation(u32); // TODO: make associated newtype of Calculus ?

impl Relation {
    #[inline(always)]
    fn count_ones(self) -> u32 {
        self.0.count_ones()
    }
    #[inline(always)]
    fn trailing_zeros(self) -> u32 {
        self.0.trailing_zeros()
    }
    #[inline(always)]
    #[allow(dead_code)]
    fn is_subset_of(self, rhs: Relation) -> bool {
        self.0 & !(rhs.0) == 0
    }
}

const EMPTY_SET: &str = "∅";
const UNIVERSE: &str = "𝓤";

#[derive(Debug)]
pub struct QualitativeCalculus {
    // TODO: convert to Vec or TzcntVec
    relation_symbols: HashMap<Relation, String>,
    relations: HashMap<String, Relation>,
    // TODO: improve converse storage (TzcntVec? / flattened)
    converses: HashMap<Relation, Relation>,
    // TODO: flatten this
    compositions: TzcntTable,
    a_tractable: HashSet<Relation>,
    // TODO: sorted by least constraining value (slides 09/pg13), and(?) maybe elide Option (just use empty vec?)
    a_tractable_splits: Vec<Option<Vec<Relation>>>, // indexed by goal Relation
    // TODO: universe_* may be converted to generic associated const(s)
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
        if !self.a_tractable.is_empty() {
            if DEBUG_A_TRACTABLE {
                writeln!(f, "a-tractable relations:")?;
                for &a_tractable_relation in self.a_tractable.iter() {
                    writeln!(f, "{}", self.relation_to_symbol(a_tractable_relation))?;
                }
            }
            writeln!(f, "a-tractable sub-algebra splits:")?;
            for (i, maybe_tractable_subset) in self.a_tractable_splits.iter().enumerate() {
                if let Some(tractable_subset) = maybe_tractable_subset {
                    let split_relation = Relation(i as u32);
                    write!(f, "{} => {{ ", self.relation_to_symbol(split_relation))?;
                    write!(
                        f,
                        "{}",
                        tractable_subset
                            .iter()
                            .map(|&composed_relation| self.relation_to_symbol(composed_relation))
                            .join(" 🙴 ")
                    )?;
                    writeln!(f, " }}")?;
                }
            }
        }
        Ok(())
    }
}

impl QualitativeCalculus {
    const EMPTY_RELATION: Relation = Relation(0);

    pub fn new(calculus_definition: &str) -> QualitativeCalculus {
        QualitativeCalculus::with_a_tractable(calculus_definition, None)
    }

    // TODO: Buffered Reader(?)
    // TODO: iterate only once; maybe take any Iterator?
    // TODO: support reading in priorities
    pub fn with_a_tractable(
        calculus_definition: &str,
        a_tractable_definiton: Option<&str>,
    ) -> QualitativeCalculus {
        // TODO: Consider not copying the string slices (cost: lifetime bound to argument)
        let mut relation_symbols: HashMap<Relation, String> = HashMap::new();
        relation_symbols.insert(Self::EMPTY_RELATION, EMPTY_SET.to_owned());
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

        // parse a-tractable subset definition
        let a_tractable = if let Some(def) = a_tractable_definiton {
            def.lines()
                .filter(|l| !l.is_empty())
                .filter(|l| !l.starts_with('#'))
                .map(|relation_symbol| {
                    // TODO: this duplicates `symbol_to_relation`
                    if let Some(&base_rel) = relations.get(relation_symbol) {
                        base_rel
                    } else {
                        relation_symbol
                            .split_ascii_whitespace()
                            .filter_map(|g| match relations.get(g) {
                                Some(rel) => Some(rel),
                                None => None, // silently drop anything not a base relation (e.g. commas)
                            })
                            .fold(Relation(0), |acc, &rel| acc | rel)
                    }
                })
                .collect()
        } else {
            HashSet::new()
        };

        let mut calculus = QualitativeCalculus {
            relation_symbols,
            relations,
            converses,
            compositions,
            a_tractable,
            a_tractable_splits: Vec::new(),
            universe_relation,
            universe_popcnt: universe_relation.count_ones(),
        };

        if !calculus.a_tractable.is_empty() {
            // pre-compute minimal covers
            calculus.a_tractable_splits = {
                let mut a_tractable_splits = vec![None; 1 + u32::from(universe_relation) as usize];

                #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
                struct Node {
                    rel: Relation,
                }

                #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
                struct Edge {
                    cost: u32,
                    label: Relation,
                }

                impl Add for Edge {
                    type Output = Edge;

                    fn add(self, rhs: Self) -> Self::Output {
                        // TODO: ugly rhs (order of cost-add operation within dijkstra.rs) dependency
                        Edge {
                            cost: self.cost + rhs.cost,
                            label: rhs.label,
                        }
                    }
                }

                impl Zero for Edge {
                    fn zero() -> Self {
                        Edge {
                            cost: u32::zero(),
                            label: Relation(0),
                        }
                    }

                    fn is_zero(&self) -> bool {
                        self.cost.is_zero()
                    }
                }

                impl Ord for Edge {
                    fn cmp(&self, other: &Self) -> Ordering {
                        self.cost.cmp(&other.cost)
                    }
                }

                impl PartialOrd for Edge {
                    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                        self.cost.partial_cmp(&other.cost)
                    }
                }

                // TODO: A*?
                let parents = dijkstra_all(
                    &Node {
                        rel: Self::EMPTY_RELATION,
                    },
                    |&Node { rel: v1 }| {
                        calculus
                            .a_tractable
                            .iter()
                            .filter_map(move |&a_tractable_subset| {
                                let v2 = v1 | a_tractable_subset;
                                if v2 != Self::EMPTY_RELATION {
                                    Some((v2, a_tractable_subset))
                                } else {
                                    None
                                }
                            })
                            .map(|s| {
                                (
                                    Node { rel: s.0 },
                                    Edge {
                                        cost: 1, // constant cost TODO: a-tractable sub-algebra cost model
                                        label: s.1,
                                    },
                                )
                            })
                    },
                );

                for r in 3u32..=universe_relation.into() {
                    if r.count_ones() == 1 {
                        continue; // skip base relations
                    }
                    if DEBUG_A_TRACTABLE {
                        println!(
                            "Building path for {}",
                            calculus.relation_to_symbol(Relation(r))
                        );
                    }

                    let goal = Node { rel: Relation(r) };
                    let path: Vec<(Node, Edge)> = {
                        // TODO: upstream as `build_path_with_edges`
                        let mut rev = vec![(goal.clone(), Edge::zero())];
                        let mut next = goal.clone();
                        while let Some((parent, edge)) = parents.get(&next) {
                            rev.push((parent.clone(), *edge));
                            next = parent.clone();
                        }
                        rev.reverse(); // TODO: we don't technically need this
                        rev
                    };

                    if DEBUG_A_TRACTABLE {
                        println!(
                            "path: {}",
                            path.iter()
                                .map(|e| format!(
                                    "(rel: {}, label: {})",
                                    calculus.relation_to_symbol(e.0.rel),
                                    calculus.relation_to_symbol(e.1.label)
                                ))
                                .join(" -> ")
                        );
                    }

                    // collect the labels (skipping empty relation labels at start/end)
                    let split: Vec<Relation> = path
                        .into_iter()
                        .map(
                            |(
                                _,
                                Edge {
                                    label: a_tractable, ..
                                },
                            )| a_tractable,
                        )
                        .filter(|&rel| rel != Self::EMPTY_RELATION)
                        .collect();

                    if split.is_empty() {
                        println!(
                            "[WARNING] Empty split occurred at relation {}!",
                            calculus.relation_to_symbol(goal.rel)
                        );
                        continue;
                    }

                    // make sure we *really* split into a-tractable only
                    for member in split.iter() {
                        assert!(calculus.a_tractable.contains(member))
                    }

                    // assert that the split covers relation r
                    assert!(
                        fold_union(split.iter().cloned()) & Relation(r) == Relation(r),
                        "Didn't fully cover {} with split {:?}!",
                        r,
                        split
                    );
                    if DEBUG_A_TRACTABLE {
                        println!(
                            "[SUCCESS] Found split: {:?}",
                            split
                                .iter()
                                .map(|&r| calculus.relation_to_symbol(r))
                                .collect_vec()
                        );
                    }
                    a_tractable_splits[r as usize] = Some(split);
                }
                a_tractable_splits
            };
        }
        calculus
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
                .filter_map(|g| match self.symbol_to_base_relation(g) {
                    Some(rel) => Some(rel),
                    None => None, // silently drop anything not a base relation (e.g. commas)
                })
                // TODO: This really should panic if all are None instead of returning Relation(0)
                .fold(Relation(0), |acc, rel| acc | rel)
        }
    }

    pub fn relation_to_symbol(&self, relation: Relation) -> String {
        if relation == Self::EMPTY_RELATION {
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
    ) -> SmallVec<[Relation; size_of::<Relation>() * 8]> {
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
    ) -> SmallVec<[Relation; size_of::<Relation>() * 8]> {
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
                if relation == Self::EMPTY_RELATION {
                    self.universe_relation
                } else if relation == self.universe_relation {
                    Self::EMPTY_RELATION
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
        if relation1 == Self::EMPTY_RELATION || relation2 == Self::EMPTY_RELATION {
            return Self::EMPTY_RELATION;
        } else if relation1 == self.universe_relation || relation2 == self.universe_relation {
            return self.universe_relation;
        }*/
        match (relation1.count_ones(), relation2.count_ones()) {
            // Any EMPTY_SET => Empty Set
            (0, _) | (_, 0) => Self::EMPTY_RELATION,
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
                let inner_vec = self.relation_to_base_relations(relation2);
                // TODO: generate-once + clone vs .iter() always ? memcpy iter? (https://github.com/rust-lang/rust/pull/21846#issuecomment-110526401)
                //       (or is this all irrelevant since the compiler will unroll it anyways? ref: size_hint)
                let inner = inner_vec.iter();

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

    pub fn get_a_tractable_split(&self, goal: Relation) -> Option<&Vec<Relation>> {
        debug_assert!(!self.a_tractable.is_empty());
        if let Some(subset) = self.a_tractable_splits.get(goal.0 as usize) {
            if subset.is_none() || subset.as_deref().unwrap().is_empty() {
                None
            } else {
                subset.as_ref()
            }
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct Solver<'a> {
    calculus: &'a QualitativeCalculus,
    largest_number: u32,
    // TODO: rename to `edges` ?
    relation_instances: Vec<Vec<Relation>>, // includes the reverse relations
    priorities: Vec<u32>,                   // indexed by Relation
    pub comment: String,
}

impl<'a> fmt::Display for Solver<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "largest_number: {}", self.largest_number)?;
        if DEBUG_PRIORITIES {
            writeln!(f, "priorities:")?;
            for (r, p) in self.priorities.iter().take(65).enumerate() {
                writeln!(
                    f,
                    "{} = {}",
                    self.calculus.relation_to_symbol(Relation(r as u32)),
                    p,
                )?;
            }
            writeln!(f, "... (elided)")?;
        }

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
                    "Previous instance or derived converse ({},{}):{:?} conflicts with new instance {:?}",
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
        let mut priorities: Vec<u32> =
            Vec::with_capacity((u32::from(calculus.universe_relation) + 1) as usize);
        priorities.push(std::u32::MIN); // empty relation => Maximum priority
                                        // TODO: implement & consider base relation priorities (e.g. "=" stronger than ">")
        for any_relation in 1..calculus.universe_relation.into() {
            let wrapped_relation = Relation(any_relation);
            // pushes to index [any_relation as usize]
            priorities.push(match wrapped_relation.count_ones() {
                //_ if true => 1, // TODO: this is ~= or faster than what's below...
                // TODO: is the direction relevant / correct here ?
                1 if false => {
                    // TODO: is this distinction even needed?
                    // base relation => derive from composition table
                    let compositions = calculus.compositions.get_all(wrapped_relation);
                    (compositions.fold(1f32, |acc, (_j, res)| {
                        acc * (1f32 / u32::from(res).count_ones() as f32) // TODO: FIX THIS!!!
                    }) * 1000f32) as u32
                }
                _ => {
                    // composed relation => calculate via tightness formula
                    // TODO: this can be *very* costly to run eagerly (e.g. on mid6)
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
        priorities.push(std::u32::MAX); // universe relation => Minimum priority
        assert_eq!(
            priorities.len() as u32,
            u32::from(calculus.universe_relation) + 1
        );

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

    #[inline]
    fn is_a_tractable(&self) -> bool {
        debug_assert!(!self.calculus.a_tractable.is_empty());
        for inner in self.relation_instances.iter() {
            for rel in inner.iter() {
                // TODO: do we also need to explicitly handle subsets of a_tractable members as a-tractable?
                if !self.calculus.a_tractable.contains(rel) {
                    return false;
                }
            }
        }
        true
    }

    // TODO: rename to "is_scenario"?
    #[inline]
    fn only_has_base_relations(&self) -> bool {
        // TODO: "self.relation_values()" iterator? sth auto-vectorizable?
        //       (does LLVM have a POPCNT auto-vectorization?)
        // TODO: manually vectorized POPCNT (https://github.com/kimwalisch/libpopcnt,
        //       http://0x80.pl/articles/sse-popcount.html)
        // TODO: may be able to use caller-side guarantee that `popcnt != 0`
        //       (trivial inconsistency will always have been checked beforehand)
        self.relation_instances.iter().all(|inner| {
            inner.iter().all(|rel| {
                let popcnt = rel.count_ones();
                // TODO: is universe a base relation in this context (scenario)?
                popcnt == 1 //|| popcnt == self.calculus.universe_popcnt
            })
        })
    }

    #[inline(never)]
    fn trivially_inconsistent(&self) -> Result<(), String> {
        // TODO: check vectorization (should trivially auto-vectorize)
        for (i, inner) in self.relation_instances.iter().enumerate() {
            for (j, &rel) in inner.iter().enumerate() {
                if rel == QualitativeCalculus::EMPTY_RELATION {
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

    // TODO: convert Err type to an informational struct and leave formatting to caller
    pub fn a_closure_v2(&mut self) -> Result<(), String> {
        self.trivially_inconsistent()?;
        self.a_closure_v2q(None)
    }

    // Note: callers must already have checked for trivial inconsistency
    fn a_closure_v2q(
        &mut self,
        queue: Option<HashKeyedPriorityQueue<(u32, u32), Reverse<u32>>>,
    ) -> Result<(), String> {
        // TODO: Maximum size of queue hint to avoid re-allocation
        // TODO: Consider radix-heap crate
        // TODO: skip edges that only have adjacent universal relations?
        // TODO: skip if i == j == UNIVERSE (worth it? or is the compose-fast-path good enough?)
        let mut queue = queue.unwrap_or_else(|| {
            iproduct!(0..=self.largest_number, 0..=self.largest_number)
                // TODO: Idempotency of converse is not always guaranteed
                .filter(|&(i, j)| i < j)
                .map(|(i, j)| ((i, j), Reverse(self.get_priority(self.lookup(i, j)))))
                .collect()
        });
        if DEBUG_A_CLOSURE {
            println!("Initial queue size: {}", queue.len());
        }
        while let Some((&(i, j), _p)) = queue.pop() {
            if DEBUG_PRIORITIES {
                println!("prio: {:?}", _p);
            }

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
        if DEBUG_A_CLOSURE {
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

            if refined_ik == QualitativeCalculus::EMPTY_RELATION {
                //return Err(String::new()); // <- for maximum performance (~10% (why?))
                return Err(self.format_refinement(i, j, k, c_ik, c_ij, c_jk, refined_ik));
            } else if DEBUG_A_CLOSURE && TRACE_REFINEMENTS {
                println!(
                    "{}",
                    self.format_refinement(i, j, k, c_ik, c_ij, c_jk, refined_ik)
                );
            }

            if let Some(q) = queue {
                // TODO: refined_ik being a subset of c_ik *should* guarantee, that we're always
                //       inserting an item of equal or higher priority? (ref radix-heap crate)
                q.set((i, k), Reverse(self.get_priority(refined_ik)));
            }
            // refined successfully
            return Ok(true);
        }
        // did not refine
        Ok(false)
    }

    #[allow(clippy::too_many_arguments)]
    #[inline(never)]
    fn format_refinement(
        &self,
        i: u32,
        j: u32,
        k: u32,
        c_ik: Relation,
        c_ij: Relation,
        c_jk: Relation,
        refined_ik: Relation,
    ) -> String {
        if DEBUG && TRACE_REFINEMENTS {
            format!(
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
            )
        } else {
            format!(
                "Refined ({0},{2}):{3} over ({0},{1}):{4} and ({1},{2}):{5} to ({0},{2}):{6}",
                i,
                j,
                k,
                self.calculus.relation_to_symbol(c_ik),
                self.calculus.relation_to_symbol(c_ij),
                self.calculus.relation_to_symbol(c_jk),
                self.calculus.relation_to_symbol(refined_ik)
            )
        }
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

    fn non_a_tractable_nodes(&self) -> Vec<(u32, u32)> {
        let mut res = Vec::new();
        for (i, inner) in self.relation_instances.iter().enumerate() {
            for (j, rel) in inner.iter().enumerate() {
                if !self.calculus.a_tractable.contains(rel) {
                    res.push((i as u32, j as u32))
                }
            }
        }
        res
    }

    pub fn refinement_search_v1(&mut self) -> Result<(), String> {
        self.trivially_inconsistent()?;
        self._refinement_search_v1()
    }

    fn _refinement_search_v1(&mut self) -> Result<(), String> {
        if let Err(msg) = self.a_closure_v2q(None) {
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
                if cloned_solver._refinement_search_v1().is_ok() {
                    return Ok(());
                }
            }
        }
        Err("Refinement search failed to find a solution".to_owned())
    }

    pub fn refinement_search_v1_5(&mut self) -> Result<(), String> {
        self.trivially_inconsistent()?;
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

    pub fn refinement_search_v1_6(&mut self) -> Result<(), String> {
        self.trivially_inconsistent()?;
        self.refinement_search_v1_6q(None)
    }

    // v1.5 with most constraining variable and least constraining value
    // TODO: this still seems to be wrong, as there's no performance improvement at all
    pub fn refinement_search_v1_6q(
        &mut self,
        queue: Option<HashKeyedPriorityQueue<(u32, u32), Reverse<u32>>>,
    ) -> Result<(), String> {
        if let Err(msg) = self.a_closure_v2q(queue) {
            return Err(msg);
        }

        if self.only_has_base_relations() {
            if DEBUG {
                println!(
                    "Refinement Search V1.6: A-closure resulted in base relations only => Success!"
                );
            }
            return Ok(());
        }

        // TODO: this is *likely* wrong
        let mut variable_queue: HashKeyedPriorityQueue<(u32, u32), Reverse<u32>> = self
            .nodes_with_non_base_relations_to_fix()
            .into_iter()
            .map(|(i, j)| ((i, j), Reverse(self.get_priority(self.lookup(i, j)))))
            .collect();

        if DEBUG {
            println!("Variable queue: {:?}", variable_queue);
        }

        while let Some((&(i, j), _p)) = variable_queue.pop() {
            let composed_relation = self.lookup(i, j); // TODO: remove duplicate lookup

            let base_relations = self.calculus.relation_to_base_relations(composed_relation);
            if DEBUG {
                println!(
                    "Refinement Search: {{{:?}}} at ({}, {})",
                    self.calculus.relation_to_symbol(composed_relation),
                    i,
                    j
                );
            }
            let mut value_queue: HashKeyedPriorityQueue<Relation, u32> = base_relations
                .into_iter()
                .map(|base_relation| (base_relation, self.get_priority(base_relation)))
                .collect();

            if DEBUG {
                println!("Value queue: {:?}", value_queue);
            }

            while let Some((&base_relation, _)) = value_queue.pop() {
                if DEBUG {
                    println!(
                        "Refinement Search: Fixing to '{}'...",
                        self.calculus.relation_to_symbol(base_relation),
                    );
                }

                let mut cloned_solver = self.clone();
                cloned_solver.set_with_reverse(i, j, base_relation);
                let q = iter::once(((i, j), Reverse(1))).collect();
                if cloned_solver.refinement_search_v1_6q(Some(q)).is_ok() {
                    return Ok(());
                }
            }
        }
        Err("Refinement Search V1.6 failed to find a solution".to_owned())
    }

    pub fn refinement_search_v1_9(&mut self) -> Result<(), String> {
        if self.calculus.a_tractable.is_empty() {
            panic!("Refinement Search V1.9 requires a-tractable subsets!");
        }
        self.trivially_inconsistent()?;
        self.refinement_search_v1_9q(None, 0)
    }

    // v1.6 with a-tractable subset partitioning
    // TODO: this is slow or doesn't terminate for non a-tractable inconsistent examples
    pub fn refinement_search_v1_9q(
        &mut self,
        queue: Option<HashKeyedPriorityQueue<(u32, u32), Reverse<u32>>>,
        depth: u32, // TODO: only track depth if DEBUG
    ) -> Result<(), String> {
        if DEBUG {
            println!("Depth: {}", depth);
        }

        if let Err(msg) = self.a_closure_v2q(queue) {
            if DEBUG {
                println!("A-closure failed here");
            }
            return Err(msg);
        }

        if self.is_a_tractable() {
            if DEBUG {
                println!(
                    "Refinement Search V1.9: A-closure resulted in base relations only => Success!"
                );
            }
            return Ok(());
        }

        let mut variable_queue: HashKeyedPriorityQueue<(u32, u32), Reverse<u32>> = self
            .non_a_tractable_nodes()
            .into_iter()
            .map(|(i, j)| ((i, j), Reverse(self.get_priority(self.lookup(i, j)))))
            .collect();

        if DEBUG_PRIORITIES {
            println!("Variable queue: {:?}", variable_queue);
        }

        while let Some((&(i, j), _p)) = variable_queue.pop() {
            let composed_relation = self.lookup(i, j);
            if DEBUG {
                println!(
                    "Refinement Search: {{{:?}}} at ({}, {})",
                    self.calculus.relation_to_symbol(composed_relation),
                    i,
                    j
                );
            }

            let base_relations = self
                .calculus
                .relation_to_base_relations(composed_relation)
                .into_vec(); // TODO: move this back into the match

            let split = match self.calculus.get_a_tractable_split(composed_relation) {
                Some(a_tractable_subset) => {
                    if DEBUG {
                        println!(
                            "A-tractable subsets: {}",
                            a_tractable_subset
                                .iter()
                                .map(|&r| self.calculus.relation_to_symbol(r))
                                .join(" 🙴 ")
                        );
                    }
                    a_tractable_subset
                }
                None => {
                    if DEBUG {
                        print!("Base relations: ");
                        for &r in base_relations.iter() {
                            print!("{},", self.calculus.relation_to_symbol(r));
                        }
                        println!();
                    }
                    &base_relations
                }
            };

            let mut value_queue: HashKeyedPriorityQueue<Relation, u32> = split
                .into_iter()
                .map(|&relation| (relation, self.get_priority(relation)))
                .collect();

            if DEBUG_PRIORITIES {
                println!("Value queue: {:?}", value_queue);
            }

            while let Some((&relation, _p)) = value_queue.pop() {
                if DEBUG {
                    println!(
                        "Fixing to '{}' (prio: {})...",
                        self.calculus.relation_to_symbol(relation),
                        _p
                    );
                }

                let mut cloned_solver = self.clone();
                cloned_solver.set_with_reverse(i, j, relation);
                let q = iter::once(((i, j), Reverse(1))).collect();
                if cloned_solver
                    .refinement_search_v1_9q(Some(q), depth + 1)
                    .is_ok()
                {
                    return Ok(());
                }
            }
        }
        Err("Refinement Search V1.9 failed to find a solution".to_owned())
    }

    // TODO: this is not working correctly yet
    // TODO: bookkeeping of network changes to "undo" dynamically (no expensive cloning)
    // TODO: count levels going down and going up the tree with DEBUG
    // TODO: most decisive node
    // TODO: least constraining value
    // Reasonable: about 10 to 50 variables in reasonable time
    #[allow(clippy::while_let_on_iterator, clippy::collapsible_if)]
    pub fn refinement_search_v2(&mut self) -> Result<(), String> {
        if self.calculus.a_tractable.is_empty() {
            panic!("Refinement Search V2 requires a-tractable subsets!");
        }
        self.trivially_inconsistent()?;

        if self.is_a_tractable() && DEBUG {
            println!("Refinement search V2: Started with an a-tractable subset.");
        }

        if let Err(msg) = self.a_closure_v2() {
            if DEBUG {
                println!("Refinement search V2: A-closure failed: {}", msg);
            }
            return Err(msg);
        }

        if self.is_a_tractable() {
            if DEBUG {
                println!(
                    "Refinement search V2: A-closure resulted in an a-tractable subset => Success!"
                );
            }
            return Ok(());
        }

        let mut nodes_to_fix = self.non_a_tractable_nodes();
        while !self.is_a_tractable() {
            // TODO: better SELECT
            let (i, j) = match nodes_to_fix.pop() {
                Some(n) => n,
                None => {
                    todo!("Ran out of nodes-to-fix!");
                    //nodes_to_fix = self.non_a_tractable_nodes();
                    //continue;
                }
            };
            let c_ij = self.lookup(i, j);

            let base_relations = self.calculus.relation_to_base_relations(c_ij); // XXX: ugly
            let a_tractable_subset = match self.calculus.get_a_tractable_split(c_ij) {
                Some(subset) => subset.as_ref(),
                None => base_relations.as_ref(),
            };

            if DEBUG {
                println!(
                    "Split {} into {:?}",
                    self.calculus.relation_to_symbol(c_ij),
                    a_tractable_subset
                        .iter()
                        .map(|&s| self.calculus.relation_to_symbol(s))
                        .collect_vec()
                );
            }

            // TODO: better SELECT
            let mut value_queue = a_tractable_subset.iter();
            while let Some(&a_tractable) = value_queue.next() {
                let mut cloned_solver = self.clone();
                cloned_solver.set_with_reverse(i, j, a_tractable);

                let q = iter::once(((i, j), Reverse(1u32))).collect();
                if cloned_solver.a_closure_v2q(Some(q)).is_ok() {
                    if DEBUG {
                        println!("A-Closure v2 succeeded...");
                    }
                    // success! apply changes...
                    let Solver {
                        // de-structure to move Vec
                        relation_instances: new_relation_instances,
                        ..
                    } = cloned_solver;
                    self.relation_instances = new_relation_instances;
                } else {
                    if DEBUG {
                        println!("A-Closure v2 failed...");
                    }
                    // TODO: correct FAIL / backtracking
                    panic!("Failed, because I can't backtrack yet :(")
                }
            }
        }

        if !self.nodes_with_non_base_relations_to_fix().is_empty() {
            todo!("Forgot to fix some stuff...");
        }

        if DEBUG {
            println!("Refinement search V2: Arrived at a-closed, a-tractable subset => Success!");
        }
        Ok(())
    }

    pub fn refinement_search_v3(&mut self) -> Result<(), String> {
        todo!("Refinement Search V3.0")
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

    #[inline]
    fn get_all(&self, rel1: Relation) -> impl Iterator<Item = (Relation, Relation)> + '_ {
        unsafe {
            let inner: &Vec<u32> = self.0.get_unchecked(rel1.trailing_zeros() as usize);
            inner
                .iter()
                .enumerate()
                .filter(|(_, &o)| o != 0)
                .map(|(i, &o)| (Relation((1 << i) as u32), Relation(o)))
        }
    }
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

#[cfg(test)]
#[allow(dead_code)]
mod tests {
    use std::fs;

    use super::*;

    // Calculi

    fn setup_linear_calculus() -> QualitativeCalculus {
        QualitativeCalculus::new(&fs::read_to_string("resources/linear.txt").unwrap())
    }

    fn setup_allen_calculus() -> QualitativeCalculus {
        QualitativeCalculus::new(&fs::read_to_string("resources/allen.txt").unwrap())
    }

    fn setup_allen_calculus_with_a_tractable() -> QualitativeCalculus {
        QualitativeCalculus::with_a_tractable(
            &fs::read_to_string("resources/allen.txt").unwrap(),
            Some(&fs::read_to_string("resources/ia_ord_horn.txt").unwrap()),
        )
    }

    fn setup_allen2_calculus() -> QualitativeCalculus {
        QualitativeCalculus::new(&fs::read_to_string("resources/allen2.txt").unwrap())
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

    #[test]
    fn test_a_tractable_subset() {
        let calculus = setup_allen_calculus_with_a_tractable();

        {
            let goal = Relation(0);
            assert_eq!(calculus.get_a_tractable_split(goal), None);
        }

        {
            let goal = Relation(0b01_1010_1010);
            println!("Goal({}): {}", goal.0, calculus.relation_to_symbol(goal));
            let split = calculus.get_a_tractable_split(goal).unwrap();

            assert!(split.contains(&Relation(170)));
            assert!(split.contains(&Relation(256)));

            for &s in split.iter() {
                println!("{} = {}", s.0, calculus.relation_to_symbol(s));
                assert!(calculus.a_tractable.contains(&s))
            }
            assert!(fold_union(split.iter().cloned()) & goal == goal);
        }

        {
            let goal = Relation(0b1_0101_0101_1110);
            println!("Goal({}): {}", goal.0, calculus.relation_to_symbol(goal));
            let split = calculus.get_a_tractable_split(goal).unwrap();

            // TODO: this path is non-deterministic
            //assert!(split.contains(&Relation(1356)));
            //assert!(split.contains(&Relation(2)));
            //assert!(split.contains(&Relation(5204)));

            for &s in split.iter() {
                println!("{} = {}", s.0, calculus.relation_to_symbol(s));
                assert!(calculus.a_tractable.contains(&s))
            }
            assert!(fold_union(split.iter().cloned()) & goal == goal);
        }

        {
            let goal = calculus.universe_relation; // 0b1_1111_1111_1111
            println!("Goal({}): {}", goal.0, calculus.relation_to_symbol(goal));
            let split = calculus.get_a_tractable_split(goal).unwrap();
            assert_eq!(split.len(), 1);
            assert_eq!(split[0], calculus.universe_relation);

            for &s in split.iter() {
                println!("{} = {}", s.0, calculus.relation_to_symbol(s));
                assert!(calculus.a_tractable.contains(&s))
            }
        }
    }

    // Solvers

    fn setup_easy_solvers(calculus: &QualitativeCalculus) -> Vec<Solver> {
        let input = fs::read_to_string("resources/pc_test1.csp").unwrap();
        let mut solvers = Vec::new();
        for pc in input.split(".\n\n").into_iter() {
            solvers.push(Solver::new(&calculus, pc));
        }
        solvers
    }

    fn setup_medium6_solvers(calculus: &QualitativeCalculus) -> Vec<Solver> {
        let input = fs::read_to_string("resources/ia_test_instances_6.txt").unwrap();
        let mut solvers = Vec::new();
        for pc in input.split(".\n\n").into_iter() {
            solvers.push(Solver::new(&calculus, pc));
        }
        solvers
    }

    fn setup_hard_solver1(calculus: &QualitativeCalculus) -> Solver {
        let input = fs::read_to_string("resources/30x500_m_3_allen_eq1.csp").unwrap();
        Solver::new(&calculus, &input)
    }

    fn setup_hard_solvers(calculus: &QualitativeCalculus) -> Vec<Solver> {
        let input = fs::read_to_string("resources/30x500_m_3_allen.csp").unwrap();
        let mut solvers = Vec::new();
        for pc in input.split(".\n\n").into_iter() {
            solvers.push(Solver::new(&calculus, pc));
        }
        solvers
    }

    fn setup_inconsistent_but_closed_solver(calculus: &QualitativeCalculus) -> Solver {
        let input = fs::read_to_string("resources/inconsistent_but_closed.csp").unwrap();
        Solver::new(&calculus, &input)
    }

    // Solver tests

    #[test]
    fn test_is_a_tractable() {
        let calculus = setup_allen_calculus_with_a_tractable();
        let solver = setup_inconsistent_but_closed_solver(&calculus);
        assert!(!solver.is_a_tractable())
    }

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
    #[ignore] // TODO: add consistency comments to file
    fn test_v2_hard() {
        let calculus = setup_allen2_calculus();
        let mut solvers = setup_hard_solvers(&calculus);
        for solver in solvers.iter_mut() {
            try_verify!(solver, solver.a_closure_v2());
        }
    }

    #[test]
    fn test_v2_inconsistent_but_closed() {
        let calculus = setup_allen_calculus();
        let mut solver = setup_inconsistent_but_closed_solver(&calculus);
        assert!(solver.a_closure_v2().is_ok()) // wrong result expected
    }

    #[test]
    //#[ignore] // this is too slow without `--release`
    fn test_ref1_5_inconsistent_but_closed() {
        let calculus = setup_allen_calculus();
        let mut solver = setup_inconsistent_but_closed_solver(&calculus);
        try_verify!(solver, solver.refinement_search_v1_5());
    }
}
