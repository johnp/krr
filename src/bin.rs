#[macro_use]
extern crate clap;

use std::collections::BTreeMap;
use std::fmt::{Display, Error, Formatter};
use std::fs;
use std::io;
use std::io::{Read, Write};
use std::iter;
use std::time::Instant;

use clap::{App, Arg};

use krr::*;
use std::borrow::Borrow;

#[derive(Debug)]
enum ErrorType {
    FalsePositive,
    FalseNegative,
}

impl Display for ErrorType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Self::FalsePositive => write!(f, "False Positive")?,
            Self::FalseNegative => write!(f, "False Negative")?,
        }
        Ok(())
    }
}

fn main() {
    #[allow(deprecated)] // TODO: Remove this once Clap macros stopped using std::sync::ONCE_INIT
    let matches = App::new(crate_name!())
        .version(crate_version!())
        .about(crate_description!())
        .author(crate_authors!("\n"))
        .arg(
            Arg::with_name("VERBOSE")
                .help("Enable verbose output. Multiple occurrences increase verbosity.")
                .short("v")
                .long("verbose")
                .multiple(true),
        )
        .arg(
            Arg::with_name("CALC_INPUT")
                .help("Calculus input file to read.")
                .required(true)
                .index(1),
        )
        .arg(
            Arg::with_name("PC_INPUT")
                .help("Instance input file to read. \"-\" reads from standard input.")
                .required(true)
                .index(2),
        )
        .arg(
            Arg::with_name("PC_INDEX")
                .help("Index, starting at 1, of the instance to solve (within the given file).")
                .required(false)
                .validator(|s| match s.parse::<usize>() {
                    Ok(_) => Ok(()),
                    Err(_) => Err("PC_INDEX must be a positive integer > 0".to_owned()),
                })
                .index(3),
        )
        .arg(
            Arg::with_name("SOLVER")
                .short("s")
                .long("solver")
                .help("Solver (version) to use.")
                .required(false)
                .takes_value(true)
                .default_value("v2")
                .possible_values(&["v1", "v2", "ref1", "ref1.5", "ref1.6", "ref1.9", "ref2"]),
        )
        .arg(
            Arg::with_name("A_TRACTABLE")
                .short("a")
                .long("a-tractable")
                .help("A-tractable sub-algebras input file to read")
                .required(false)
                .takes_value(true),
        )
        .get_matches();

    let verbose_count = matches.occurrences_of("VERBOSE");
    let calc_input = fs::read_to_string(matches.value_of("CALC_INPUT").unwrap())
        .expect("Failed to read CALC_INPUT file");
    let pc_input = match matches.value_of("PC_INPUT").unwrap() {
        "-" => {
            let mut s = String::new();
            io::stdin()
                .read_to_string(&mut s)
                .expect("Error reading STDIN");
            s
        }
        path => fs::read_to_string(path).expect("Failed to read PC_INPUT file"),
    };
    let a_tractable = matches
        .value_of("A_TRACTABLE")
        .map(|path| fs::read_to_string(path).expect("Failed to read A_TRACTABLE file"));

    if verbose_count >= 3 {
        println!("Using calculus input file: {}", calc_input);
        if pc_input == "-" {
            println!("Reading pc from stdin");
        } else {
            println!("Using pc input file: {}", pc_input);
        }
        if let Some(path) = a_tractable.borrow() {
            println!("Using a-tractable file: {}", path);
        }
    }

    let calculus = QualitativeCalculus::with_a_tractable(&calc_input, a_tractable.as_deref());
    if verbose_count >= 2 {
        println!("Calculus:\n{}", calculus);
    }

    let version = matches.value_of("SOLVER").unwrap();
    let idx;
    let mut counter = 0;
    let mut errors = BTreeMap::new();
    let mut split = pc_input
        .split(".\n")
        .map(|s| s.trim_matches('\n'))
        .filter(|s| !s.is_empty());
    // don't judge me
    let iter: Box<dyn Iterator<Item = &str>> = if let Some(idx_str) = matches.value_of("PC_INDEX") {
        idx = idx_str.parse::<usize>().unwrap();
        Box::new(iter::once(split.nth(idx - 1).unwrap_or_else(|| {
            panic!("Could not find instance at given index '{}'", idx)
        })))
    } else {
        idx = 1;
        Box::new(split)
    };
    let all_solvers_start = Instant::now();
    for (pc, i) in iter.zip(idx..) {
        if pc.is_empty() {
            println!("[WARNING] Empty instance at index {}", i);
            continue;
        }
        let mut solver = Solver::new(&calculus, pc);
        let consistent: Option<bool> = parse_comment(&solver.comment);
        println!(
            "Comment (parsed consistent: {:?}): {}",
            consistent, solver.comment
        );
        println!("Solver (idx: {}, s:{}):\n{}", i, version, solver);
        let time = Instant::now();
        let result = match version {
            "v1" => solver.a_closure_v1(),
            "v2" => solver.a_closure_v2(),
            "ref1" => solver.refinement_search_v1(),
            "ref1.5" => solver.refinement_search_v1_5(),
            "ref1.6" => solver.refinement_search_v1_6(),
            "ref1.9" => solver.refinement_search_v1_9(),
            "ref2" => solver.refinement_search_v2(),
            _ => panic!("Unexpected version {}", version),
        };
        println!("Time: {:?}", time.elapsed());
        match result {
            Ok(()) => {
                println!("Result: Consistent");
                if verbose_count >= 1 {
                    println!("Reduced: {:#}", solver);
                }
                if consistent == Some(false) {
                    let _ = io::stdout().flush();
                    eprintln!("[ERROR] INPUT ASSERTS INCONSISTENCY!");
                    let _ = io::stderr().flush();
                    errors.insert(i, ErrorType::FalsePositive);
                }
            }
            Err(msg) => {
                println!("Result: Not three-consistent, because:\n{}", msg);
                if consistent == Some(true) {
                    let _ = io::stdout().flush();
                    eprintln!("[ERROR] INPUT ASSERTS CONSISTENCY!");
                    let _ = io::stderr().flush();
                    errors.insert(i, ErrorType::FalseNegative);
                }
            }
        }
        counter += 1;
        println!("===========================================");
    }

    println!(
        "Finished {} given QCSP{} in {:?} total!",
        counter,
        if counter > 1 { "s" } else { "" },
        all_solvers_start.elapsed()
    );
    if !errors.is_empty() {
        let _ = io::stdout().flush();
        eprintln!("{} ERRORS:", errors.len());
        for (idx, error) in errors.iter() {
            eprintln!("Instance {} has error: {}", idx, error);
        }
    }
}
