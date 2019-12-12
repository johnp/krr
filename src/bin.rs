#[macro_use]
extern crate clap;
extern crate unicode_segmentation;

use std::fs;
use std::io;
use std::iter;

use clap::{App, Arg};

use krr::QualitativeCalculus;
use krr::Solver;
use std::collections::BTreeMap;
use std::fmt::{Display, Error, Formatter};
use std::io::Write;

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
    let matches = App::new(crate_name!())
        .version(crate_version!())
        .about(crate_description!())
        .author(crate_authors!("\n"))
        .arg(Arg::with_name("VERBOSE")
            .help("Enable verbose output")
            .short("v")
            .long("verbose")
        )
        .arg(
            Arg::with_name("CALC_INPUT")
                .help("Calculus input file to read")
                .required(true)
                .index(1),
        )
        .arg(
            Arg::with_name("PC_INPUT")
                .help("Instance input file to read")
                .required(true)
                .index(2),
        )
        .arg(
            Arg::with_name("PC_INDEX")
                .help("Index, starting at 1, of the instance to solve (within the given file)")
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
                .help("Solver (version) to use (A-Closure)")
                .required(false)
                // TODO: Increment default version once supported
                .takes_value(true)
                .default_value("v1")
                .possible_values(&["v1", "v2"]),
        )
        .get_matches();

    println!(
        "Using calc input file: {}",
        matches.value_of("CALC_INPUT").unwrap()
    );
    println!(
        "Using pc input file: {}",
        matches.value_of("PC_INPUT").unwrap()
    );
    let verbose = matches.value_of("VERBOSE").is_some();
    let calc_input = fs::read_to_string(matches.value_of("CALC_INPUT").unwrap())
        .expect("Failed to read CALC_INPUT file");
    let pc_input = fs::read_to_string(matches.value_of("PC_INPUT").unwrap())
        .expect("Failed to read PC_INPUT file");

    let calculus = QualitativeCalculus::new(&calc_input);
    if verbose {
        println!("Calculus:\n{}", calculus);
    }

    let idx;
    let mut counter = 0;
    let mut errors = BTreeMap::new();
    let mut split = pc_input.split(".\n").map(|s| s.trim_matches('\n'));
    // don't judge me
    let iter: Box<dyn Iterator<Item = &str>> = if let Some(idx_str) = matches.value_of("PC_INDEX") {
        idx = idx_str.parse::<usize>().unwrap();
        Box::new(iter::once(split.nth(idx - 1).unwrap_or_else(|| {
            panic!("Could not find instance at index '{}'", idx)
        })))
    } else {
        idx = 1;
        Box::new(split)
    };
    // TODO: very cheap timing information
    for (pc, i) in iter.zip(idx..) {
        if pc.is_empty() {
            continue;
        }
        let mut solver = Solver::new(&calculus, pc);
        let consistent: Option<bool> = comment_parse(&solver.comment);
        println!(
            "Comment (parsed consistent: {:?}): {}",
            consistent, solver.comment
        );
        let version = matches.value_of("SOLVER").unwrap();
        println!("Solver ({}):\n{}", version, solver);
        let result = match version {
            "v1" => solver.a_closure_v1(),
            "v2" => solver.a_closure_v2(),
            _ => panic!("Unexpected version {}", version),
        };
        match result {
            Ok(()) => {
                println!("Result: Consistent");
                //println!("Reduced: {:#}", solver);
                if consistent == Some(false) {
                    let _ = io::stdout().flush();
                    eprintln!("ERROR: INPUT ASSERTS INCONSISTENCY!");
                    let _ = io::stderr().flush();
                    errors.insert(i, ErrorType::FalsePositive);
                }
            }
            Err(msg) => {
                println!("Result: Not three-consistent, because:\n{}", msg);
                if consistent == Some(true) {
                    let _ = io::stdout().flush();
                    eprintln!("ERROR: INPUT ASSERTS CONSISTENCY!");
                    let _ = io::stderr().flush();
                    errors.insert(i, ErrorType::FalseNegative);
                }
            }
        }
        counter += 1;
        println!("===========================================");
    }

    println!("Finished {} given QCSPs!", counter);
    if !errors.is_empty() {
        let _ = io::stdout().flush();
        eprintln!("{} ERRORS:", errors.len());
        for (idx, error) in errors.iter() {
            eprintln!("Instance {} has error: {}", idx, error);
        }
    }
}

fn comment_parse(comment: &str) -> Option<bool> {
    if comment.contains("NOT consistent") || comment.contains("inconsistent") {
        Some(false)
    } else if comment.contains("consistent") {
        Some(true)
    } else {
        None
    }
}
