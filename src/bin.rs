extern crate clap;
extern crate unicode_segmentation;

use std::fs;
use std::io;
use std::iter;

use clap::{App, Arg};

use krr::QualitativeCalculus;
use krr::Solver;
use std::io::Write;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter, Error};

#[derive(Debug)]
enum ErrorType {
    FalsePositive,
    FalseNegative
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
    let matches = App::new("krr")
        .version("0.1")
        .about("Knowledge Representation & Reasoning")
        .author("Johannes Pfrang <johannespfrang@gmail.com>")
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
                .help("Index of the pc to solve (within the given file)")
                .required(false)
                .validator(|s| match s.parse::<usize>() {
                    Ok(_) => Ok(()),
                    Err(_) => Err("PC_INDEX must be a positive integer".to_owned()),
                })
                .index(3),
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
    let calc_input = fs::read_to_string(matches.value_of("CALC_INPUT").unwrap())
        .expect("Failed to read CALC_INPUT file");
    let pc_input = fs::read_to_string(matches.value_of("PC_INPUT").unwrap())
        .expect("Failed to read PC_INPUT file");

    let calculus = QualitativeCalculus::new(&calc_input);
    //println!("Calculus:\n{}", calculus);

    let idx;
    let mut counter = 0;
    let mut errors = BTreeMap::new();
    let split = pc_input.split(".\n");
    let iter: Box<dyn Iterator<Item = &str>> = if let Some(idx_str) = matches.value_of("PC_INDEX") {
        idx = idx_str.parse::<usize>().unwrap();
        Box::new(iter::once(split.take(idx).last().unwrap_or_else(|| {
            panic!("Could not find QCSP at index '{}'", idx)
        })))
    } else {
        idx = 1;
        Box::new(split)
    };
    for (pc, i) in iter.zip(idx..) {
        if pc.is_empty() {
            break;
        }
        let consistent: Option<bool> = pc
            .lines()
            .take(4)
            .map(|l| comment_parse(l))
            .skip_while(Option::is_none)
            .nth(0)
            .unwrap_or(None);
        let mut solver = Solver::new(&calculus, pc);
        println!("Comment: {}", solver.comment);
        println!("Solver:\n{}", solver);
        match solver.a_closure_v1() {
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
            eprintln!("Instance {} has error: {}",idx, error);
        }
    }
}

fn comment_parse(line: &str) -> Option<bool> {
    let start = line.find('#')?;
    let comment = &line[start..];
    if comment.contains("NOT consistent") || comment.contains("inconsistent") {
        Some(false)
    } else {
        Some(true)
    }
}
