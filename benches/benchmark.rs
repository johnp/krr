use criterion::{black_box, criterion_group, criterion_main, Criterion};
use krr::{QualitativeCalculus, Solver};
use std::fs;
use std::time::Duration;

fn setup_calculus() -> QualitativeCalculus {
    QualitativeCalculus::new(&fs::read_to_string("resources/linear.txt").unwrap())
}

fn setup_allen_calculus() -> QualitativeCalculus {
    QualitativeCalculus::new(&fs::read_to_string("resources/allen.txt").unwrap())
}

fn setup_allen2_calculus() -> QualitativeCalculus {
    QualitativeCalculus::new(&fs::read_to_string("resources/allen2.txt").unwrap())
}

fn setup_easy_solvers(calculus: &QualitativeCalculus) -> Vec<Solver> {
    let input = fs::read_to_string("resources/pc_test1.csp").unwrap();
    let mut solvers = Vec::new();
    for pc in input.split(".\n").map(|s| s.trim_matches('\n')).into_iter() {
        if pc.is_empty() {
            continue;
        }
        solvers.push(Solver::new(&calculus, pc));
    }
    solvers
}

fn setup_medium6_solvers(calculus: &QualitativeCalculus) -> Vec<Solver> {
    let input = fs::read_to_string("resources/ia_test_instances_6.txt").unwrap();
    let mut solvers = Vec::new();
    for pc in input.split(".\n").map(|s| s.trim_matches('\n')).into_iter() {
        if pc.is_empty() {
            continue;
        }
        solvers.push(Solver::new(&calculus, pc));
    }
    solvers
}

fn setup_hard_solvers(calculus: &QualitativeCalculus) -> Vec<Solver> {
    let input = fs::read_to_string("resources/30x500_m_3_allen.csp").unwrap();
    let mut solvers = Vec::new();
    for pc in input.split(".\n").map(|s| s.trim_matches('\n')).into_iter() {
        if pc.is_empty() {
            continue;
        }
        solvers.push(Solver::new(&calculus, pc));
    }
    solvers
}

pub fn criterion_benchmark(c: &mut Criterion) {
    // finishes within hundreds of ns => susceptible to noise
    /*
    {
        let mut easy = c.benchmark_group("pc_test1");

        let linear_calculus = black_box(setup_calculus());
        let easy_solvers = black_box(setup_easy_solvers(&linear_calculus));

        for (i, mut solver) in easy_solvers.into_iter().enumerate() {
            easy.bench_function(&format!("idx: {}", i), |b| b.iter(|| solver.a_closure_v2()));
        }
    }
    */

    {
        let mut med = c.benchmark_group("ia_test_instances_6");
        med.sample_size(1_000);
        med.measurement_time(Duration::from_secs(10));

        let allen_calculus = black_box(setup_allen_calculus());
        let med_solvers = black_box(setup_medium6_solvers(&allen_calculus));

        for (i, mut solver) in med_solvers.into_iter().enumerate() {
            med.bench_function(&format!("idx: {}", i), |b| b.iter(|| solver.a_closure_v2()));
        }
    }

    {
        let mut hard = c.benchmark_group("30x500");
        hard.sample_size(10);
        hard.measurement_time(Duration::from_secs(60));

        let allen2_calculus = black_box(setup_allen2_calculus());
        let hard_solvers = black_box(setup_hard_solvers(&allen2_calculus));

        for (i, mut solver) in hard_solvers.into_iter().enumerate() {
            hard.bench_function(&format!("idx: {}", i), |b| b.iter(|| solver.a_closure_v2()));
        }
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
