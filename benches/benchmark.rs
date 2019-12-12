use criterion::{black_box, criterion_group, criterion_main, Criterion};
use krr::{QualitativeCalculus, Solver};
use std::fs;

fn setup_calculus() -> QualitativeCalculus {
    QualitativeCalculus::new(&fs::read_to_string("linear.txt").expect("Failed to read test file."))
}

fn setup_allen_calculus() -> QualitativeCalculus {
    QualitativeCalculus::new(&fs::read_to_string("allen.txt").expect("Failed to read test file."))
}

fn setup_easy_solvers(calculus: &QualitativeCalculus) -> Vec<Solver> {
    let input = fs::read_to_string("pc_test1.csp").expect("Failed to read test file.");
    let mut solvers = Vec::new();
    for pc in input.split(".\n\n") {
        println!("{}", pc);
        solvers.push(Solver::new(&calculus, pc));
    }
    solvers
}

fn setup_hard_solver1(calculus: &QualitativeCalculus) -> Solver {
    let input = fs::read_to_string("30x500_m_3_allen_eq1.csp").expect("Failed to read test file.");
    Solver::new(&calculus, &input)
}

// TODO: Compare different A-Closure impls
pub fn criterion_benchmark(c: &mut Criterion) {
    let linear_calculus = black_box(setup_calculus());
    {
        let easy_solvers = black_box(setup_easy_solvers(&linear_calculus));

        for (i, mut solver) in easy_solvers.into_iter().enumerate() {
            c.bench_function(&format!("easy {}", i), |b| b.iter(|| solver.a_closure_v2()));
        }
    }

    let allen_calculus = black_box(setup_allen_calculus());
    c.bench_function("hard 1", |b| {
        b.iter(|| {
            let mut hard_solver1 = black_box(setup_hard_solver1(&allen_calculus));
            hard_solver1.a_closure_v2()
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
