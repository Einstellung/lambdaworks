use iai::black_box;
use lambdaworks_stark::{
    air::{context::ProofOptions, example::cairo},
    prover::prove,
    verifier::verify,
};

mod functions;
mod util;

#[inline(never)]
fn simple_fibonacci_benchmarks() {
    let (trace, fibonacci_air) = functions::stark::generate_fib_proof_params(8);

    let proof = black_box(prove(
        black_box(&trace),
        black_box(&fibonacci_air),
        black_box(&mut ()),
    ));

    let ok = black_box(verify(
        black_box(&proof),
        black_box(&fibonacci_air),
        &mut (),
    ));

    assert!(ok);
}

#[inline(never)]
fn two_col_fibonacci_benchmarks() {
    let (trace, fibonacci_air) = functions::stark::generate_fib_2_cols_proof_params(16);

    let proof = black_box(prove(
        black_box(&trace),
        black_box(&fibonacci_air),
        black_box(&mut ()),
    ));

    let ok = black_box(verify(
        black_box(&proof),
        black_box(&fibonacci_air),
        black_box(&mut ()),
    ));

    assert!(ok);
}

iai::main!(simple_fibonacci_benchmarks, two_col_fibonacci_benchmarks,);
