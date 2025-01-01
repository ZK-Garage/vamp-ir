use criterion::{criterion_group, criterion_main, Criterion};

use halo2_proofs::pasta::{EqAffine, Fp};
use halo2_proofs::plonk::keygen_vk;
use halo2_proofs::poly::commitment::Params;

use std::collections::HashMap;
use std::fs;
use std::fs::File;
use std::io::Write;
use std::rc::Rc;

use vamp_ir::ast::Module;
use vamp_ir::halo2::synth::{keygen, prover, verifier, Halo2Module, PrimeFieldOps};
use vamp_ir::transform::compile;
use vamp_ir::util::{prompt_inputs, Config};

use std::time::Instant;

#[allow(dead_code)]
fn bench(pir_file: &str) {
    let mut file = File::create("benches/halo2_bench_timing.txt").unwrap();

    // COMPILATION
    println!("* Compiling constraints...");
    let inst2 = Instant::now();
    let unparsed_file = fs::read_to_string(pir_file).expect("cannot read file");
    let module = Module::parse(&unparsed_file).unwrap();
    let module_3ac = compile(
        module,
        &PrimeFieldOps::<Fp>::default(),
        &Config { quiet: false },
    ).expect("Failed to compile module"); // Added expect for error handling
    println!("* Compiling constraints (3AC)...");
    let inst3 = Instant::now();
    file.write_all(
        format!(
            "Compiling constraints time: {:?}\n",
            inst3.duration_since(inst2)
        )
        .as_bytes(),
    ).unwrap();

    println!("* Synthesizing arithmetic circuit...");
    let inst4 = Instant::now();
    let module_rc = Rc::new(module_3ac);
    let mut circuit = Halo2Module::<Fp>::new(module_rc);
    let params: Params<EqAffine> = Params::new(circuit.k);
    let inst5 = Instant::now();
    file.write_all(
        format!(
            "Synthesizing arithmetic circuit time: {:?}\n",
            inst5.duration_since(inst4)
        )
        .as_bytes(),
    ).unwrap();
    println!("* Constraint compilation success!");

    // PROOF GENERATION
    // Prover POV
    println!("* Soliciting circuit witnesses...");
    let inst6 = Instant::now();
    // Prompt for program inputs
    let var_assignments_ints = prompt_inputs(&circuit.module);
    let mut var_assignments = HashMap::new();
    for (k, v) in var_assignments_ints {
        var_assignments.insert(k, vamp_ir::halo2::synth::make_constant(v));
    }
    // Populate variable definitions
    circuit.populate_variables(var_assignments);
    let inst7 = Instant::now();
    file.write_all(
        format!(
            "Soliciting circuit witnesses time: {:?}\n",
            inst7.duration_since(inst6)
        )
        .as_bytes(),
    ).unwrap();

    // Generating proving key
    println!("* Generating proving key...");
    let inst8 = Instant::now();
    let (pk, _vk) = keygen(&circuit, &params).expect("Keygen failed in halo2 benchmark");
    let inst9 = Instant::now();
    file.write_all(
        format!(
            "Generating proving key time: {:?}\n",
            inst9.duration_since(inst8)
        )
        .as_bytes(),
    ).unwrap();

    // Start proving witnesses
    println!("* Proving knowledge of witnesses...");
    let inst10 = Instant::now();
    let proof = prover(circuit.clone(), &params, &pk).expect("prover failed in halo2 benchmark");
    let inst11 = Instant::now();
    file.write_all(
        format!(
            "Proving knowledge of witnesses time: {:?}\n",
            inst11.duration_since(inst10)
        )
        .as_bytes(),
    ).unwrap();

    // PROOF VERIFICATION
    println!("* Generating verifying key...");
    let inst12 = Instant::now();
    let vk = keygen_vk(&params, &circuit.clone()).expect("keygen_vk should not fail");
    let inst13 = Instant::now();
    file.write_all(
        format!(
            "Generating verifying key time: {:?}\n",
            inst13.duration_since(inst12)
        )
        .as_bytes(),
    ).unwrap();

    println!("* Verifying proof validity...");
    let inst14 = Instant::now();
    let verifier_result = verifier(&params, &vk, &proof);
    let inst15 = Instant::now();
    file.write_all(
        format!(
            "Verifying proof validity time: {:?}\n",
            inst15.duration_since(inst14)
        )
        .as_bytes(),
    ).unwrap();
    if let Ok(()) = verifier_result {
        println!("* Zero-knowledge proof, max_degree: u32 is valid");
    } else {
        println!("* Result from verifier: {:?}", verifier_result);
    }
}

#[allow(dead_code)]
fn criterion_benchmark(_c: &mut Criterion) {
    let source = "tests/blake2s.pir".to_string();
    //_c.bench_function("plonk_bench", |b| b.iter(|| bench(&source, max_degree)));
    bench(&source);
}

criterion_group!(benches, criterion_benchmark);

/*
criterion_group!{
    name = benches;
    // This can be any expression that returns a `Criterion` object.
    config = Criterion::default().significance_level(0.1).sample_size(10);
    targets = criterion_benchmark
}
 */

criterion_main!(benches);
