use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{create_test_fri_params, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::get_symbolic_constraints;

use rand::rngs::SmallRng;
use rand::SeedableRng;
use runwai_p3::air::{CleanAirInstance, RunwaiAir};
use runwai_p3::ast::Expr;
use runwai_p3::config::StarkConfig;
use runwai_p3::key::AirInfo;
use runwai_p3::lookup::ByteRangeAir;
use runwai_p3::permutation::generate_multiplicity_traces;
use runwai_p3::prover::prove;
use runwai_p3::verify::verify;

pub fn generate_fibonacci_trace<F: Field>(num_steps: usize) -> RowMajorMatrix<F> {
    let mut values = Vec::with_capacity(num_steps * 1);
    let mut a = F::ZERO;
    values.push(a);
    for _ in 1..num_steps {
        a += F::ONE;
        values.push(a);
    }
    RowMajorMatrix::new(values, 1)
}

fn main() {
    // ##################################### Setting #####################################################
    type Val = BabyBear;
    type Perm = Poseidon2BabyBear<16>;
    type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
    type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
    type ValMmcs =
        MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 8>;
    type Challenge = BinomialExtensionField<Val, 4>;
    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
    type Dft = Radix2DitParallel<Val>;
    type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
    type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let config = create_test_fri_params(challenge_mmcs, 2);
    let pcs = Pcs::new(dft, val_mmcs, config);

    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    // ##################################### Load AIR #####################################################
    let expr = Expr::from_json_file("examples/clk.json").unwrap();
    let main_air = RunwaiAir::<Val>::new(expr, 1);
    let main_air_width = main_air.width + 1;
    let symbolic_constraints = get_symbolic_constraints(&main_air, 0, 0);
    for sc in &symbolic_constraints {
        println!("{:?}", sc);
    }
    let air_instance = CleanAirInstance::Main(main_air);

    // Create a single VK with multiple AirInfo instances
    //let byte_range_air = ByteRangeAir::new();
    //let byte_range_air_instance = CleanAirInstance::ByteRange(byte_range_air);

    // Create VK with multiple air instances (main + lookup)
    let air_instances = vec![
        (air_instance, main_air_width),
        //(byte_range_air_instance, 1), // ByteRange has width 1
    ];

    let air_infos: Vec<AirInfo<BabyBear>> = air_instances
        .into_iter()
        .map(|(air, trace_width)| AirInfo::new(air, trace_width))
        .collect();

    // ##################################### Execute the Program ##########################################
    let num_steps = 512; // Choose the number of Fibonacci steps
    let main_trace = generate_fibonacci_trace::<Val>(num_steps);

    // Generate lookup traces using the AirInfo instances from the VK
    let lookup_traces = generate_multiplicity_traces::<BabyBear, MyConfig>(&air_infos, &main_trace);
    // Collect all traces: main trace + lookup traces
    let mut traces = vec![main_trace.clone()];
    traces.extend(lookup_traces);
    println!("{:?}", air_infos.len());
    println!("{:?}", traces.len());

    let pis = vec![];
    let proof = prove(&config, &air_infos, &traces, &pis);
    verify(&config, &air_infos, &proof, &pis).expect("verification failed");

    println!("Success");

    /*
    type Val = Mersenne31; // TODO: Change to KoalaBear
    type Challenge = BinomialExtensionField<Val, 3>;

    type ByteHash = Keccak256Hash;
    type FieldHash = SerializingHasher<ByteHash>;
    let byte_hash = ByteHash {};
    let field_hash = FieldHash::new(Keccak256Hash {});

    type MyCompress = CompressionFunctionFromHasher<ByteHash, 2, 32>;
    let compress = MyCompress::new(byte_hash);

    type ValMmcs = MerkleTreeMmcs<Val, u8, FieldHash, MyCompress, 32>;
    let val_mmcs = ValMmcs::new(field_hash, compress);

    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());

    type Challenger = SerializingChallenger32<Val, HashChallenger<u8, ByteHash, 32>>;

    let fri_params = FriParameters {
        log_blowup: 1,
        num_queries: 100,
        proof_of_work_bits: 16,
        mmcs: challenge_mmcs,
        log_final_poly_len: 1,
    };

    type Pcs = CirclePcs<Val, ValMmcs, ChallengeMmcs>;
    let pcs = Pcs {
        mmcs: val_mmcs,
        fri_params,
        _phantom: std::marker::PhantomData,
    };

    type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;
    let challenger = Challenger::from_hasher(vec![], byte_hash);
    let config = MyConfig::new(pcs, challenger);

    let expr = Expr::from_json_file("examples/clk.json").unwrap();
    let air = RunwaiAir::<Val>::new(expr, 1);
    let symbolic_constraints = get_symbolic_constraints(&air, 0, 0);
    for sc in &symbolic_constraints {
        println!("{:?}", sc);
    }

    let num_steps = 8; // Choose the number of Fibonacci steps
    let trace = generate_fibonacci_trace::<Val>(num_steps);
    //let proof = prove(&config, &air, trace, &vec![]);

    //let result = verify(&config, &air, &proof, &vec![]);

    //if result.is_ok() {
    //    println!("verification successes");
    //}
    */
}
