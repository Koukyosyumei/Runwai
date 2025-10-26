use std::fmt::Debug;

use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_circle::CirclePcs;
use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_field::Field;
use p3_fri::FriParameters;
use p3_keccak::Keccak256Hash;
use p3_koala_bear::KoalaBear;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_mersenne_31::Mersenne31;
use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher};
use p3_uni_stark::{get_symbolic_constraints, prove, verify, StarkConfig};

use runwai_p3::air::RunwaiAir;
use runwai_p3::ast::Expr;

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
    type Val = Mersenne31;
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
    let proof = prove(&config, &air, trace, &vec![]);

    let result = verify(&config, &air, &proof, &vec![]);

    if result.is_ok() {
        println!("verification successes");
    }
}
