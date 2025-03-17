#![allow(non_snake_case)]


use std::ops::{Add, Mul};

use ark_bulletproofs::{r1cs::*, BulletproofGens, PedersenGens};
use ark_ec::{short_weierstrass::SWCurveConfig, AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field, PrimeField, UniformRand};
use ark_secq256k1::{Affine, Fr};
use ark_std::rand::seq::SliceRandom;
use ark_std::rand::thread_rng;
use ark_std::One;
use digest::crypto_common::{KeyInit, KeyIvInit};
use merlin::Transcript;
use rand_core::{CryptoRng, RngCore};

/// A proof-of-shuffle.
struct ShuffleProof(R1CSProof<Affine>);

impl ShuffleProof {
    fn gadget<CS: RandomizableConstraintSystem<Fr>>(
        cs: &mut CS,
        x: Vec<Variable<Fr>>,
        y: Vec<Variable<Fr>>,
    ) -> Result<(), R1CSError> {
        assert_eq!(x.len(), y.len());
        let k = x.len();

        if k == 1 {
            cs.constrain(y[0] - x[0]);
            return Ok(());
        }

        cs.specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"shuffle challenge");

            // Make last x multiplier for i = k-1 and k-2
            let (_, _, last_mulx_out) = cs.multiply(x[k - 1] - z, x[k - 2] - z);

            // Make multipliers for x from i == [0, k-3]
            let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
                let (_, _, o) = cs.multiply(prev_out.into(), x[i] - z);
                o
            });

            // Make last y multiplier for i = k-1 and k-2
            let (_, _, last_muly_out) = cs.multiply(y[k - 1] - z, y[k - 2] - z);

            // Make multipliers for y from i == [0, k-3]
            let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
                let (_, _, o) = cs.multiply(prev_out.into(), y[i] - z);
                o
            });

            // Constrain last x mul output and last y mul output to be equal
            cs.constrain(first_mulx_out - first_muly_out);

            Ok(())
        })
    }
}

impl ShuffleProof {
    /// Attempt to construct a proof that `output` is a permutation of `input`.
    ///
    /// Returns a tuple `(proof, input_commitments || output_commitments)`.
    pub fn prove<'a, 'b, R: CryptoRng + RngCore>(
        prng: &mut R,
        pc_gens: &'b PedersenGens<Affine>,
        bp_gens: &'b BulletproofGens<Affine>,
        transcript: &'a mut Transcript,
        input: &[Fr],
        output: &[Fr],
    ) -> Result<(ShuffleProof, Vec<Affine>, Vec<Affine>), R1CSError> {
        // Apply a domain separator with the shuffle parameters to the transcript
        // XXX should this be part of the gadget?
        let k = input.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_u64(b"k", k as u64);

        let mut prover = Prover::new(&pc_gens, transcript);

        let (input_commitments, input_vars): (Vec<_>, Vec<_>) = input
            .into_iter()
            .map(|v| prover.commit(*v, Fr::rand(prng)))
            .unzip();

        let (output_commitments, output_vars): (Vec<_>, Vec<_>) = output
            .into_iter()
            .map(|v| prover.commit(*v, Fr::rand(prng)))
            .unzip();

        ShuffleProof::gadget(&mut prover, input_vars, output_vars)?;

        let proof = prover.prove(prng, &bp_gens)?;

        Ok((ShuffleProof(proof), input_commitments, output_commitments))
    }
}

impl ShuffleProof {
    /// Attempt to verify a `ShuffleProof`.
    pub fn verify<'a, 'b>(
        &self,
        pc_gens: &'b PedersenGens<Affine>,
        bp_gens: &'b BulletproofGens<Affine>,
        transcript: &'a mut Transcript,
        input_commitments: &Vec<Affine>,
        output_commitments: &Vec<Affine>,
    ) -> Result<(), R1CSError> {
        // Apply a domain separator with the shuffle parameters to the transcript
        // XXX should this be part of the gadget?
        let k = input_commitments.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_u64(b"k", k as u64);

        let mut verifier = Verifier::new(transcript);

        let input_vars: Vec<_> = input_commitments
            .iter()
            .map(|V| verifier.commit(*V))
            .collect();

        let output_vars: Vec<_> = output_commitments
            .iter()
            .map(|V| verifier.commit(*V))
            .collect();

        ShuffleProof::gadget(&mut verifier, input_vars, output_vars)?;

        verifier.verify(&self.0, &pc_gens, &bp_gens)?;
        Ok(())
    }
}

fn kshuffle_helper(k: usize) {
    use rand::Rng;

    // Common code
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new((2 * k).next_power_of_two(), 1);

    let (proof, input_commitments, output_commitments) = {
        // Randomly generate inputs and outputs to kshuffle
        let mut rng = rand::thread_rng();
        let (min, max) = (0u64, u64::MAX);
        let input: Vec<Fr> = (0..k).map(|_| Fr::from(rng.gen_range(min..max))).collect();
        let mut output = input.clone();
        output.shuffle(&mut rand::thread_rng());

        let mut prover_transcript = Transcript::new(b"ShuffleProofTest");
        ShuffleProof::prove(
            &mut rng,
            &pc_gens,
            &bp_gens,
            &mut prover_transcript,
            &input,
            &output,
        )
        .unwrap()
    };

    {
        let mut verifier_transcript = Transcript::new(b"ShuffleProofTest");
        assert!(proof
            .verify(
                &pc_gens,
                &bp_gens,
                &mut verifier_transcript,
                &input_commitments,
                &output_commitments
            )
            .is_ok());
    }
}

#[test]
fn shuffle_gadget_test_1() {
    kshuffle_helper(1);
}

#[test]
fn shuffle_gadget_test_2() {
    kshuffle_helper(2);
}

#[test]
fn shuffle_gadget_test_3() {
    kshuffle_helper(3);
}

#[test]
fn shuffle_gadget_test_4() {
    kshuffle_helper(4);
}

#[test]
fn shuffle_gadget_test_5() {
    kshuffle_helper(5);
}

#[test]
fn shuffle_gadget_test_6() {
    kshuffle_helper(6);
}

#[test]
fn shuffle_gadget_test_7() {
    kshuffle_helper(7);
}

#[test]
fn shuffle_gadget_test_24() {
    kshuffle_helper(24);
}

#[test]
fn shuffle_gadget_test_42() {
    kshuffle_helper(42);
}

fn u64_from_scalar(x: Fr) -> u64 {
    let b = x.0.to_bytes_le();
    let u64_len = u64::BITS as usize / 8;
    if b[u64_len..].iter().any(|bi| *bi != 0) {
        panic!("Input is too large");
    }

    lakey_acc(&b[..u64_len], 1u64 << u8::BITS)
}

pub fn lakey_acc<
    U: Clone,
    V: Clone + Mul<Output = V>,
    T: From<U> + Add<Output = T> + Mul<V, Output = T> + Default + Clone,
>(
    x: &[U],
    base: V,
) -> T {
    let (head, tail) = (&x[0], &x[1..]);
    let init = T::from(head.clone());
    let mut a = base.clone();
    tail.iter().enumerate().fold(init, |acc, (i, xi)| {
        let acc = acc + T::from(xi.clone()) * a.clone();
        // Skip to prevent overflow.
        if i != tail.len() - 1 {
            a = a.clone() * base.clone();
        }
        acc
    })
}

fn bin_equality_gadget<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    x: &LinearCombination<Fr>,
    x_val: Option<Fr>,
) -> Result<Vec<Variable<Fr>>, R1CSError> {
    let x_bits: Vec<Variable<Fr>> = (0..Fr::MODULUS_BIT_SIZE as usize)
        .map(|i| {
            // Create low-level variables and add them to constraints
            let (a, b, o) = cs.allocate_multiplier(x_val.as_ref().map(|q| {
                let bit = q.0.get_bit(i) as i32;
                ((1 - bit).into(), bit.into())
            }))?;

            // Enforce a * b = 0, so one of (a,b) is zero
            cs.constrain(o.into());

            // Enforce that a = 1 - b, so they both are 1 or 0.
            cs.constrain(a + (b - Fr::from(1u64)));

            Ok(b)
        })
        .collect::<Result<_, R1CSError>>()?;

    // Enforce that x = Sum(b_i * 2^i, i = 0..n-1)
    let x_acc: LinearCombination<Fr> = lakey_acc(&x_bits, Fr::from(2u64));
    cs.constrain(x.clone() - x_acc);

    Ok(x_bits)
}

// sketch1: Q_a=[λ_a]P1 ∈ G1, Com((λ_a, r), (Q_b, H2)) = [λ_a]Q_b + [r]H2 ∈ G2, λ_ab=x([λ_a]Q_b), Com((λ_ab, t), (P1, H1)), Q_ab=[λ_ab]P2
// sketch2: Com((λ_a, r), (P1, H1)) ∈ G1, check if DL equal across Com, Q_a; Q_b, Q_ab ∈ G2: compute λ_ab=x([λ_a]Q_B) => check Q_ab==[λ_ab]P2
// we use https://eprint.iacr.org/2022/1593.pdf to prove that λ_a is equal across G1, G2 (generalization of Chaum-Pedersen proto (G1=G2))

// proof of x(Q_ab) = x([λ_a]Q_b), idea from https://eprint.iacr.org/2024/397.pdf
fn dh_gadget<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    λ_a: Option<Fr>,
    Q_b: ark_secp256k1::Affine,
    var_a: Variable<Fr>,
    var_ab: Variable<Fr>,
) -> Result<(), R1CSError> {

    let (w_a, w_b) = (Fr::from(0), Fr::from(7));
    let l = (Fr::MODULUS_BIT_SIZE-1) as i32;
    let Δ1: Vec<_> = (0..l).map(|i| if i == (l-1) {
        (ark_secp256k1::Config::GENERATOR*ark_secp256k1::Fr::from(-(l*l+3*l)/2)).into_affine()
    } else {
        (ark_secp256k1::Config::GENERATOR*ark_secp256k1::Fr::from(i+2)).into_affine()
    }).collect();
    let mut δ = vec![Q_b];
    for i in (1..l as usize) {
        δ.push(((*δ.last().unwrap())*ark_secp256k1::Fr::from(2)).into_affine());
    }
    let Δ2: Vec<_> = Δ1.iter().zip(δ.iter()).map(|(x, y)| (*x+y).into_affine()).collect();

    let k_vars = bin_equality_gadget(cs, &LinearCombination::from(var_a), λ_a)?;

    // P_0 = Δ_0
    let (_, _, x0) = cs.multiply(k_vars[0] * *δ[0].x().unwrap() + *Δ1[0].x().unwrap(), Variable::One().into()); // x0 = k[0]*(x-x')+x'
    let (_, _, y0) = cs.multiply(k_vars[0] * *δ[0].y().unwrap() + *Δ1[0].y().unwrap(), Variable::One().into()); // y0 = k[0]*(y-y')+y'
    let mut P  = λ_a.map(|v| vec![ (Q_b * ark_secp256k1::Fr::from(v.0.get_bit(0) as u64) + Δ1[0] ).into_affine() ] );
    let mut P_vars = vec![(x0, y0)];

    for i in 1..l as usize {
        // calculate witness P_i = P_i_1 + Δ_i
        let P_i = if let Some(λ_a) = λ_a {
            let P_i = (*(P.as_ref().unwrap().last().unwrap()) + match λ_a.0.get_bit(i) {
                true => Δ2[i],
                false => Δ1[i]
            }).into_affine();
            P.as_mut().unwrap().push( P_i );
            Some(P_i)
        } else { None };
        // calculate Delta
        let (Δ_i_x, Δ_i_y) = (k_vars[i] * *δ[i].x().unwrap() + *Δ1[i].x().unwrap(), k_vars[i] * *δ[i].y().unwrap() + *Δ1[i].y().unwrap() );
        
        let (_, x_P, x_P2) = cs.allocate_multiplier(P_i.map(|P_i| (*P_i.x().unwrap(), *P_i.x().unwrap())))?;
        let (_, y_P, y_P2) = cs.allocate_multiplier(P_i.map(|P_i| (*P_i.y().unwrap(), *P_i.y().unwrap())))?;
        let (_, _, x_P3) = cs.multiply(x_P2.into(), x_P.into());
        let (P_i_1_x, P_i_1_y) = *P_vars.last().unwrap();
        P_vars.push((x_P, y_P));
        
        // check curve equation for current points
        let curve_eq = y_P2 - x_P3 - x_P*w_a - w_b;
        cs.constrain(curve_eq);

        // check that Δ_i, -P_i, P_i_1 is on the same line
        let (_, _, t1) = cs.multiply(P_i_1_y + y_P, Δ_i_x - x_P);
        let (_, _, t2) = cs.multiply(Δ_i_y + y_P, P_i_1_x - x_P);
        cs.constrain(t1-t2);
    }

    // final check of x coordinate
    cs.constrain(var_ab - P_vars.last().unwrap().0 );
    Ok(())
}

fn dh_gadget_proof(
    pc_gens: &PedersenGens<Affine>,
    bp_gens: &BulletproofGens<Affine>,
    Q_b: ark_secp256k1::Affine,

    λ_a: Fr,
    λ_ab: Fr,
) -> Result<(R1CSProof<Affine>, (Affine, Affine)), R1CSError> {
    let mut blinding_rng = rand::thread_rng();

    let mut transcript = Transcript::new(b"ARTGadget");

    // 1. Create a prover
    let mut prover = Prover::new(pc_gens, &mut transcript);

    // 2. Commit high-level variables
    let (a_commitment, var_a) = prover.commit(λ_a, Fr::rand(&mut blinding_rng));
    let (ab_commitment, var_ab) = prover.commit(λ_ab, Fr::rand(&mut blinding_rng));

    dh_gadget(&mut prover, Some(λ_a), Q_b, var_a, var_ab)?;
    let circuit_len = prover.multipliers_len();
    let proof = prover.prove(&mut blinding_rng, bp_gens)?;
    println!("{:?} {:?}", circuit_len, proof);

    Ok((proof, (a_commitment, ab_commitment)))
}

fn dh_gadget_verify(
    pc_gens: &PedersenGens<Affine>,
    bp_gens: &BulletproofGens<Affine>,
    proof: R1CSProof<Affine>,
    Q_b: ark_secp256k1::Affine,

    a_commitment: Affine,
    ab_commitment: Affine,
) -> Result<(), R1CSError> {
    let mut transcript = Transcript::new(b"ARTGadget");
    let mut verifier = Verifier::new(&mut transcript);
    let var_a = verifier.commit(a_commitment);
    let var_ab = verifier.commit(ab_commitment);

    dh_gadget(&mut verifier, None, Q_b, var_a, var_ab)?;

    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .map_err(|_| R1CSError::VerificationError)
}

fn dh_gadget_roundtrip() -> Result<(), R1CSError> {
    let mut blinding_rng = rand::thread_rng();
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);
    let Q_b = ark_secp256k1::Affine::rand(&mut blinding_rng);
    let λ_a = -42;

    let R = (Q_b * ark_secp256k1::Fr::from(λ_a)).into_affine();
    
    let (proof, (var_a, var_b)) = dh_gadget_proof(&pc_gens, &bp_gens, Q_b, Fr::from(λ_a), Fr::from(R.x().unwrap().0))?;

    dh_gadget_verify(&pc_gens, &bp_gens, proof, Q_b, var_a, var_b)
}

#[test]
fn dh_gadget_roundtrip_test() {
    assert!(dh_gadget_roundtrip().is_ok());

}

/// Constrains (a1 + a2) * (b1 + b2) = (c1 + c2)
fn example_gadget<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    a1: LinearCombination<Fr>,
    a2: LinearCombination<Fr>,
    b1: LinearCombination<Fr>,
    b2: LinearCombination<Fr>,
    c1: LinearCombination<Fr>,
    c2: LinearCombination<Fr>,
) {
    let (_, _, c_var) = cs.multiply(a1 + a2, b1 + b2);
    cs.constrain(c1 + c2 - c_var);
}

// Prover's scope
fn example_gadget_proof(
    pc_gens: &PedersenGens<Affine>,
    bp_gens: &BulletproofGens<Affine>,
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> Result<(R1CSProof<Affine>, Vec<Affine>), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSExampleGadget");
    let mut rng = thread_rng();

    // 1. Create a prover
    let mut prover = Prover::new(pc_gens, &mut transcript);

    // 2. Commit high-level variables
    let (commitments, vars): (Vec<_>, Vec<_>) = [a1, a2, b1, b2, c1]
        .iter()
        .map(|x| prover.commit(Fr::from(*x), Fr::rand(&mut thread_rng())))
        .unzip();

    // 3. Build a CS
    example_gadget(
        &mut prover,
        vars[0].into(),
        vars[1].into(),
        vars[2].into(),
        vars[3].into(),
        vars[4].into(),
        Fr::from(c2).into(),
    );

    // 4. Make a proof
    let proof = prover.prove(&mut rng, bp_gens)?;

    Ok((proof, commitments))
}

// Verifier logic
fn example_gadget_verify(
    pc_gens: &PedersenGens<Affine>,
    bp_gens: &BulletproofGens<Affine>,
    c2: u64,
    proof: R1CSProof<Affine>,
    commitments: Vec<Affine>,
) -> Result<(), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    // 1. Create a verifier
    let mut verifier = Verifier::new(&mut transcript);

    // 2. Commit high-level variables
    let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();

    // 3. Build a CS
    example_gadget(
        &mut verifier,
        vars[0].into(),
        vars[1].into(),
        vars[2].into(),
        vars[3].into(),
        vars[4].into(),
        Fr::from(c2).into(),
    );

    // 4. Verify the proof
    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .map_err(|_| R1CSError::VerificationError)
}

fn example_gadget_roundtrip_helper(
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(4096, 1);

    let (proof, commitments) = example_gadget_proof(&pc_gens, &bp_gens, a1, a2, b1, b2, c1, c2)?;

    example_gadget_verify(&pc_gens, &bp_gens, c2, proof, commitments)
}

fn example_gadget_roundtrip_serialization_helper(
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let (proof, commitments) = example_gadget_proof(&pc_gens, &bp_gens, a1, a2, b1, b2, c1, c2)?;

    let proof = proof.to_bytes()?;

    let proof = R1CSProof::from_bytes(&proof)?;

    example_gadget_verify(&pc_gens, &bp_gens, c2, proof, commitments)
}

#[test]
fn example_gadget_test() {
    // (3 + 4) * (6 + 1) = (40 + 9)
    assert!(example_gadget_roundtrip_helper(3, 4, 6, 1, 40, 9).is_ok());
    // (3 + 4) * (6 + 1) != (40 + 10)
    assert!(example_gadget_roundtrip_helper(3, 4, 6, 1, 40, 10).is_err());
}

#[test]
fn example_gadget_serialization_test() {
    // (3 + 4) * (6 + 1) = (40 + 9)
    assert!(example_gadget_roundtrip_serialization_helper(3, 4, 6, 1, 40, 9).is_ok());
    // (3 + 4) * (6 + 1) != (40 + 10)
    assert!(example_gadget_roundtrip_serialization_helper(3, 4, 6, 1, 40, 10).is_err());
}

// Range Proof gadget

/// Enforces that the quantity of v is in the range [0, 2^n).
pub fn range_proof<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    mut v: LinearCombination<Fr>,
    v_assignment: Option<u64>,
    n: usize,
) -> Result<(), R1CSError> {
    let mut exp_2 = Fr::one();
    for i in 0..n {
        // Create low-level variables and add them to constraints
        let (a, b, o) = cs.allocate_multiplier(v_assignment.map(|q| {
            let bit: u64 = (q >> i) & 1;
            ((1 - bit).into(), bit.into())
        }))?;

        // Enforce a * b = 0, so one of (a,b) is zero
        cs.constrain(o.into());

        // Enforce that a = 1 - b, so they both are 1 or 0.
        cs.constrain(a + b - LinearCombination::from(Fr::one()));

        // Add `-b_i*2^i` to the linear combination
        // in order to form the following constraint by the end of the loop:
        // v = Sum(b_i * 2^i, i = 0..n-1)
        v = v - b * exp_2;

        exp_2 = exp_2 + exp_2;
    }

    // Enforce that v = Sum(b_i * 2^i, i = 0..n-1)
    cs.constrain(v);

    Ok(())
}

#[test]
fn range_proof_gadget() {
    use rand::thread_rng;
    use rand::Rng;

    let mut rng = thread_rng();
    let m = 3; // number of values to test per `n`

    for n in [2, 10, 32, 63].iter() {
        let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
        let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min..max)).collect();
        for v in values {
            assert!(range_proof_helper(v.into(), *n).is_ok());
        }
        assert!(range_proof_helper((max + 1).into(), *n).is_err());
    }
}

fn range_proof_helper(v_val: u64, n: usize) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::<Affine>::default();
    let bp_gens = BulletproofGens::new(128, 1);

    // Prover's scope
    let (proof, commitment) = {
        // Prover makes a `ConstraintSystem` instance representing a range proof gadget
        let mut prover_transcript = Transcript::new(b"RangeProofTest");
        let mut rng = rand::thread_rng();

        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let (com, var) = prover.commit(v_val.into(), Fr::rand(&mut rng));
        assert!(range_proof(&mut prover, var.into(), Some(v_val), n).is_ok());

        let proof = prover.prove(&mut rng, &bp_gens)?;

        (proof, com)
    };

    // Verifier makes a `ConstraintSystem` instance representing a merge gadget
    let mut verifier_transcript = Transcript::new(b"RangeProofTest");
    let mut verifier = Verifier::new(&mut verifier_transcript);

    let var = verifier.commit(commitment);

    // Verifier adds constraints to the constraint system
    assert!(range_proof(&mut verifier, var.into(), None, n).is_ok());

    // Verifier verifies proof
    verifier.verify(&proof, &pc_gens, &bp_gens)
}

#[test]
fn batch_range_proof_gadget() {
    let values = [(0u64, 16usize)];
    assert!(batch_range_proof_helper(&values).is_ok());

    let values = [(0u64, 16usize), (3, 16), ((1 << 16) - 1, 16), (1 << 16, 32)];
    assert!(batch_range_proof_helper(&values).is_ok());

    let values = [(0u64, 16usize), (3, 16), (1 << 16, 16), (1 << 16, 32)];
    assert!(batch_range_proof_helper(&values).is_err());

    let values = [
        (0u64, 16usize),
        (3, 16),
        ((1 << 16) - 1, 16),
        (1 << 16, 32),
        (1 << 63, 64),
    ];
    assert!(batch_range_proof_helper(&values).is_ok());

    let values = [
        (0u64, 16usize),
        (3, 16),
        ((1 << 16) - 1, 16),
        (1u64 << 32, 32),
        (1 << 63, 64),
    ];
    assert!(batch_range_proof_helper(&values).is_err());
}

fn batch_range_proof_helper(v_vals: &[(u64, usize)]) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::<Affine>::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let mut proofs = vec![];
    let mut commitments = vec![];

    let mut range_bound = vec![];
    for (v, n) in v_vals {
        // Prover's scope
        let (proof, commitment) = {
            // Prover makes a `ConstraintSystem` instance representing a range proof gadget
            let mut prover_transcript = Transcript::new(b"RangeProofTest");
            let mut rng = rand::thread_rng();

            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

            let (com, var) = prover.commit(Fr::from(*v), Fr::rand(&mut rng));
            assert!(range_proof(&mut prover, var.into(), Some(*v), *n).is_ok());

            let proof = prover.prove(&mut rng, &bp_gens)?;
            (proof, com)
        };
        range_bound.push(*n);
        proofs.push(proof);
        commitments.push(commitment);
    }

    let mut verifier_transcripts = vec![Transcript::new(b"RangeProofTest"); commitments.len()];
    let mut verifiers = vec![];
    let mut prng = thread_rng();
    for ((commitment, transcript), n) in commitments
        .iter()
        .zip(verifier_transcripts.iter_mut())
        .zip(range_bound)
    {
        let mut verifier = Verifier::new(transcript);

        // Verifier makes a `ConstraintSystem` instance representing a merge gadget
        let var = verifier.commit(*commitment);

        // Verifier adds constraints to the constraint system
        assert!(range_proof(&mut verifier, var.into(), None, n).is_ok());

        verifiers.push(verifier);
    }

    let a = verifiers.into_iter().zip(proofs.iter());
    batch_verify(&mut prng, a, &pc_gens, &bp_gens)
}
