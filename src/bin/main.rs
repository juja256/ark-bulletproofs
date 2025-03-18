#![allow(non_snake_case)]
use std::ops::{Add, Mul};

use ark_bulletproofs::{r1cs::*, BulletproofGens, PedersenGens};
use ark_ec::{short_weierstrass::SWCurveConfig, AffineRepr, CurveGroup};
use ark_ff::{BigInt, BigInteger, Field, PrimeField, UniformRand};

use ark_secp256k1 as G1; // for R1CS bp proving
use ark_secq256k1 as G2; // used in R1CS statements

use ark_std::rand::seq::SliceRandom;
use ark_std::rand::thread_rng;
use ark_std::One;
use digest::crypto_common::{KeyInit, KeyIvInit};
use merlin::Transcript;
use rand_core::{CryptoRng, RngCore};
use tracing::{debug, info, instrument};

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

fn bin_equality_gadget<CS: ConstraintSystem<G1::Fr>>(
    cs: &mut CS,
    x: &LinearCombination<G1::Fr>,
    x_val: Option<G1::Fr>,
) -> Result<Vec<Variable<G1::Fr>>, R1CSError> {
    let bint = x_val.map(|x| x.into_bigint());
    
    let x_bits: Vec<Variable<G1::Fr>> = (0..G1::Fr::MODULUS_BIT_SIZE as usize)
        .map(|i| {
            // Create low-level variables and add them to constraints
            let (a, b, o) = cs.allocate_multiplier(bint.map(|bint| {
                let bit = bint.get_bit(i) as i32;
                ((1 - bit).into(), bit.into())
            }))?;

            // Enforce a * b = 0, so one of (a,b) is zero
            cs.constrain(o.into());

            // Enforce that a = 1 - b, so they both are 1 or 0.
            cs.constrain(a + (b - G1::Fr::from(1u64)));

            Ok(b)
        })
        .collect::<Result<_, R1CSError>>()?;

    // Enforce that x = Sum(b_i * 2^i, i = 0..n-1)
    let x_acc: LinearCombination<G1::Fr> = lakey_acc(&x_bits, G1::Fr::from(2u64));
    cs.constrain(x.clone() - x_acc);

    Ok(x_bits)
}

// sketch1: Q_a=[λ_a]P1 ∈ G1, Com((λ_a, r), (Q_b, H2)) = [λ_a]Q_b + [r]H2 ∈ G2, λ_ab=x([λ_a]Q_b), Com((λ_ab, t), (P1, H1)), Q_ab=[λ_ab]P2
// sketch2: Com((λ_a, r), (P1, H1)) ∈ G1, check if DL equal across Com, Q_a; Q_b, Q_ab ∈ G2: compute λ_ab=x([λ_a]Q_B) => check Q_ab==[λ_ab]P2
// we use https://eprint.iacr.org/2022/1593.pdf to prove that λ_a is equal across G1, G2 (generalization of Chaum-Pedersen proto (G1=G2))

// proof of x(Q_ab) = x([λ_a]Q_b), idea from https://eprint.iacr.org/2024/397.pdf
fn dh_gadget<CS: ConstraintSystem<G1::Fr>>(
    cs: &mut CS,
    λ_a: Option<G1::Fr>,
    Q_b: G2::Affine,
    var_a: Variable<G1::Fr>,
    var_ab: Variable<G1::Fr>,
) -> Result<(), R1CSError> {
    let (w_a, w_b) = (G1::Fr::from(0), G1::Fr::from(7));
    let l = (G1::Fr::MODULUS_BIT_SIZE) as i32;
    let Δ1: Vec<_> = (0..l).map(|i| if i == (l-1) {
        (G2::Config::GENERATOR*G2::Fr::from(-(l*l + l - 2)/2)).into_affine()
    } else {
        (G2::Config::GENERATOR*G2::Fr::from(i+2)).into_affine()
    }).collect();

    let mut δ = vec![Q_b];
    for _ in 1..l as usize {
        δ.push(((*δ.last().unwrap())*G2::Fr::from(2)).into_affine());
    }
    let Δ2: Vec<_> = Δ1.iter().zip(δ.iter()).map(|(x, y)| (*x+y).into_affine()).collect();
    let k_vars = bin_equality_gadget(cs, &LinearCombination::from(var_a), λ_a)?;
    let λ_a = λ_a.map(|x| x.into_bigint());
    
    // P_0 = Δ_0
    let (_, _, x0) = cs.multiply( Variable::One() * *Δ1[0].x().unwrap() + k_vars[0] * (*Δ2[0].x().unwrap() - *Δ1[0].x().unwrap()), Variable::One().into()); // x0 = k[0]*(x-x')+x'
    let (_, _, y0) = cs.multiply(Variable::One() * *Δ1[0].y().unwrap() + k_vars[0] * (*Δ2[0].y().unwrap() - *Δ1[0].y().unwrap()), Variable::One().into()); // y0 = k[0]*(y-y')+y'
    let mut P  = λ_a.map(|λ_a| vec![ (Q_b * G2::Fr::from(λ_a.get_bit(0) as u64) + Δ1[0] ).into_affine() ] );
    let mut P_vars = vec![(x0, y0)];
    
    for i in 1..l as usize {
        // calculate witness P_i = P_i_1 + Δ_i
        let P_i = if let Some(λ_a) = λ_a {
            let P_i = (*(P.as_ref().unwrap().last().unwrap()) + match λ_a.get_bit(i) {
                true => Δ2[i],
                false => Δ1[i]
            }).into_affine();
            P.as_mut().unwrap().push( P_i );
            Some(P_i)
        } else { None };

        let (Δ_i_x, Δ_i_y) = (
            Variable::One() * *Δ1[i].x().unwrap() + k_vars[i] * (*Δ2[i].x().unwrap() - *Δ1[i].x().unwrap()), 
            Variable::One() * *Δ1[i].y().unwrap() + k_vars[i] * (*Δ2[i].y().unwrap() - *Δ1[i].y().unwrap())
        );

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
    info!("P_final = {:?}", P.as_ref().map(|P| P.iter().last().clone() ));
    // final check of x coordinate
    cs.constrain(var_ab - P_vars.last().unwrap().0 );
    
    Ok(())
}

#[instrument(skip(pc_gens, bp_gens, Q_b, λ_a, λ_ab))]
fn dh_gadget_proof(
    pc_gens: &PedersenGens<G1::Affine>,
    bp_gens: &BulletproofGens<G1::Affine>,
    Q_b: G2::Affine,

    λ_a: G1::Fr,
    λ_ab: G1::Fr,
) -> Result<(R1CSProof<G1::Affine>, (G1::Affine, G1::Affine)), R1CSError> {
    let mut blinding_rng = rand::thread_rng();

    let mut transcript = Transcript::new(b"ARTGadget");

    // 1. Create a prover
    let mut prover = Prover::new(pc_gens, &mut transcript);

    // 2. Commit high-level variables
    let (a_commitment, var_a) = prover.commit(λ_a, G1::Fr::rand(&mut blinding_rng));
    let (ab_commitment, var_ab) = prover.commit(λ_ab, G1::Fr::rand(&mut blinding_rng));

    dh_gadget(&mut prover, Some(λ_a), Q_b, var_a, var_ab)?;
    let circuit_len = prover.multipliers_len();

    let proof = prover.prove(&mut blinding_rng, bp_gens)?;
    info!("ARTGadget proved: circuit_size = {:?}, proof_size = {:?}", circuit_len, proof.to_bytes()?.len() );

    Ok((proof, (a_commitment, ab_commitment)))
}

#[instrument(skip(pc_gens, bp_gens, proof, a_commitment, ab_commitment))]
fn dh_gadget_verify(
    pc_gens: &PedersenGens<G1::Affine>,
    bp_gens: &BulletproofGens<G1::Affine>,
    proof: R1CSProof<G1::Affine>,
    Q_b: G2::Affine,

    a_commitment: G1::Affine,
    ab_commitment: G1::Affine,
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
    let bp_gens = BulletproofGens::new(2048, 1);
    let Q_b = G2::Affine::rand(&mut blinding_rng);
    
    let λ_a = BigInt::new([(1u64<<62) + 5, 1, 1, (1u64<<62) + 5]);
    
    let R = (Q_b * G2::Fr::from(λ_a)).into_affine();
    info!("R_real={:?}", R);
    
    let (proof, (var_a, var_b)) = dh_gadget_proof(&pc_gens, &bp_gens, Q_b, G1::Fr::from(λ_a), G1::Fr::from(*R.x().unwrap()))?;

    dh_gadget_verify(&pc_gens, &bp_gens, proof, Q_b, var_a, var_b)
}

fn main() {
    // Використовуємо змінну середовища MY_LOG_LEVEL замість RUST_LOG
    let log_level = std::env::var("PROOF_LOG").unwrap_or_else(|_| "info".to_string());

    tracing_subscriber::fmt()
         // Встановлюємо рівень логування з змінної середовища
         .with_env_filter(log_level)
         // Додаємо вивід часу (опціонально)
         .with_target(false)
         .init();

    dh_gadget_roundtrip().unwrap();
}