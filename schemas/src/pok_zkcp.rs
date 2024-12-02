use crate::hard_relation::HardRelation;
use crate::nizk::NIZK;
use crate::utils::{point_to_byte_vector, proj, scalar_to_byte_vector, bit_at};
use digest::{Digest, KeyInit};
use elliptic_curve::ops::Reduce;
use elliptic_curve::point::AffineCoordinates;
use elliptic_curve::scalar::NonZeroScalar;
use elliptic_curve::FieldBytes;
use elliptic_curve::{CurveArithmetic, Group};
use rand_core::OsRng;
use std::marker::PhantomData;
use std::vec;
use elliptic_curve::ff::Field;

pub struct PoKZKCP<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    _curve_marker: PhantomData<C>,
    _hash_marker: PhantomData<H>,
}

pub struct Witness<C>
where
    C: CurveArithmetic,
{
    pub sig: C::Scalar,
    pub sk: C::Scalar,
    pub w: C::Scalar,
    pub elgamal_randomness: Vec<C::Scalar>,
    pub sig_bytes: Vec<u8>
}

pub struct Statement<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    pub vk: C::ProjectivePoint,
    pub sig_hash: C::Scalar,
    pub gs: C::ProjectivePoint,
    pub x: C::ProjectivePoint,
    pub elgamal_a: Vec<C::ProjectivePoint>,
    pub elgamal_b: Vec<C::ProjectivePoint>,
    pub msg: String,
    _hash_marker: PhantomData<H>,
}

impl<C, H> Statement<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    pub fn new(
        vk: C::ProjectivePoint,
        sig_hash: C::Scalar,
        gs: C::ProjectivePoint,
        x: C::ProjectivePoint,
        elgamal_a: Vec<C::ProjectivePoint>,
        elgamal_b: Vec<C::ProjectivePoint>,
        msg: String) -> Self {
        Statement::<C,H> {
            vk, sig_hash, gs, x, elgamal_a, elgamal_b, msg,
            _hash_marker: PhantomData,
        }
    }

    pub fn to_byte_vector(&self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        v.append(&mut point_to_byte_vector::<C>(&self.vk));
        v.append(&mut scalar_to_byte_vector::<C>(&self.sig_hash));
        v.append(&mut point_to_byte_vector::<C>(&self.gs));
        v.append(&mut point_to_byte_vector::<C>(&self.x));
        for i in 0..self.elgamal_a.len() {
            v.append(&mut point_to_byte_vector::<C>(&self.elgamal_a[i]));
            v.append(&mut point_to_byte_vector::<C>(&self.elgamal_b[i]));
        }
        let clone_msg = self.msg.clone();
        v.append(&mut clone_msg.into_bytes());

        v
    }
}

impl<C, H> HardRelation<Statement<C, H>, Witness<C>> for Witness<C>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    type PP = C::ProjectivePoint;

    fn R(pp: &Self::PP, w: &Witness<C>, x: &Statement<C, H>) -> bool {
        let g = *pp;
        let rv = x.gs + ((-x.vk) * x.sig_hash);
        let proj_pk = proj::<C>(&x.vk);
        let proj_rv = proj::<C>(&rv);
        let hasher = H::new();
        let ev = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(&proj_pk)
                .chain_update(&proj_rv)
                .chain_update(x.msg.as_str())
                .finalize(),
        );

        let mut exp = C::Scalar::ONE;
        let mut total = C::Scalar::ZERO;
        let mut total_a = C::ProjectivePoint::identity();
        let mut total_b = C::ProjectivePoint::identity();
        for i in 0..x.elgamal_a.len() {
            let bit = if bit_at(&w.sig_bytes, i) == 0 {
                C::Scalar::ZERO
            } else {
                C::Scalar::ONE
            };
            if !(x.elgamal_a[i] == g*w.elgamal_randomness[i]
                 && x.elgamal_b[i] == x.x*w.elgamal_randomness[i]+g*bit) {
                return false;
            }
            total = total + w.elgamal_randomness[i] * exp;
            total_a = total_a + x.elgamal_a[i];
            total_b = total_b + x.elgamal_b[i];
            exp = exp.double();
        }

        x.x == g * w.w 
            && x.gs == g * w.sig 
            && ev == x.sig_hash
            && total_a == g*total
            && total_b == x.x*total + x.gs
    }
    // From a Witness w, compute a Statement s such that R(w, s) == true
    fn statement(pp: &Self::PP, w: &Witness<C>) -> Statement<C, H> {
        unimplemented!("This function should never be called!");
    }

    fn gen(pp: &Self::PP) -> (Witness<C>, Statement<C, H>) {
        unimplemented!("This function should never be called!");
    }
}

pub struct ProofCommitments<C>
where
    C: CurveArithmetic,
{
    rel_as: C::ProjectivePoint,
    sig_keys: C::ProjectivePoint,
    sig: C::ProjectivePoint,
    a_bits: Vec<C::ProjectivePoint>,
    b1_bits: Vec<C::ProjectivePoint>,
    b2_bits: Vec<C::ProjectivePoint>,
    a_total: C::ProjectivePoint,
    b_total: C::ProjectivePoint
}

impl<C> ProofCommitments<C>
where
    C: CurveArithmetic
{
    fn to_byte_vector(&self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        v.append(&mut point_to_byte_vector::<C>(&self.rel_as));
        v.append(&mut point_to_byte_vector::<C>(&self.sig_keys));
        v.append(&mut point_to_byte_vector::<C>(&self.sig));
        v.append(&mut point_to_byte_vector::<C>(&self.a_total));
        v.append(&mut point_to_byte_vector::<C>(&self.b_total));
        for i in 0..self.a_bits.len() {
            v.append(&mut point_to_byte_vector::<C>(&self.a_bits[i]));
            v.append(&mut point_to_byte_vector::<C>(&self.b1_bits[i]));
            v.append(&mut point_to_byte_vector::<C>(&self.b2_bits[i]));
        };

        v
    }
}


pub struct ProofResponses<C>
where
    C: CurveArithmetic,
{
    rel_as: C::Scalar,
    sig_keys: C::Scalar,
    sig: C::Scalar,
    a_bits: Vec<C::Scalar>,
    b1_bits: Vec<C::Scalar>,
    b2_bits: Vec<C::Scalar>,
    total: C::Scalar
}

impl<C> ProofResponses<C>
where
    C: CurveArithmetic
{
    fn to_byte_vector(&self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        v.append(&mut scalar_to_byte_vector::<C>(&self.rel_as));
        v.append(&mut scalar_to_byte_vector::<C>(&self.sig_keys));
        v.append(&mut scalar_to_byte_vector::<C>(&self.sig));
        v.append(&mut scalar_to_byte_vector::<C>(&self.total));
        for i in 0..self.a_bits.len() {
            v.append(&mut scalar_to_byte_vector::<C>(&self.a_bits[i]));
            v.append(&mut scalar_to_byte_vector::<C>(&self.b1_bits[i]));
            v.append(&mut scalar_to_byte_vector::<C>(&self.b2_bits[i]));
        };

        v
    }
}

pub struct Proof<C>
where
    C: CurveArithmetic,
{
    commitments: ProofCommitments<C>,
    challenges: (Vec<C::Scalar>, Vec<C::Scalar>),
    responses: ProofResponses<C>
}

impl<C> Proof<C>
where
    C: CurveArithmetic,
{
    pub fn to_byte_vector(&self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        v.append(&mut self.commitments.to_byte_vector());
        v.append(&mut self.responses.to_byte_vector());

        for i in 0..self.challenges.1.len() {
            v.append(&mut scalar_to_byte_vector::<C>(&self.challenges.0[i]));
            v.append(&mut scalar_to_byte_vector::<C>(&self.challenges.1[i]));
        }

        v
    }
}

fn compute_challenge<C, H>(
    commitments: &ProofCommitments<C>,
    x: &Statement<C, H>,
) -> C::Scalar
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    let sig_hash = Into::<<C::AffinePoint as AffineCoordinates>::FieldRepr>::into(x.sig_hash);
    let mut hasher = H::new();
    hasher.update(proj::<C>(&commitments.rel_as));
    hasher.update(proj::<C>(&commitments.sig_keys));
    hasher.update(proj::<C>(&commitments.sig));
    hasher.update(proj::<C>(&commitments.a_total));
    hasher.update(proj::<C>(&commitments.b_total));
    hasher.update(proj::<C>(&x.vk));
    hasher.update(sig_hash);
    hasher.update(proj::<C>(&x.gs));
    hasher.update(proj::<C>(&x.x));
    hasher.update(x.msg.as_str());

    for i in 0..commitments.a_bits.len() {
        hasher.update(proj::<C>(&commitments.a_bits[i]));
        hasher.update(proj::<C>(&commitments.b1_bits[i]));
        hasher.update(proj::<C>(&commitments.b2_bits[i]));
        hasher.update(proj::<C>(&x.elgamal_a[i]));
        hasher.update(proj::<C>(&x.elgamal_b[i]));
    }
    let c = <C::Scalar as Reduce<C::Uint>>::reduce_bytes( &hasher.finalize() );

    c
}


impl<C, H> NIZK for PoKZKCP<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    type CRS = ();
    type Statement = Statement<C, H>;
    type Witness = Witness<C>;
    type Proof = Proof<C>;

    fn crs_gen() -> Self::CRS {
        ()
    }

    fn prove(crs: &Self::CRS, x: &Self::Statement, w: &Self::Witness) -> Self::Proof {
        let sig_bytes = &w.sig_bytes;
        let g = C::ProjectivePoint::generator();
        let ek = x.x;
        let ekg = x.x - g;
        let ct_b = &x.elgamal_b;
        let n_bits = sig_bytes.len()*8;

        let rel_as_randomness = NonZeroScalar::<C>::random(&mut OsRng);
        let rel_as_commitment = g*(*rel_as_randomness);
        let sig_keys_randomness = NonZeroScalar::<C>::random(&mut OsRng);
        let sig_keys_commitment = g*(*sig_keys_randomness);
        let sig_randomness = NonZeroScalar::<C>::random(&mut OsRng);
        let sig_commitment = g*(*sig_randomness);

        let mut randomness = Vec::<C::Scalar>::with_capacity(n_bits);
        let mut commitments_a = Vec::<C::ProjectivePoint>::with_capacity(n_bits);
        let mut commitments_b1 = Vec::<C::ProjectivePoint>::with_capacity(n_bits);
        let mut commitments_b2 = Vec::<C::ProjectivePoint>::with_capacity(n_bits);
        let mut cheats =Vec::<C::Scalar>::with_capacity(n_bits);
        let mut responses_a =Vec::<C::Scalar>::with_capacity(n_bits);
        let mut responses_b1 =Vec::<C::Scalar>::with_capacity(n_bits);
        let mut responses_b2 =Vec::<C::Scalar>::with_capacity(n_bits);
        let mut random_responses = Vec::<C::Scalar>::with_capacity(n_bits);

        let mut total_elgamal_exp = C::Scalar::ZERO;
        let mut exp_accumulator = C::Scalar::ONE;

        for i in 0..n_bits {
            let u = NonZeroScalar::<C>::random(&mut OsRng);
            randomness.push(*u);
            let cheat = NonZeroScalar::<C>::random(&mut OsRng);
            cheats.push(*cheat);
            let random_response = NonZeroScalar::<C>::random(&mut OsRng);
            random_responses.push(*random_response);

            commitments_a.push(g * (*u));
            if bit_at(&sig_bytes, i) == 0 { // i-th bit of the signature is 0
                commitments_b1.push(ek * (*u));
                //commitments_b2.push(x.elgamal_b[i] * (*random_response) - g + ct_b[i] * (- (*cheat)));
                commitments_b2.push(ek * *random_response + (x.elgamal_b[i] - g)*(- *cheat));
            } else { // i-th bit of the signature is 1
                commitments_b1.push(ek * (*random_response) + x.elgamal_b[i] * (- (*cheat)));
                commitments_b2.push(ek * (*u));
            }

            total_elgamal_exp = total_elgamal_exp + w.elgamal_randomness[i] * exp_accumulator;
            exp_accumulator = exp_accumulator.double();
        }

        let total_elgamal_randomness = NonZeroScalar::<C>::random(&mut OsRng);
        let total_elgamal_commitment_a = g*(*total_elgamal_randomness);
        let total_elgamal_commitment_b = ek*(*total_elgamal_randomness);

        let commitments = ProofCommitments::<C> {
            rel_as: rel_as_commitment,
            sig_keys: sig_keys_commitment,
            sig: sig_commitment,
            a_bits: commitments_a,
            b1_bits: commitments_b1,
            b2_bits: commitments_b2,
            a_total: total_elgamal_commitment_a,
            b_total: total_elgamal_commitment_b
        }; 

        let c = compute_challenge(&commitments, x);
        
        let rel_as_response = *rel_as_randomness + c * w.w;
        let sig_keys_response = *sig_keys_randomness + c * w.sk;
        let sig_response = *sig_randomness + c *w.sig;

        let mut challenges_c1 =Vec::<C::Scalar>::with_capacity(n_bits);
        let mut challenges_c2 =Vec::<C::Scalar>::with_capacity(n_bits);
        for i in 0..n_bits {
            responses_a.push(randomness[i] + c * w.elgamal_randomness[i]);
            if bit_at(&sig_bytes, i) == 0 { // i-th bit of the signature is 0
                let c2 = cheats[i];
                let c1 = c - c2;
                responses_b1.push(randomness[i] + c1*w.elgamal_randomness[i]);
                responses_b2.push(random_responses[i]);
                challenges_c1.push(c1);
                challenges_c2.push(c2);
            } else { // i-th bit of the signature is 1
                let c1 = cheats[i];
                let c2 = c - c1;
                responses_b1.push(random_responses[i]);
                responses_b2.push(randomness[i] + c2*w.elgamal_randomness[i]);
                challenges_c1.push(c1);
                challenges_c2.push(c2);
            }
        }

        let total_elgamal_response = *total_elgamal_randomness + c * total_elgamal_exp;

        Proof::<C> {
            commitments,
            challenges: (challenges_c1, challenges_c2),
            responses: ProofResponses::<C> {
                rel_as: rel_as_response,
                sig_keys: sig_keys_response,
                sig: sig_response,
                a_bits: responses_a,
                b1_bits: responses_b1,
                b2_bits: responses_b2,
                total: total_elgamal_response
            }
        }
    }

    #[rustfmt::skip]
    fn verify(crs: &Self::CRS, x: &Self::Statement, p: &Self::Proof) -> bool {
        let g = C::ProjectivePoint::generator();
        let ek = x.x;
        let ekg = x.x - g;

        let rv = x.gs + ((-x.vk) * x.sig_hash);
        let proj_pk = proj::<C>(&x.vk);
        let proj_rv = proj::<C>(&rv);
        let hasher = H::new();
        let ev = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(&proj_pk)
                .chain_update(&proj_rv)
                .chain_update(x.msg.as_str())
                .finalize(),
        );
        let c = compute_challenge::<C, H>(&p.commitments, x);

        let mut A = C::ProjectivePoint::identity();
        let mut B = C::ProjectivePoint::identity();
        let mut exp_acc = C::Scalar::ONE;
        for i in 0..x.elgamal_a.len() {
            let c1 = p.challenges.0[i];
            let c2 = p.challenges.1[i];
            if !( c == c1 + c2
                && g * p.responses.a_bits[i] == p.commitments.a_bits[i] + x.elgamal_a[i]*c
                && ek * p.responses.b1_bits[i] == p.commitments.b1_bits[i] + x.elgamal_b[i]*c1
                && ek * p.responses.b2_bits[i] == p.commitments.b2_bits[i] + (x.elgamal_b[i]-g)*c2) {
                return false;
            }
            A = A + x.elgamal_a[i]*exp_acc;
            B = B + x.elgamal_b[i]*exp_acc;
            exp_acc = exp_acc.double();
        }


        ev == x.sig_hash 
            && g * p.responses.sig_keys == p.commitments.sig_keys + x.vk*c
            && g * p.responses.rel_as == p.commitments.rel_as + x.x*c
            && g * p.responses.total == p.commitments.a_total + A*c
//            && g * p.responses.total == p.commitments.b_total + ek * c - x.gs
    }
}
