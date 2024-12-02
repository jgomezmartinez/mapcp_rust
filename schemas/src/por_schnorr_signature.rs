use crate::hard_relation::HardRelation;
use crate::nizk::NIZK;
use crate::utils::{point_to_byte_vector, proj, scalar_to_byte_vector};
use digest::{Digest, KeyInit};
use elliptic_curve::ops::Reduce;
use elliptic_curve::point::AffineCoordinates;
use elliptic_curve::scalar::NonZeroScalar;
use elliptic_curve::FieldBytes;
use elliptic_curve::{CurveArithmetic, Group};
use rand_core::OsRng;
use std::marker::PhantomData;
use crate::schnorr_signatures::{SchnorrSignatureScheme, SchnorrSignature};
use crate::signature_scheme::SignatureScheme;
use std::time::Instant;

pub struct PoRSchnorrSignature<C, H>
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
    sig_proof: C::Scalar,
    w: C::Scalar,
}

impl<C> Witness<C>
where
    C: CurveArithmetic,
{
    pub fn new(sig: C::Scalar, w: C::Scalar) -> Self {
        Self { sig_proof: sig, w }
    }
}

pub struct Crs<C>
where 
    C: CurveArithmetic 
{
    g: C::ProjectivePoint,
    h: C::ProjectivePoint
}

pub struct Statement<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    x: C::ProjectivePoint,
    pk: C::ProjectivePoint,
    gs: C::ProjectivePoint,
    e: C::Scalar,
    msg: String,
    _hash_marker: PhantomData<H>,
}

impl<C, H> Statement<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    pub fn to_byte_vector(&self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        v.append(&mut point_to_byte_vector::<C>(&self.x));
        v.append(&mut point_to_byte_vector::<C>(&self.pk));
        v.append(&mut point_to_byte_vector::<C>(&self.gs));
        v.append(&mut scalar_to_byte_vector::<C>(&self.e));
        let clone_msg = self.msg.clone();
        v.append(&mut clone_msg.into_bytes());

        v
    }

    pub fn new(
        x: C::ProjectivePoint,
        pk: C::ProjectivePoint,
        gs: C::ProjectivePoint,
        e: C::Scalar,
        msg: String,
    ) -> Self {
        Self {
            x,
            pk,
            gs,
            e,
            msg,
            _hash_marker: PhantomData,
        }
    }
}

impl<C, H> HardRelation<Statement<C, H>, Witness<C>> for Witness<C>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    type PP = Crs<C>;

    fn R(pp: &Self::PP, w: &Witness<C>, x: &Statement<C, H>) -> bool {
        let rv = x.gs + x.pk * x.e;
        let proj_pk = proj::<C>(&x.pk);
        let proj_rv = proj::<C>(&rv);
        let hasher = H::new();
        let ev = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(&proj_pk)
                .chain_update(&proj_rv)
                .chain_update(x.msg.as_str())
                .finalize(),
        );
        let b1 = x.gs == pp.g * w.sig_proof && ev == x.e;
        let b2 = pp.g * w.w == x.x;
        let b3 = pp.h * w.w == x.x;
        
        (b1 && b2) || b3

        //let g = C::ProjectivePoint::generator();
        //let rv = x.gs + x.pk * x.e;
        //let proj_rv = proj::<C>(&rv);
        //let hasher = H::new();
        //let ev = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
        //    &hasher
        //        .chain_update(&proj_rv)
        //        .chain_update(x.msg.as_str())
        //        .finalize(),
        //);
        //x.x == g * w.w && x.gs == g * w.sig && g * x.ct == x.x + x.gs && ev == x.e
    }
    // From a Witness w, compute a Statement s such that R(w, s) == true
    fn statement(pp: &Self::PP, w: &Witness<C>) -> Statement<C, H> {
        unimplemented!("This function should never be called!");
    }

    fn gen(pp: &Self::PP) -> (Witness<C>, Statement<C, H>) {
        unimplemented!("This function should never be called!");
    }
}

pub struct Proof<C>
where
    C: CurveArithmetic,
{
    a: (C::ProjectivePoint, C::ProjectivePoint, C::ProjectivePoint),
    r: (C::Scalar, C::Scalar, C::Scalar),
    c: (C::Scalar, C::Scalar)
}

impl<C> Proof<C>
where
    C: CurveArithmetic,
{
    pub fn to_byte_vector(&self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        let (a_g, a_sig, a_h) = self.a;
        let (r_g, r_sig, r_h) = self.r;
        let (c1, c2) = self.c;
        v.append(&mut point_to_byte_vector::<C>(&a_g));
        v.append(&mut point_to_byte_vector::<C>(&a_sig));
        v.append(&mut point_to_byte_vector::<C>(&a_h));
        v.append(&mut scalar_to_byte_vector::<C>(&r_g));
        v.append(&mut scalar_to_byte_vector::<C>(&r_sig));
        v.append(&mut scalar_to_byte_vector::<C>(&r_h));
        v.append(&mut scalar_to_byte_vector::<C>(&c1));
        v.append(&mut scalar_to_byte_vector::<C>(&c2));

        v
    }
}

fn compute_challenge<C, H>(
    a: (C::ProjectivePoint, C::ProjectivePoint, C::ProjectivePoint),
    x: &Statement<C, H>,
) -> C::Scalar
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    let (a_g, a_sig, a_h) = a;

    let proj_a_g = proj::<C>(&a_g);
    let proj_a_sig = proj::<C>(&a_sig);
    let proj_a_h = proj::<C>(&a_h);
    let proj_gs = proj::<C>(&x.gs);
    let proj_x = proj::<C>(&x.x);
    let proj_pk = proj::<C>(&x.pk);
    let e = Into::<<C::AffinePoint as AffineCoordinates>::FieldRepr>::into(x.e);

    let hasher = H::new();
    let c = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
        &hasher
            .chain_update(proj_a_g)
            .chain_update(proj_a_h)
            .chain_update(proj_a_sig)
            .chain_update(proj_gs)
            .chain_update(proj_x)
            .chain_update(proj_pk)
            .chain_update(e)
            .chain_update(x.msg.as_str())
            .finalize(),
    );

    c
}

impl<C, H> NIZK for PoRSchnorrSignature<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    type CRS = Crs<C>;
    type Statement = Statement<C, H>;
    type Witness = Witness<C>;
    type Proof = Proof<C>;

    fn crs_gen() -> Self::CRS {
        crate::debug_print!("DIFFIE-HELMAN for interactive crs gen for generators g and h");
        // both parties:
        let g = C::ProjectivePoint::generator();
        // Party A:
        let start = Instant::now();
        let nz_alpha = NonZeroScalar::<C>::random(&mut OsRng);
        let alpha : C::Scalar = *nz_alpha;
        let h1 = g * alpha;
        let duration = start.elapsed();
        crate::debug_print!("Diffie-Helman first phase: {} ms", duration.as_millis());
        crate::debug_print!("transmited {} bytes", point_to_byte_vector::<C>(&h1).len());
        // Send h1 to party A
        // Party B:
        let start = Instant::now();
        let nz_beta = NonZeroScalar::<C>::random(&mut OsRng);
        let beta : C::Scalar = *nz_beta;
        let h = h1* beta;
        let duration = start.elapsed();
        crate::debug_print!("Diffie-Helman second phase: {} ms", duration.as_millis());
        crate::debug_print!("transmited {} bytes", point_to_byte_vector::<C>(&h).len());
        // Send h to  party A
        // both parties:
        let crs = Crs::<C> {
            g, h
        };
        
        crs
    }

    fn prove(crs: &Self::CRS, x: &Self::Statement, w: &Self::Witness) -> Self::Proof {
        let nz_u_g = NonZeroScalar::<C>::random(&mut OsRng);
        let nz_u_h = NonZeroScalar::<C>::random(&mut OsRng);
        let nz_u_sig = NonZeroScalar::<C>::random(&mut OsRng);
        let u_g = nz_u_g.as_ref();
        let u_h = nz_u_h.as_ref();
        let u_sig = nz_u_sig.as_ref();
        let g = crs.g;
        let h = crs.h;

        let a_g : C::ProjectivePoint;
        let a_sig : C::ProjectivePoint;
        let a_h : C::ProjectivePoint;
        let a : (C::ProjectivePoint, C::ProjectivePoint, C::ProjectivePoint);

        // TODO change compute challenge
        let c : C::Scalar;
        let c1: C::Scalar;
        let c2: C::Scalar;

        let r_g : C::Scalar;
        let r_sig : C::Scalar;
        let r_h : C::Scalar;

        if crs.g * w.w == x.x {
            let nz_c2 = NonZeroScalar::<C>::random(&mut OsRng);
            c2 = *nz_c2;

            a_g = g* u_g;
            a_sig = g* u_sig;
            a_h = x.x * (-c2) + h*u_h;

            a = (a_g, a_sig, a_h);
            c = compute_challenge::<C, H>(a, x);
            c1 = c - c2;

            r_g = c1*w.w + u_g;
            r_sig = c1*w.sig_proof + u_sig;
            r_h = *u_h;
        } else {
            let nz_c1 = NonZeroScalar::<C>::random(&mut OsRng);
            c1 = *nz_c1;

            a_g = x.x*(-c1) + g* u_g;
            a_sig = x.gs*(-c1) + g*u_sig;
            a_h = h * u_h;

            a = (a_g, a_sig, a_h);
            c = compute_challenge::<C, H>(a, x);
            c2 = c - c1;

            r_g = *u_g;
            r_sig = *u_sig;
            r_h = c2*w.w + u_h;
        }

        let c = (c1, c2);
        let r = (r_g, r_sig, r_h);

        Proof::<C> {
            a, r, c
        }
    }

    #[rustfmt::skip]
    fn verify(crs: &Self::CRS, x: &Self::Statement, p: &Self::Proof) -> bool {
        let (a_g, a_sig, a_h) = p.a;
        let (r_g, r_sig, r_h) = p.r;
        let (c1, c2) = p.c;
        let g = crs.g;
        let h = crs.h;
        let rv = x.gs + (-x.pk) * x.e;
        let proj_pk = proj::<C>(&x.pk);
        let proj_rv = proj::<C>(&rv);
        let hasher = H::new();
        let ev = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(&proj_pk)
                .chain_update(&proj_rv)
                .chain_update(x.msg.as_str())
                .finalize(),
        );
        let c = compute_challenge::<C, H>(p.a, x);

        c == c1 + c2
        && ev == x.e 
        && g * r_sig == a_sig + x.gs * c1
        && g * r_g == a_g + x.x * c1
        && h * r_h == a_h + x.x * c2
    }
}

