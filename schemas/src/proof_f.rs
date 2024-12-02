use crate::hard_relation::HardRelation;
use crate::nizk::NIZK;
use crate::utils::proj;
use digest::Digest;
use elliptic_curve::ff::Field;
use elliptic_curve::ops::Reduce;
use elliptic_curve::scalar::NonZeroScalar;
use elliptic_curve::{CurveArithmetic, Group};
use rand_core::OsRng;
use std::marker::PhantomData;

pub struct SigmaProofF<C, H>
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
    s: C::Scalar,
    e: C::Scalar,
}

impl<C> Witness<C>
where
    C: CurveArithmetic,
{
    fn new(s: C::Scalar, e: C::Scalar) -> Self {
        Witness { s, e }
    }
}

pub struct Statement<C>
where
    C: CurveArithmetic,
{
    g: C::ProjectivePoint,
    h: C::ProjectivePoint,
    x: C::ProjectivePoint,
    c_s: C::ProjectivePoint,
}

impl<C> Statement<C>
where
    C: CurveArithmetic,
{
    fn new(
        g: C::ProjectivePoint,
        h: C::ProjectivePoint,
        x: C::ProjectivePoint,
        c_s: C::ProjectivePoint,
    ) -> Self {
        Statement { g, h, x, c_s }
    }
}

// Relation_f = {(f, c_s; s) | f(s) = 1 && c_s = commit(s)}
// in the case that f(s) = 1 <=> x = g^s we get:
// Relation_f = {(x, c_s, h, g; s, e) | x = g^s && c_s = g^e * h^s}
impl<C> HardRelation<Statement<C>, Witness<C>> for Witness<C>
where
    C: CurveArithmetic,
{
    type PP = C::ProjectivePoint;

    fn R(pp: &Self::PP, w: &Witness<C>, x: &Statement<C>) -> bool {
        x.x == x.g * w.s && x.c_s == x.g * w.e + x.h * w.s
    }

    fn statement(pp: &Self::PP, w: &Witness<C>) -> Statement<C> {
        //let g = C::ProjectivePoint::generator();
        //let h = C::ProjectivePoint::random(&mut OsRng);
        //let x = g * w.s;
        //let c_s = g * w.e + h * w.s;
        //Statement::<C>::new(g, h, x, c_s)
        unimplemented!("This function should never be called!");
    }

    fn gen(pp: &Self::PP) -> (Witness<C>, Statement<C>) {
        //let s = C::Scalar::random(&mut OsRng);
        //let e = C::Scalar::random(&mut OsRng);
        //let w = Witness::<C>::new(s, e);
        //let x = Self::statement(&w);

        //(w, x)
        unimplemented!("This function should never be called!");
    }
}

impl<C, H> NIZK for SigmaProofF<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    type CRS = C::ProjectivePoint;
    type Statement = Statement<C>;
    type Witness = Witness<C>;
    type Proof = (
        (C::ProjectivePoint, C::ProjectivePoint, C::ProjectivePoint),
        (C::Scalar, C::Scalar, C::Scalar),
    );

    fn crs_gen() -> Self::CRS {
        Self::CRS::generator()
    }

    fn prove(crs: &Self::CRS, x: &Self::Statement, w: &Self::Witness) -> Self::Proof {
        let _u1 = NonZeroScalar::<C>::random(&mut OsRng);
        let _u2 = NonZeroScalar::<C>::random(&mut OsRng);
        let u1 = _u1.as_ref();
        let u2 = _u2.as_ref();

        let g = x.g;
        let h = x.h;

        let a0 = g * u1;
        let a1 = g * u1;
        let a2 = h * u2;
        let a = (a0, a1, a2);

        let proj_g = proj::<C>(&g);
        let proj_h = proj::<C>(&h);
        let proj_c_s = proj::<C>(&x.c_s);
        let proj_x = proj::<C>(&x.x);
        let proj_a0 = proj::<C>(&a0);
        let proj_a1 = proj::<C>(&a1);
        let proj_a2 = proj::<C>(&a2);

        let hasher = H::new();
        let c = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(proj_g)
                .chain_update(proj_h)
                .chain_update(proj_c_s)
                .chain_update(proj_x)
                .chain_update(proj_a0)
                .chain_update(proj_a1)
                .chain_update(proj_a2)
                .finalize(),
        );

        let r0 = *u1 + c * w.s;
        let r1 = *u1 + c * w.e;
        let r2 = *u2 + c * w.s;
        let r = (r0, r1, r2);

        (a, r)
    }

    fn verify(crs: &Self::CRS, x: &Self::Statement, p: &Self::Proof) -> bool {
        let (a, r) = *p;
        let (a0, a1, a2) = a;
        let (r0, r1, r2) = r;

        let g = x.g;
        let h = x.h;

        let proj_g = proj::<C>(&g);
        let proj_h = proj::<C>(&h);
        let proj_c_s = proj::<C>(&x.c_s);
        let proj_x = proj::<C>(&x.x);
        let proj_a0 = proj::<C>(&a0);
        let proj_a1 = proj::<C>(&a1);
        let proj_a2 = proj::<C>(&a2);

        let hasher = H::new();
        let c = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(proj_g)
                .chain_update(proj_h)
                .chain_update(proj_c_s)
                .chain_update(proj_x)
                .chain_update(proj_a0)
                .chain_update(proj_a1)
                .chain_update(proj_a2)
                .finalize(),
        );

        (g * r0 == a0 + x.x * c) && (g * r1 + h * r2 == a1 + a2 + x.c_s * c)
    }
}
