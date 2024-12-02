use crate::nizk::NIZK;
use crate::utils::proj;
use crate::HardRelation;
use digest::Digest;
use elliptic_curve::ff::Field;
use elliptic_curve::ops::Reduce;
use elliptic_curve::scalar::NonZeroScalar;
use elliptic_curve::{CurveArithmetic, Group};
use rand_core::OsRng;
use std::marker::PhantomData;

pub struct SigmaProofStar<C, H>
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
    y: C::Scalar,
    w: C::Scalar,
}

impl<C> Witness<C>
where
    C: CurveArithmetic,
{
    fn new(s: C::Scalar, e: C::Scalar, y: C::Scalar, w: C::Scalar) -> Self {
        Witness { s, e, y, w }
    }
}

pub struct Statement<C>
where
    C: CurveArithmetic,
{
    g: C::ProjectivePoint,
    h: C::ProjectivePoint,
    c_s: C::ProjectivePoint,
    y: C::ProjectivePoint,
    m: C::ProjectivePoint,
    pk: C::ProjectivePoint,
    x: C::ProjectivePoint,
}

impl<C> Statement<C>
where
    C: CurveArithmetic,
{
    fn new(
        g: C::ProjectivePoint,
        h: C::ProjectivePoint,
        c_s: C::ProjectivePoint,
        y: C::ProjectivePoint,
        m: C::ProjectivePoint,
        pk: C::ProjectivePoint,
        x: C::ProjectivePoint,
    ) -> Self {
        Statement {
            g,
            h,
            c_s,
            y,
            m,
            pk,
            x,
        }
    }
}

// Relation* = {(c_s, x, h, ct; w, s) | c_s = commit(s) &
//                                      x = g^w &
//                                      ct = enc(pk, s) &
//                                      pk = g^w}
// in our case, we have:
// Relation* = {(c_s, x, h, (Y, M), pk; s, y, w) | c_s = g^e * h^s &
//                                                 Y = g^y &
//                                                 M = s * pk^y &
//                                                 x = g^w &
//                                                 pk = g^w}
impl<C> HardRelation<Statement<C>, Witness<C>> for Witness<C>
where
    C: CurveArithmetic,
{
    fn R(w: &Witness<C>, x: &Statement<C>) -> bool {
        (x.c_s == x.g * w.e + x.h * w.s)
            && (x.y == x.g * w.y)
            && (x.m == w.s + x.pk * w.y)
            && (x.x == x.g * w.w)
            && (x.pk == x.g * w.w)
    }

    fn statement(w: &Witness<C>) -> Statement<C> {
        //let g = C::ProjectivePoint::generator();
        //let h = C::ProjectivePoint::random(&mut OsRng);
        //let c_s = g * w.e + h * w.s;
        //let y = g * w.y;
        //let pk = g * w.w;
        //let m = w.s + pk * w.y;
        //let x = g * w.w;
        //Statement::<C>::new(g, h, c_s, y, m, pk, x)
        unimplemented!("This function should never be called!");
    }

    fn gen() -> (Witness<C>, Statement<C>) {
        //let s = C::Scalar::random(&mut OsRng);
        //let e = C::Scalar::random(&mut OsRng);
        //let y = C::Scalar::random(&mut OsRng);
        //let w = C::Scalar::random(&mut OsRng);
        //let witness = Witness::<C>::new(s, e, y, w);
        //let statement = Self::statement(&witness);

        //(witness, statement)
        unimplemented!("This function should never be called!");
    }
}

type Point<C: CurveArithmetic> = C::ProjectivePoint;
type Scalar<C: CurveArithmetic> = C::Scalar;

impl<C, H> NIZK for SigmaProofStar<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    type CRS = C::ProjectivePoint;
    type Statement = Statement<C>;
    type Witness = Witness<C>;
    type Proof = (
        (Point<C>, Point<C>, Point<C>, Point<C>, Point<C>),
        (Scalar<C>, Scalar<C>, Scalar<C>, Scalar<C>, Scalar<C>),
    );

    fn crs_gen() -> Self::CRS {
        Self::CRS::generator()
    }

    fn prove(crs: &Self::CRS, x: &Self::Statement, w: &Self::Witness) -> Self::Proof {
        let _u_11 = NonZeroScalar::<C>::random(&mut OsRng);
        let _u_12 = NonZeroScalar::<C>::random(&mut OsRng);
        let _u_32 = NonZeroScalar::<C>::random(&mut OsRng);
        let _u_2 = NonZeroScalar::<C>::random(&mut OsRng);
        let u_11 = _u_11.as_ref();
        let u_12 = _u_12.as_ref();
        let u_32 = _u_32.as_ref();
        let u_2 = _u_2.as_ref();

        let g = x.g;
        let h = x.h;

        let a_11 = g * u_11;
        let a_12 = h * u_12;
        let a_31 = u_11 + x.pk * u_11;
        let a_32 = g * u_32;
        let a_2 = g * u_2;
        let a = (a_11, a_12, a_31, a_32, a_2);

        let proj_g = proj::<C>(&g);
        let proj_h = proj::<C>(&h);
        let proj_c_s = proj::<C>(&x.c_s);
        let proj_y = proj::<C>(&x.y);
        let proj_m = proj::<C>(&x.m);
        let proj_x = proj::<C>(&x.x);
        let proj_a_11 = proj::<C>(&a_11);
        let proj_a_12 = proj::<C>(&a_12);
        let proj_a_31 = proj::<C>(&a_31);
        let proj_a_32 = proj::<C>(&a_32);
        let proj_a_2 = proj::<C>(&a_2);

        let hasher = H::new();
        let c = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(proj_g)
                .chain_update(proj_h)
                .chain_update(proj_c_s)
                .chain_update(proj_x)
                .chain_update(proj_a_11)
                .chain_update(proj_a_12)
                .chain_update(proj_a_31)
                .chain_update(proj_a_32)
                .chain_update(proj_a_2)
                .finalize(),
        );

        let r_11 = u_11 + c * w.e;
        let r_12 = u_12 + c * w.s;
        let r_31 = u_11 + c * w.s;
        let r_32 = u_32 + c * w.y;
        let r_2 = u_2 + c * w.w;

        let r = (r_11, r_12, r_31, r_32, r_2);

        (a, r)
    }

    fn verify(crs: &Self::CRS, x: &Self::Statement, p: &Self::Proof) -> bool {
        let (a, r) = *p;
        let (a_11, a_12, a_31, a_32, a_2) = a;
        let (r_11, r_12, r_31, r_32, r_2) = r;

        let g = x.g;
        let h = x.h;

        let proj_g = proj::<C>(&g);
        let proj_h = proj::<C>(&h);
        let proj_c_s = proj::<C>(&x.c_s);
        let proj_y = proj::<C>(&x.y);
        let proj_m = proj::<C>(&x.m);
        let proj_x = proj::<C>(&x.x);
        let proj_a_11 = proj::<C>(&a_11);
        let proj_a_12 = proj::<C>(&a_12);
        let proj_a_31 = proj::<C>(&a_31);
        let proj_a_32 = proj::<C>(&a_32);
        let proj_a_2 = proj::<C>(&a_2);

        let hasher = H::new();
        let c = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(proj_g)
                .chain_update(proj_h)
                .chain_update(proj_c_s)
                .chain_update(proj_x)
                .chain_update(proj_a_11)
                .chain_update(proj_a_12)
                .chain_update(proj_a_31)
                .chain_update(proj_a_32)
                .chain_update(proj_a_2)
                .finalize(),
        );

        (g * r_2 == a_2 + x.x * c)
            && (g * r_2 == a_2 + x.pk * c)
            && (g * r_11 + h * r_12 == a_11 + a_12 + x.c_s * c)
            && (a_31 + x.m * c == r_31 + x.pk * c)
            && (a_32 + x.y * c == g * r_32)
    }
}
