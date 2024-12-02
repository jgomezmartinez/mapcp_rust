use crate::hard_relation::HardRelation;
use crate::nizk::NIZK;
use crate::utils::{point_to_byte_vector, proj, scalar_to_byte_vector};
use digest::Digest;
use elliptic_curve::ops::Reduce;
use elliptic_curve::point::AffineCoordinates;
use elliptic_curve::scalar::NonZeroScalar;
use elliptic_curve::AffinePoint;
use elliptic_curve::FieldBytes;
use elliptic_curve::{CurveArithmetic, Group};
use rand_core::OsRng;
use std::marker::PhantomData;

pub struct SigmaProofPhi<C1, C2, H1, H2>
where
    C1: CurveArithmetic,
    C2: CurveArithmetic,
    H2: Digest<OutputSize = C2::FieldBytesSize>,
    H1: Digest<OutputSize = C1::FieldBytesSize>,
{
    _curve_marker_1: PhantomData<C1>,
    _curve_marker_2: PhantomData<C2>,
    _hash_marker_1: PhantomData<H1>,
    _hash_marker_2: PhantomData<H2>,
}

pub struct Witness<C>
where
    C: CurveArithmetic,
{
    s: C::Scalar,
    w: C::Scalar,
    y: C::Scalar,
    point: C::ProjectivePoint,
}

impl<C> Witness<C>
where
    C: CurveArithmetic,
{
    pub fn new(s: C::Scalar, w: C::Scalar, y: C::Scalar, point: C::ProjectivePoint) -> Self {
        Witness { s, w, y, point }
    }

    pub fn to_byte_vector(&self) -> Vec<u8> {
        let s_array = Into::<FieldBytes<C>>::into(self.s);
        let w_array = Into::<FieldBytes<C>>::into(self.w);
        let y_array = Into::<FieldBytes<C>>::into(self.y);
        let affine_point: AffinePoint<C> = self.point.into();
        let point_array = Into::<FieldBytes<C>>::into(affine_point.x());

        let mut v: Vec<u8> = Vec::new();
        v.extend_from_slice(s_array.as_slice());
        v.extend_from_slice(w_array.as_slice());
        v.extend_from_slice(y_array.as_slice());
        v.extend_from_slice(point_array.as_slice());
        v.push(affine_point.y_is_odd().unwrap_u8());

        v
    }
}

pub struct Statement<C1, C2>
where
    C1: CurveArithmetic,
    C2: CurveArithmetic,
{
    g1: C1::ProjectivePoint,
    g2: C2::ProjectivePoint,
    point_2: C2::ProjectivePoint,
    x: C1::ProjectivePoint,
    ct: (C1::ProjectivePoint, C1::ProjectivePoint),
}

impl<C1, C2> Statement<C1, C2>
where
    C1: CurveArithmetic,
    C2: CurveArithmetic,
{
    pub fn new(
        g1: C1::ProjectivePoint,
        g2: C2::ProjectivePoint,
        point_2: C2::ProjectivePoint,
        x: C1::ProjectivePoint,
        ct: (C1::ProjectivePoint, C1::ProjectivePoint),
    ) -> Self {
        Statement {
            g1,
            g2,
            point_2,
            x,
            ct,
        }
    }

    pub fn to_byte_vector(&self) -> Vec<u8> {
        let (ct_a, ct_b) = self.ct;
        let mut v: Vec<u8> = Vec::new();
        v.append(&mut point_to_byte_vector::<C2>(&self.point_2));
        v.append(&mut point_to_byte_vector::<C1>(&self.x));
        v.append(&mut point_to_byte_vector::<C1>(&ct_a));
        v.append(&mut point_to_byte_vector::<C1>(&ct_b));

        v
    }
}

fn scalar_transformation<C1, C2>(s1: &C1::Scalar) -> C2::Scalar
where
    C1: CurveArithmetic,
    C2: CurveArithmetic,
    <C2 as elliptic_curve::Curve>::Uint: From<<C1 as CurveArithmetic>::Scalar>,
{
    <C2::Scalar as Reduce<C2::Uint>>::reduce((*s1).into())
}

fn phi<C1, C2>(s: &C1::Scalar) -> C2::ProjectivePoint
where
    C1: CurveArithmetic,
    C2: CurveArithmetic,
    <C2 as elliptic_curve::Curve>::Uint: From<<C1 as CurveArithmetic>::Scalar>,
{
    let s2 = scalar_transformation::<C1, C2>(&s);
    C2::ProjectivePoint::generator() * s2
}

impl<C1, C2> HardRelation<Statement<C1, C2>, Witness<C1>> for Witness<C1>
where
    C1: CurveArithmetic,
    C2: CurveArithmetic,
    <C2 as elliptic_curve::Curve>::Uint: From<<C1 as CurveArithmetic>::Scalar>,
{
    type PP = (C1::ProjectivePoint, C2::ProjectivePoint);
    fn R(pp: &Self::PP, w: &Witness<C1>, x: &Statement<C1, C2>) -> bool {
        let (A, B) = x.ct;

        A == x.g1 * w.y
            && B == x.x * w.y + w.point
            && x.x == x.g1 * w.w
            && x.point_2 == x.g2 * scalar_transformation::<C1, C2>(&w.s)
            && x.point_2 == phi::<C1, C2>(&w.s)
    }

    fn statement(pp: &Self::PP, w: &Witness<C1>) -> Statement<C1, C2> {
        unimplemented!("This function should never be called!");
    }

    fn gen(pp: &Self::PP) -> (Witness<C1>, Statement<C1, C2>) {
        unimplemented!("This function should never be called!");
    }
}

impl<C1, C2, H1, H2> SigmaProofPhi<C1, C2, H1, H2>
where
    C1: CurveArithmetic,
    C2: CurveArithmetic,
    H2: Digest<OutputSize = C2::FieldBytesSize>,
    H1: Digest<OutputSize = C1::FieldBytesSize>,
    <C2 as elliptic_curve::Curve>::Uint: From<<C1 as CurveArithmetic>::Scalar>,
{
    fn compute_challenge(
        a: (
            C1::ProjectivePoint,
            C1::ProjectivePoint,
            C1::ProjectivePoint,
            C2::ProjectivePoint,
            C2::ProjectivePoint,
        ),
        x: &Statement<C1, C2>,
    ) -> (C1::Scalar, C2::Scalar) {
        let (a1, a2, a3, a4, a5) = a;
        let (ct_a, ct_b) = x.ct;
        let proj_g1 = proj::<C1>(&x.g1);
        let proj_g2 = proj::<C2>(&x.g2);
        let proj_point_2 = proj::<C2>(&x.point_2);
        let proj_x = proj::<C1>(&x.x);
        let proj_ct_a = proj::<C1>(&ct_a);
        let proj_ct_b = proj::<C1>(&ct_b);
        let proj_a1 = proj::<C1>(&a1);
        let proj_a2 = proj::<C1>(&a2);
        let proj_a3 = proj::<C1>(&a3);
        let proj_a4 = proj::<C2>(&a4);
        let proj_a5 = proj::<C2>(&a5);

        let hasher = H1::new();
        let c1 = <C1::Scalar as Reduce<C1::Uint>>::reduce_bytes(
            &hasher
                .chain_update(proj_g1)
                .chain_update(proj_g2)
                .chain_update(proj_point_2)
                .chain_update(proj_x)
                .chain_update(proj_ct_a)
                .chain_update(proj_ct_b)
                .chain_update(proj_a1)
                .chain_update(proj_a2)
                .chain_update(proj_a3)
                .chain_update(proj_a4)
                .chain_update(proj_a5)
                .finalize(),
        );
        let c2 = scalar_transformation::<C1, C2>(&c1);

        (c1, c2)
    }
}

pub struct Proof<C1, C2>
where
    C1: CurveArithmetic,
    C2: CurveArithmetic,
{
    a: (
        C1::ProjectivePoint,
        C1::ProjectivePoint,
        C1::ProjectivePoint,
        C2::ProjectivePoint,
        C2::ProjectivePoint,
    ),
    r: (
        C1::ProjectivePoint,
        C1::Scalar,
        C1::Scalar,
        C1::Scalar,
        C2::Scalar,
    ),
}

impl<C1, C2> Proof<C1, C2>
where
    C1: CurveArithmetic,
    C2: CurveArithmetic,
{
    pub fn to_byte_vector(&self) -> Vec<u8> {
        let (a1, a2, a3, a4, a5) = self.a;
        let (r1, r2, r3, r4, r5) = self.r;
        let mut v: Vec<u8> = Vec::new();

        v.append(&mut point_to_byte_vector::<C1>(&a1));
        v.append(&mut point_to_byte_vector::<C1>(&a2));
        v.append(&mut point_to_byte_vector::<C1>(&a3));
        v.append(&mut point_to_byte_vector::<C2>(&a4));
        v.append(&mut point_to_byte_vector::<C2>(&a5));
        v.append(&mut point_to_byte_vector::<C1>(&r1));
        v.append(&mut scalar_to_byte_vector::<C1>(&r2));
        v.append(&mut scalar_to_byte_vector::<C1>(&r3));
        v.append(&mut scalar_to_byte_vector::<C1>(&r4));
        v.append(&mut scalar_to_byte_vector::<C2>(&r5));

        v
    }
}

impl<C1, C2, H1, H2> NIZK for SigmaProofPhi<C1, C2, H1, H2>
where
    C1: CurveArithmetic,
    C2: CurveArithmetic,
    H2: Digest<OutputSize = C2::FieldBytesSize>,
    H1: Digest<OutputSize = C1::FieldBytesSize>,
    <C2 as elliptic_curve::Curve>::Uint: From<<C1 as CurveArithmetic>::Scalar>,
{
    type CRS = C1::ProjectivePoint;
    type Statement = Statement<C1, C2>;
    type Witness = Witness<C1>;
    type Proof = Proof<C1, C2>;

    fn crs_gen() -> Self::CRS {
        Self::CRS::generator()
    }

    fn prove(crs: &Self::CRS, x: &Self::Statement, w: &Self::Witness) -> Self::Proof {
        let _u1 = NonZeroScalar::<C1>::random(&mut OsRng);
        let _u2 = NonZeroScalar::<C1>::random(&mut OsRng);
        let _u3 = NonZeroScalar::<C1>::random(&mut OsRng);
        let _u4 = _u1; //NonZeroScalar::<C1>::random(&mut OsRng);
        let _u5 = NonZeroScalar::<C2>::random(&mut OsRng);

        let u1 = _u1.as_ref();
        let u2 = _u2.as_ref();
        let u3 = _u3.as_ref();
        let u4 = _u4.as_ref();
        let u5 = _u5.as_ref();

        let a1 = x.x * (*u1);
        let a2 = x.g1 * (*u2);
        let a3 = x.g1 * (*u3);
        let a4 = phi::<C1, C2>(u4);
        let a5 = x.g2 * (*u5);
        let a = (a1, a2, a3, a4, a5);

        let (c1, _) = Self::compute_challenge(a, x);

        let r1 = w.point * c1 + x.x * (*u1 - *u2);
        let r2 = *u2 + c1 * w.y;
        let r3 = *u3 + c1 * w.w;
        let aux = w.s * c1;
        let s_c1 = scalar_transformation::<C1, C2>(&aux);
        let r4 = (*u4) + w.s * c1;
        let r5 = *u5 + s_c1;
        let r = (r1, r2, r3, r4, r5);

        Proof::<C1, C2> { a, r }
    }

    fn verify(crs: &Self::CRS, x: &Self::Statement, p: &Self::Proof) -> bool {
        let (a1, a2, a3, a4, a5) = p.a;
        let (r1, r2, r3, r4, r5) = p.r;

        let (c1, c2) = Self::compute_challenge(p.a, x);

        let (ct_a, ct_b) = x.ct;

        a1 + ct_b * c1 == r1 + x.x * r2
            && a2 + ct_a * c1 == x.g1 * r2
            && a3 + x.x * c1 == x.g1 * r3
            && phi::<C1, C2>(&r4) == a4 + x.point_2 * c2
            && x.g2 * r5 == a5 + x.point_2 * c2
    }
}
