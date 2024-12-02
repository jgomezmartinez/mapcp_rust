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

pub struct PoKSchnorrSignature<C, H>
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
    sig: C::Scalar,
    w: C::Scalar,
}

impl<C> Witness<C>
where
    C: CurveArithmetic,
{
    pub fn new(sig: C::Scalar, w: C::Scalar) -> Self {
        Self { sig, w }
    }
}

pub struct Statement<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    gs: C::ProjectivePoint,
    x: C::ProjectivePoint,
    pk: C::ProjectivePoint,
    e: C::Scalar,
    ct: C::Scalar,
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
        v.append(&mut point_to_byte_vector::<C>(&self.gs));
        v.append(&mut point_to_byte_vector::<C>(&self.x));
        v.append(&mut point_to_byte_vector::<C>(&self.pk));
        v.append(&mut scalar_to_byte_vector::<C>(&self.e));
        v.append(&mut scalar_to_byte_vector::<C>(&self.ct));
        let clone_msg = self.msg.clone();
        v.append(&mut clone_msg.into_bytes());

        v
    }

    pub fn new(
        gs: C::ProjectivePoint,
        x: C::ProjectivePoint,
        pk: C::ProjectivePoint,
        e: C::Scalar,
        ct: C::Scalar,
        msg: String,
    ) -> Self {
        Self {
            gs,
            x,
            pk,
            e,
            ct,
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
    type PP = C::ProjectivePoint;

    fn R(pp: &Self::PP, w: &Witness<C>, x: &Statement<C, H>) -> bool {
        let g = *pp;
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
        x.x == g * w.w && x.gs == g * w.sig && g * x.ct == x.x + x.gs && ev == x.e
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
    a: (C::ProjectivePoint, C::ProjectivePoint),
    r: (C::Scalar, C::Scalar),
}

impl<C> Proof<C>
where
    C: CurveArithmetic,
{
    pub fn to_byte_vector(&self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        let (a1, a2) = self.a;
        let (r1, r2) = self.r;
        v.append(&mut point_to_byte_vector::<C>(&a1));
        v.append(&mut point_to_byte_vector::<C>(&a2));
        v.append(&mut scalar_to_byte_vector::<C>(&r1));
        v.append(&mut scalar_to_byte_vector::<C>(&r2));

        v
    }
}

fn compute_challenge<C, H>(
    a: (C::ProjectivePoint, C::ProjectivePoint),
    x: &Statement<C, H>,
) -> C::Scalar
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    let (a1, a2) = a;

    let proj_a1 = proj::<C>(&a1);
    let proj_a2 = proj::<C>(&a2);
    let proj_gs = proj::<C>(&x.gs);
    let proj_x = proj::<C>(&x.x);
    let proj_pk = proj::<C>(&x.pk);
    let e = Into::<<C::AffinePoint as AffineCoordinates>::FieldRepr>::into(x.e);
    let ct = Into::<<C::AffinePoint as AffineCoordinates>::FieldRepr>::into(x.ct);

    let hasher = H::new();
    let c = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
        &hasher
            .chain_update(proj_a1)
            .chain_update(proj_a2)
            .chain_update(proj_gs)
            .chain_update(proj_x)
            .chain_update(proj_pk)
            .chain_update(e)
            .chain_update(ct)
            .chain_update(x.msg.as_str())
            .finalize(),
    );

    c
}

impl<C, H> NIZK for PoKSchnorrSignature<C, H>
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
        let nz_u1 = NonZeroScalar::<C>::random(&mut OsRng);
        let nz_u2 = NonZeroScalar::<C>::random(&mut OsRng);
        let u1 = nz_u1.as_ref();
        let u2 = nz_u2.as_ref();
        let g = C::ProjectivePoint::generator();
        let a1 = g * u1;
        let a2 = g * u2;

        let a = (a1, a2);
        let c = compute_challenge::<C, H>(a, x);

        let r1 = *u1 + w.sig * c;
        let r2 = *u2 + w.w * c;
        let r = (r1, r2);

        Proof::<C> { a, r }
    }

    #[rustfmt::skip]
    fn verify(crs: &Self::CRS, x: &Self::Statement, p: &Self::Proof) -> bool {
        let (a1, a2) = p.a;
        let (r1, r2) = p.r;
        let g = C::ProjectivePoint::generator();
        let rv = x.gs + ((-x.pk) * x.e);
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

        g * x.ct == x.x + x.gs 
            && ev == x.e 
            && g * r1 == a1 + x.gs * c 
            && g * r2 == a2 + x.x * c
    }
}
