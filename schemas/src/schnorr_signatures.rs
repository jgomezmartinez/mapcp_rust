use crate::hard_relation::HardRelation;
use crate::signature_scheme::SignatureScheme;
use crate::utils::{point_to_byte_vector, proj, scalar_to_byte_vector};
use digest::Digest;
use elliptic_curve::ops::Reduce;
use elliptic_curve::scalar::NonZeroScalar;
use elliptic_curve::CurveArithmetic;
use elliptic_curve::Group;
use rand_core::OsRng;
use std::marker::PhantomData;

// The type representing SchnorrSignatures over an elliptic curve C
#[derive(Debug)]
pub struct SchnorrSignature<C>
where
    C: CurveArithmetic,
{
    pub proof: C::Scalar,
    pub sig: C::Scalar,
}

impl<C> SchnorrSignature<C>
where
    C: CurveArithmetic,
{
    pub fn to_byte_vector(&self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        v.append(&mut scalar_to_byte_vector::<C>(&self.proof));
        v.append(&mut scalar_to_byte_vector::<C>(&self.sig));
        v
    }
}

pub struct SchnorrSignatureScheme<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    _curve_marker: PhantomData<C>,
    _hash_marker: PhantomData<H>,
}

impl<C, H> SignatureScheme for SchnorrSignatureScheme<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    type PK = C::ProjectivePoint;
    type SK = NonZeroScalar<C>;
    type Signature = SchnorrSignature<C>;

    fn gen() -> (Self::SK, Self::PK) {
        Self::SK::gen(&C::ProjectivePoint::generator())
    }

    fn sign(sk: &Self::SK, msg: &str) -> Self::Signature {
        let _r = NonZeroScalar::<C>::random(&mut OsRng);
        let r = _r.as_ref();

        let g = C::ProjectivePoint::generator();
        let gr = g * r;
        let proj_g = proj::<C>(&gr);
        let pk = g * (*sk.as_ref());
        let proj_pk = proj::<C>(&pk);

        let hasher = H::new();
        let e = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(proj_pk)
                .chain_update(proj_g)
                .chain_update(msg)
                .finalize(),
        );
        let s = *r + *sk.as_ref() * e;

        SchnorrSignature::<C> { proof: e, sig: s }
    }

    fn verify(pk: &Self::PK, msg: &str, sig: &Self::Signature) -> bool {
        let g = C::ProjectivePoint::generator();
        let r = (g * sig.sig) + (-(*pk) * sig.proof);
        let proj_r = proj::<C>(&r);
        let proj_pk = proj::<C>(pk);
        let hasher = H::new();
        let e = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(proj_pk)
                .chain_update(proj_r)
                .chain_update(msg)
                .finalize(),
        );

        e == sig.proof
    }
}
