use crate::hard_relation::HardRelation;
use crate::signature_scheme::SignatureScheme;
use digest::Digest;
use elliptic_curve::ff::Field;
use elliptic_curve::ops::Invert;
use elliptic_curve::ops::Reduce;
use elliptic_curve::point::AffineCoordinates;
use elliptic_curve::scalar::NonZeroScalar;
use elliptic_curve::AffinePoint;
use elliptic_curve::CurveArithmetic;
use elliptic_curve::Group;
use rand_core::OsRng;
use std::marker::PhantomData;

pub struct ECDSASignature<C>
where
    C: CurveArithmetic,
{
    sig: NonZeroScalar<C>,
    proof: NonZeroScalar<C>,
}

pub struct ECDSA<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    _curve_marker: PhantomData<C>,
    _hash_marker: PhantomData<H>,
}

impl<C, H> SignatureScheme for ECDSA<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    type PK = C::ProjectivePoint;
    type SK = NonZeroScalar<C>;
    type Signature = ECDSASignature<C>;

    fn gen() -> (Self::SK, Self::PK) {
        Self::SK::gen(&C::ProjectivePoint::generator())
    }

    fn sign(sk: &Self::SK, msg: &str) -> Self::Signature {
        let hasher = H::new();
        let bytes = hasher.chain_update(msg).finalize();
        let h = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(&bytes);

        let g = C::ProjectivePoint::generator();

        let k = NonZeroScalar::<C>::random(&mut OsRng);
        let R = g * k.as_ref();
        let affine_R: AffinePoint<C> = R.into();
        // affine_R.x() is not 0 because R is computed as g*k, where k is not 0
        // therefore, it is completely safe to unwrap
        let r = NonZeroScalar::<C>::from_repr(affine_R.x()).unwrap();
        let _r = r.as_ref();
        let k_inv = k.invert();
        let scalar_proof = (*k_inv) * (h + (*_r) * (sk.as_ref()));
        // scalar_proof is very inlikely to be 0 because:
        //     - k_inv, the multiplicative inverse of k cannot be 0 (because k is not 0)
        //     - h is very unlikely to be 0 (hash)
        //     - _r is a non-zero scalar
        //     - sk is a non-zero scalar
        // therefore it is very likely safe to unwrap
        let proof = NonZeroScalar::<C>::new(scalar_proof).unwrap();

        ECDSASignature::<C> { sig: r, proof }
    }

    fn verify(pk: &Self::PK, msg: &str, sig: &Self::Signature) -> bool {
        let hasher = H::new();
        let bytes = hasher.chain_update(msg).finalize();
        let h = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(&bytes);

        let g = C::ProjectivePoint::generator();

        let s1 = sig.proof.invert();
        let s1 = s1.as_ref();
        let sig = sig.sig.as_ref();
        let R = g * (h * s1) + (*pk) * ((*sig) * (*s1));
        let affine_R: AffinePoint<C> = R.into();
        // affine_R is very unlikely to be 0 because it is computed from R and:
        //      - g is not the identity
        //      - h is very unlikely to be 0 (hash)
        //      - s1 is non-zero scalar
        //      - pk is g*sk where sk is non-zero (otherwise, pk = identity)
        //      - sig is non-zero
        // therefore it is very likely safe to unwrap
        let r = NonZeroScalar::<C>::from_repr(affine_R.x()).unwrap();
        let r = r.as_ref();

        r == sig
    }
}
