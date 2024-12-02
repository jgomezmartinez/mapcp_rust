use crate::adaptor_signatures::AdaptorSignatureScheme;
use crate::hard_relation::HardRelation;
use crate::schnorr_signatures::SchnorrSignature;
use crate::utils::proj;
use digest::Digest;
use elliptic_curve::ff::Field;
use elliptic_curve::ops::Reduce;
use elliptic_curve::scalar::NonZeroScalar;
use elliptic_curve::{CurveArithmetic, Group};
use rand_core::OsRng;
use std::marker::PhantomData;
use subtle::CtOption;

// The SchnorrAdaptorSignature struct is the schema used over a group (a curve C implementing curve arithmetic)
// and hash functions H (with their output size being the same number of bits as the representation of the field
// elements of C)
// TODO: note here that we are creating PhantomData of C and H. These are variables that are not
//       compiled (zero-sized) but I have included them because otherwise the compiler complains
//       that the generic types C and H are not used even though we require SchnorrAdaptorSignature
//       to be generic. There might be a way to not include PhantomData and make the code cleaner
pub struct SchnorrAdaptorSignature<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    _curve_marker: PhantomData<C>,
    _hash_marker: PhantomData<H>,
}

// TODO: since we are using the <C::ProjectivePoint as Group>::generator() in a few places,
//       we might want to store the generator as g in the SchnorrAdaptorSignature struct.
// TODO: we are creating a new hash everytime we need to hash something (let hasher = H::new())
//       We might want to store the hash function in the struct and the use finalize_reset()
//       function from the digest trait
impl<C, H> AdaptorSignatureScheme for SchnorrAdaptorSignature<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    // TODO: types for the signing and verification key are used as the mathematical objects they
    //       represent. It might be interesting to use the SecretKey and PublicKey types included
    //       in the elliptic_curve trait.
    type SK = NonZeroScalar<C>;
    type PK = C::ProjectivePoint;
    type Witness = NonZeroScalar<C>;
    type Statement = C::ProjectivePoint;
    type PreSignature = SchnorrSignature<C>;
    type Signature = SchnorrSignature<C>;

    fn gen() -> (Self::SK, Self::PK) {
        let sk = Self::SK::random(&mut OsRng);
        let pk = Self::SK::statement(&C::ProjectivePoint::generator(), &sk);
        (sk, pk)
    }

    fn pre_sign(sk: &Self::SK, msg: &str, x: &Self::Statement) -> Self::PreSignature {
        let _r = NonZeroScalar::<C>::random(&mut OsRng);
        let r = _r.as_ref();

        let pk = Self::SK::statement(&C::ProjectivePoint::generator(), sk);
        let g = C::ProjectivePoint::generator();
        let gx = (g * r) + (*x);

        let proj_pk = proj::<C>(&pk);
        let proj_g = proj::<C>(&gx);

        let hasher = H::new();
        let e = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(proj_pk)
                .chain_update(proj_g)
                .chain_update(msg)
                .finalize(),
        );

        let z = *r + (*sk.as_ref()) * e;
        SchnorrSignature::<C> { proof: e, sig: z }
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

    fn pre_verify(
        pk: &Self::PK,
        msg: &str,
        x: &Self::Statement,
        p_sig: &Self::PreSignature,
    ) -> bool {
        let g = C::ProjectivePoint::generator();
        let gx = (g * p_sig.sig) + (*pk * (-p_sig.proof)) + (*x);

        let proj_pk = proj::<C>(pk);
        let proj_g = proj::<C>(&gx);

        let hasher = H::new();
        let e = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(proj_pk)
                .chain_update(proj_g)
                .chain_update(msg)
                .finalize(),
        );

        e == p_sig.proof
    }

    fn adapt(_pk: &Self::PK, p_sig: &Self::PreSignature, w: &Self::Witness) -> Self::Signature {
        let z = p_sig.sig + w.as_ref();
        SchnorrSignature::<C> {
            proof: p_sig.proof,
            sig: z,
        }
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

    fn extract(
        _pk: &Self::PK,
        p_sig: &Self::PreSignature,
        sig: &Self::Signature,
    ) -> CtOption<Self::Witness> {
        NonZeroScalar::<C>::new(sig.sig - p_sig.sig)
    }
}
