use crate::nizk::NIZK;
use crate::utils::proj;
use digest::Digest;
use elliptic_curve::ops::Reduce;
use elliptic_curve::scalar::NonZeroScalar;
use elliptic_curve::{CurveArithmetic, Group};
use rand_core::OsRng;
use std::marker::PhantomData;

pub struct DLogSigmaProof<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    _curve_marker: PhantomData<C>,
    _hash_marker: PhantomData<H>,
}

impl<C, H> NIZK for DLogSigmaProof<C, H>
where
    C: CurveArithmetic,
    H: Digest<OutputSize = C::FieldBytesSize>,
{
    type CRS = C::ProjectivePoint;
    type Statement = C::ProjectivePoint;
    type Witness = NonZeroScalar<C>;
    type Proof = (C::ProjectivePoint, C::Scalar);

    fn crs_gen() -> Self::CRS {
        Self::CRS::generator()
    }

    fn prove(crs: &Self::CRS, x: &Self::Statement, w: &Self::Witness) -> Self::Proof {
        let u = Self::Witness::random(&mut OsRng);
        let a = (*crs) * u.as_ref();

        let proj_a = proj::<C>(&a);
        let proj_x = proj::<C>(x);
        let proj_g = proj::<C>(crs);

        let hasher = H::new();
        let c = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(proj_g)
                .chain_update(proj_x)
                .chain_update(proj_a)
                .finalize(),
        );

        let r = (*u.as_ref()) + c * w.as_ref();

        (a, r)
    }

    fn verify(crs: &Self::CRS, x: &Self::Statement, p: &Self::Proof) -> bool {
        let (a, r) = *p;

        let proj_a = proj::<C>(&a);
        let proj_x = proj::<C>(x);
        let proj_g = proj::<C>(crs);

        let hasher = H::new();
        let c = <C::Scalar as Reduce<C::Uint>>::reduce_bytes(
            &hasher
                .chain_update(proj_g)
                .chain_update(proj_x)
                .chain_update(proj_a)
                .finalize(),
        );

        (Self::CRS::generator() * r) == a + ((*x) * c)
    }
}
