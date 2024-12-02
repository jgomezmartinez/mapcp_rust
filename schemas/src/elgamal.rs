use crate::hard_relation::HardRelation;
use crate::public_key_encryption_scheme::PublicKeyEncryptionScheme;
use elliptic_curve::scalar::NonZeroScalar;
use elliptic_curve::CurveArithmetic;
use elliptic_curve::Group;
use rand_core::OsRng;
use std::marker::PhantomData;

pub struct ElGamal<C>
where
    C: CurveArithmetic,
{
    _curve_marker: PhantomData<C>,
}

impl<C> PublicKeyEncryptionScheme for ElGamal<C>
where
    C: CurveArithmetic,
{
    type PK = C::ProjectivePoint;
    type SK = NonZeroScalar<C>;
    type Message = C::ProjectivePoint;
    type CypherText = (C::ProjectivePoint, C::ProjectivePoint);
    type Randomness = C::Scalar;

    fn gen() -> (Self::SK, Self::PK) {
        Self::SK::gen(&C::ProjectivePoint::generator())
    }

    fn enc(pk: &Self::PK, msg: &Self::Message) -> (Self::CypherText, Self::Randomness) {
        let nz_y = NonZeroScalar::<C>::random(&mut OsRng);
        let y = nz_y.as_ref();
        let s = (*pk) * (*y);
        let g = C::ProjectivePoint::generator();

        ((g * y, s + msg), *y)
    }
    fn dec(sk: &Self::SK, ct: &Self::CypherText) -> Self::Message {
        let (a, b) = ct;
        let sk = sk.as_ref();
        let msg = *b - *a * *sk;

        msg
    }
}
