use crate::hard_relation::HardRelation;
use crate::identification_scheme::IdentificationScheme;

// and adaptor signature scheme is defined from a signature scheme w.r.t. a hard relation R
pub trait SignatureScheme {
    // The types for the secret and public key. They are related through the HardRelation trait
    // SK is the signing key and PK is the verification key.
    type PK;
    type SK: HardRelation<Self::PK, Self::SK>;
    // The types for the presignature and the signature.
    type Signature;

    fn gen() -> (Self::SK, Self::PK);

    fn sign(sk: &Self::SK, msg: &str) -> Self::Signature;

    fn verify(pk: &Self::PK, msg: &str, sig: &Self::Signature) -> bool;
}

// impl<T> SignatureScheme for T
// where
//     T: IdentificationScheme,
// {
//     type PK = T::PK;
//     type SK = T::SK;
//     type Signature = (T::Commitment, T::Response);
//
//     fn sign(sk: &Self::SK, msg: &str) -> Self::Signature {
//         let (r, st) = T::P1(sk);
//         let h; // hash(R, m)
//         let s = T::P2(sk, &r, h, &st);
//
//         (r, s)
//     }
//
//     fn verify(pk: &Self::PK, msg: &str, sig: &Self::Signature) -> bool {
//         let (r, s) = sig;
//         let h; // hash(R,m)
//
//         T::verify(pk, r, h, s)
//     }
// }
