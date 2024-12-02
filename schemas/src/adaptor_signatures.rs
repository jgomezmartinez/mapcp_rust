use crate::hard_relation::HardRelation;
use subtle::CtOption;

// and adaptor signature scheme is defined from a signature scheme w.r.t. a hard relation R
pub trait AdaptorSignatureScheme {
    // The types for the secret and public key. They are related through the HardRelation trait
    // SK is the signing key and PK is the verification key.
    type PK;
    type SK: HardRelation<Self::PK, Self::SK>;
    // The types of Witness and Statement of the hard relation R. They are related throught the
    // HardRelation trait.
    type Statement;
    type Witness: HardRelation<Self::Statement, Self::Witness>;
    // The types for the presignature and the signature.
    type PreSignature;
    type Signature;

    fn gen() -> (Self::SK, Self::PK);

    fn pre_sign(sk: &Self::SK, msg: &str, x: &Self::Statement) -> Self::PreSignature;
    fn sign(sk: &Self::SK, msg: &str) -> Self::Signature;

    fn pre_verify(
        pk: &Self::PK,
        msg: &str,
        x: &Self::Statement,
        p_sig: &Self::PreSignature,
    ) -> bool;

    fn adapt(pk: &Self::PK, p_sig: &Self::PreSignature, w: &Self::Witness) -> Self::Signature;

    fn verify(pk: &Self::PK, msg: &str, sig: &Self::Signature) -> bool;

    fn extract(
        pk: &Self::PK,
        p_sig: &Self::PreSignature,
        sig: &Self::Signature,
    ) -> CtOption<Self::Witness>;
}
