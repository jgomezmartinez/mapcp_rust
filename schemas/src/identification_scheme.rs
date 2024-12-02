use crate::hard_relation::HardRelation;

#[rustfmt::skip]
#[allow(non_snake_case)]
pub trait IdentificationScheme {
    // The types for the secret and public key. They are related through the HardRelation trait
    type PK;
    type SK: HardRelation<Self::PK, Self::SK>;
    type Challenge;
    type Commitment;
    type State;
    type Response;
    
    fn P1(sk: &Self::SK) -> (Self::Commitment, Self::State);
    fn P2(sk: &Self::SK, R: &Self::Commitment, h: &Self::Challenge, st: &Self::State) -> Self::Response;
    fn verify(pk: &Self::PK, R: &Self::Commitment, h: &Self::Challenge, s: &Self::Response) -> bool;
}
