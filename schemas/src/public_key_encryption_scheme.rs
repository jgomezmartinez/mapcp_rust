pub trait PublicKeyEncryptionScheme {
    type PK;
    type SK;
    type Message;
    type CypherText;
    type Randomness;

    fn gen() -> (Self::SK, Self::PK);
    fn enc(pk: &Self::PK, msg: &Self::Message) -> (Self::CypherText, Self::Randomness);
    fn dec(sk: &Self::SK, ct: &Self::CypherText) -> Self::Message;
}
