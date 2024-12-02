pub trait SymmetricEncryptionScheme {
    type Key;
    type Message;
    type CypherText;

    fn enc(key: &Self::Key, msg: &Self::Message) -> Self::CypherText;
    fn dec(sk: &Self::Key, ct: &Self::CypherText) -> Self::Message;
}
