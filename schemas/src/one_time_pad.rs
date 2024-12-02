use crate::symmetric_encryption::SymmetricEncryptionScheme;
use elliptic_curve::ops::Add;
use elliptic_curve::ops::Sub;
use std::marker::PhantomData;

pub struct OneTimePad<C>
where
    C: Sized + Add<Output = C> + Sub<Output = C>,
{
    _element_marker: PhantomData<C>,
}

impl<C> SymmetricEncryptionScheme for OneTimePad<C>
where
    C: Sized + Copy + Add<Output = C> + Sub<Output = C> + for<'a> Add<&'a C> + for<'a> Sub<&'a C>,
{
    type Key = C;
    type Message = C;
    type CypherText = C;

    fn enc(key: &Self::Key, msg: &Self::Message) -> Self::CypherText {
        *msg + *key
    }
    fn dec(key: &Self::Key, ct: &Self::CypherText) -> Self::Message {
        *ct - *key
    }
}
