pub mod adaptor_signatures;
pub mod ecdsa_signatures;
pub mod hard_relation;
pub mod identification_scheme;
pub mod nizk;
pub mod pedersen_commitment;
pub mod proof_f;
pub mod proof_phi;
// pub mod proof_star;
pub mod elgamal;
pub mod one_time_pad;
pub mod pok_schnorr_signature;
pub mod pok_zkcp;
pub mod por_schnorr_signature;
pub mod public_key_encryption_scheme;
pub mod schnorr_adaptor_signatures;
pub mod schnorr_signatures;
pub mod sigma_proof;
pub mod signature_scheme;
pub mod symmetric_encryption;
pub mod utils;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
