use elliptic_curve::scalar::NonZeroScalar;
use elliptic_curve::CurveArithmetic;
use k256::sha2::Sha256;
use k256::Secp256k1;
use p256::NistP256;
use schemas::adaptor_signatures::AdaptorSignatureScheme;
use schemas::elgamal::ElGamal;
use schemas::hard_relation::HardRelation;
use schemas::nizk::NIZK;
use schemas::pok_zkcp::{PoKZKCP, Proof, Statement, Witness};
use schemas::public_key_encryption_scheme::PublicKeyEncryptionScheme;
use schemas::schnorr_adaptor_signatures::SchnorrAdaptorSignature;
use schemas::schnorr_signatures::SchnorrSignature;
use schemas::schnorr_signatures::SchnorrSignatureScheme;
use schemas::signature_scheme::SignatureScheme;
use schemas::utils::{bit_at, point_to_byte_vector, proj, scalar_to_byte_vector};
use std::fs::File;
use std::fs::OpenOptions;
use std::io::{BufWriter, Write};
use std::time::Instant;

type C = NistP256;
const CURVE_NAME: &str = "NistP256";

type ASig = SchnorrAdaptorSignature<C, Sha256>;

type Sig = SchnorrSignatureScheme<C, Sha256>;
type Signature = SchnorrSignature<C>;

type DLog = NonZeroScalar<C>;

type Point = <C as CurveArithmetic>::ProjectivePoint;
type Scalar = <C as CurveArithmetic>::Scalar;

type Nizk = PoKZKCP<C, Sha256>;
type Wit = Witness<C>;
type St = Statement<C, Sha256>;

type PKE = ElGamal<C>;
type CypherText = <ElGamal<C> as PublicKeyEncryptionScheme>::CypherText;

fn selling_signature(time_file: &mut BufWriter<File>) {
    let (sk_s_1, pk_s_1) = ASig::gen();
    let (sk_s_2, pk_s_2) = ASig::gen();
    let (sk_b_1, pk_b_1) = ASig::gen();
    let (sk_b_2, pk_b_2) = ASig::gen();
    let (sk_notary, pk_notary) = ASig::gen();

    let tx_lock = "(alpha, pk_b_1) -> (alpha, (pk_b_2 && pk_s) || (pk_b_2 + t))";
    let tx_pay = "(alpha, (pk_b_2 && pk_s) || (pk_b_2 + t)) -> (alpha, pk_s_2)";
    let tx_recover = "(alpha, (pk_b_2 && pk_s) || (pk_b_2 + t)) -> (alpha, pk_b_3)";
    let msg = "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua";

    let g = Point::GENERATOR;

    //--------------------------------------------------------------------------------------
    // SELLER 1
    //--------------------------------------------------------------------------------------
    let start = Instant::now();

    let (w, x) = DLog::gen(&g);
    let signature = Sig::sign(&sk_notary, msg);
    let sig_bytes = scalar_to_byte_vector::<C>(&signature.sig);
    let sig_n_bytes = sig_bytes.len();
    let sig_n_bits = sig_n_bytes * 8;
    let mut elgamal_a = Vec::<Point>::new();
    let mut elgamal_b = Vec::<Point>::new();
    let mut enc_randomness = Vec::<Scalar>::new();
    for i in 0..sig_n_bits {
        let (cti, ri): (CypherText, Scalar) = if bit_at(&sig_bytes, i) == 0 {
            PKE::enc(&x, &Point::IDENTITY)
        } else {
            PKE::enc(&x, &Point::GENERATOR)
        };
        elgamal_a.push(cti.0);
        elgamal_b.push(cti.1);
        enc_randomness.push(ri);
    }
    let witness = Wit {
        sig: signature.sig,
        sk: *sk_notary,
        w: *w,
        elgamal_randomness: enc_randomness,
        sig_bytes: sig_bytes.clone(),
    };
    let statement = St::new(
        pk_notary,
        signature.proof,
        g * signature.sig,
        x,
        elgamal_a.clone(),
        elgamal_b.clone(),
        msg.to_string(),
    );
    let crs = Nizk::crs_gen();
    let proof = Nizk::prove(&crs, &statement, &witness);

    let duration = start.elapsed();

    schemas::debug_print!(
        "seller sends to buyer {} bytes",
        proof.to_byte_vector().len() + statement.to_byte_vector().len()
    );
    let data = format!("{}, ", duration.as_nanos());
    time_file
        .write_all(data.as_bytes())
        .expect("Unable to write to file");

    //--------------------------------------------------------------------------------------
    // BUYER 1
    //--------------------------------------------------------------------------------------
    let start = Instant::now();
    assert!(Nizk::verify(&crs, &statement, &proof));
    let signature_lock = Sig::sign(&sk_b_1, tx_lock);
    assert!(Sig::verify(&pk_b_1, tx_lock, &signature_lock));
    // Publish(tx_lock, sig_lock)
    let pre_signature_pay = ASig::pre_sign(&sk_b_2, tx_pay, &x);
    let duration = start.elapsed();

    let pre_signature_pay_size = pre_signature_pay.to_byte_vector().len();
    let signature_lock_size = signature_lock.to_byte_vector().len();
    schemas::debug_print!("buyer sends to seller {} bytes:", pre_signature_pay_size);
    schemas::debug_print!("\t-pre_sig: {} bytes", pre_signature_pay_size);
    schemas::debug_print!(
        "buyer publishes to blockchain {} bytes:",
        signature_lock_size
    );
    schemas::debug_print!("\t-sig_lock: {} bytes", pre_signature_pay_size);

    let data = format!("{}, ", duration.as_nanos());
    time_file
        .write_all(data.as_bytes())
        .expect("Unable to write to file");

    //--------------------------------------------------------------------------------------
    // SELLER 2
    //--------------------------------------------------------------------------------------
    let start = Instant::now();
    assert!(ASig::pre_verify(&pk_b_2, tx_pay, &x, &pre_signature_pay));
    let signature_pay = ASig::adapt(&pk_b_2, &pre_signature_pay, &w);
    assert!(ASig::verify(&pk_b_2, tx_pay, &signature_pay));
    let duration = start.elapsed();
    // Publish(tx_pay, signature_pay)

    let data = format!("{}, ", duration.as_nanos());
    time_file
        .write_all(data.as_bytes())
        .expect("Unable to write to file");

    let signature_pay_size = signature_pay.to_byte_vector().len();
    schemas::debug_print!(
        "seller publishes to blockchain {} bytes:",
        signature_pay_size
    );
    schemas::debug_print!("\t-sig_lock: {} bytes", signature_pay_size);

    //--------------------------------------------------------------------------------------
    // BUYER 2
    //--------------------------------------------------------------------------------------
    // signature_pay read from ledger
    let start = Instant::now();
    let extracted_w = ASig::extract(&pk_b_2, &pre_signature_pay, &signature_pay).unwrap();
    assert!(*extracted_w == *w);
    let mut byte: u8 = 0;
    let mut first_iteration = true;
    let mut extracted_bytes = Vec::<u8>::new();
    for i in 0..sig_n_bits {
        if i % 8 == 0 && !first_iteration {
            extracted_bytes.push(byte);
            byte = 0;
        }
        byte = byte >> 1;
        let decrypted_point = PKE::dec(&extracted_w, &(elgamal_a[i], elgamal_b[i]));
        if decrypted_point == Point::GENERATOR {
            byte += 128;
        }
        first_iteration = false;
    }
    extracted_bytes.push(byte);
    let duration = start.elapsed();

    let data = format!("{}\n", duration.as_nanos());
    assert!(extracted_bytes == sig_bytes);
    time_file
        .write_all(data.as_bytes())
        .expect("Unable to write to file");
}

fn main() {
    let times_file_name = String::from("selling_signature_elgamal_times_") + CURVE_NAME + ".csv";
    let time_file = OpenOptions::new()
        .append(true)
        .create(true)
        .open(times_file_name)
        .expect("Unable to open the file");
    let mut time_file = BufWriter::new(time_file);

    #[cfg(debug_assertions)]
    {
        selling_signature(&mut time_file);
    }
    #[cfg(not(debug_assertions))]
    {
        for _ in 1..1000 {
            selling_signature(&mut time_file);
        }
    }
}
