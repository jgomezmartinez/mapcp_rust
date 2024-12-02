# zkcp\_rust

## Requirements
cargo 1.76.0 (c84b36747 2024-01-18)  
rustc 1.76.0 (07dca489a 2024-02-04)  
GNU Awk 5.1.0, API: 3.0 (GNU MPFR 4.1.0, GNU MP 6.2.1)  

## How to build

For time meassurements:
```
cargo build --release
```

## How to run

To meassure execution time
```
cargo run --bin selling_signature_Secp256k1 --release
cargo run --bin selling_signature_NistP256 --release
cargo run --bin selling_signature_elgamal_Secp256k1 --release
cargo run --bin selling_signature_elgamal_NistP256 --release
cargo run --bin selling_signature_service_Secp256k1 --release
cargo run --bin selling_signature_service_NistP256 --release
```

This will generate csv files with the execution times:
- selling\_signature\_times\_Secp256k1.csv
- selling\_signature\_times\_NistP256.csv
- selling\_signature\_service\_times\_Secp256k1.csv
- selling\_signature\_service\_times\_NistP256.csv

To obtain the mean values, run
```
awk -f compute_mean.awk <file>.csv
```

To meassure communication costs run
```
cargo run --bin selling_signature_Secp256k1
cargo run --bin selling_signature_NistP256
cargo run --bin selling_signature_elgamal_Secp256k1
cargo run --bin selling_signature_elgamal_NistP256
cargo run --bin selling_signature_service_Secp256k1
cargo run --bin selling_signature_service_NistP256
```
each will produce as standard output a message showing the communication costs.


