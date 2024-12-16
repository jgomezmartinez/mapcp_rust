use elliptic_curve::point::AffineCoordinates;
use elliptic_curve::FieldBytes;
use elliptic_curve::{AffinePoint, CurveArithmetic};

#[macro_export]
macro_rules! debug_print {
    ($($e:expr),+) => {
        {
            #[cfg(debug_assertions)]
            {
                println!($($e),+)
            }
            #[cfg(not(debug_assertions))]
            {
                {}
            }
        }
    };
}

// auxiliary function used to get an object that can be represented into an array of bytes from a
// projective point.
// TODO: maybe find a better way to turn a ProjectivePoint into an array of bytes (by using
//       functions of the elliptic_curve library).
pub fn proj<C: CurveArithmetic>(
    point: &C::ProjectivePoint,
) -> <<C as CurveArithmetic>::AffinePoint as AffineCoordinates>::FieldRepr {
    let affine: AffinePoint<C> = (*point).into();
    affine.x()
}

pub fn point_to_byte_vector<C: CurveArithmetic>(point: &C::ProjectivePoint) -> Vec<u8> {
    let affine_point: AffinePoint<C> = (*point).into();
    let point_array = Into::<FieldBytes<C>>::into(affine_point.x());
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(point_array.as_slice());
    v.push(affine_point.y_is_odd().unwrap_u8());

    v
}

pub fn scalar_to_byte_vector<C: CurveArithmetic>(scalar: &C::Scalar) -> Vec<u8> {
    let array = Into::<FieldBytes<C>>::into(*scalar);
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(array.as_slice());

    v
}

pub fn ith_bit(bytes: &Vec<u8>, i: usize) -> u8 {
    let n_bits = 8 * bytes.len();
    let index_be = n_bits - i - 1;
    let byte_index = index_be / 8;
    let bit_index = 7 - (index_be % 8);
    let byte = bytes[byte_index];
    let mask = 1 << bit_index;

    if (mask & byte) > 0 {
        1
    } else {
        0
    }
}

pub fn bit_at(bytes: &Vec<u8>, i: usize) -> u8 {
    let mask = 1 << (i % 8);
    if (mask & bytes[i / 8]) > 0 {
        1
    } else {
        0
    }
    //(bytes[i / 8] >> (i % 8)) & 1
}

pub fn set_bit_at(byte: &mut u8, i: usize, val: bool) {
    let bit_index = i % 8;
    if val {
        let mask = 1 << bit_index;
        *byte |= mask;
    } else {
        let mask = !(1 << bit_index);
        *byte &= mask;
    }
}
