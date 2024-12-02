use elliptic_curve::CurveArithmetic;
use elliptic_curve::Group;
use elliptic_curve::NonZeroScalar;
use rand_core::OsRng;

pub trait HardRelation<S, W> {
    type PP;
    // given a Witness w and a Statement s, return true if (w;s) is in relation R
    #[allow(non_snake_case)]
    fn R(pp: &Self::PP, w: &W, x: &S) -> bool;
    // From a Witness w, compute a Statement s such that R(w, s) == true
    fn statement(pp: &Self::PP, w: &W) -> S;
    fn gen(pp: &Self::PP) -> (W, S);
}

// hard relation R where given a witness w in a PrimeField W (for example Integers modulo q, with q prime)
// and given a statement x in a group S, we say that w is a witness of x if:
// R(w;x) == 1  iff  x = g^w
// impl<S, W> HardRelation<S, W> for W
// where
//     S: Group + ScalarMul<W>,
//     W: PrimeField,
// {
//     fn R(w: &W, x: &S) -> bool {
//         S::generator() * (*w) == *x
//     }
//     fn statement(w: &W) -> S {
//         S::generator() * (*w)
//     }
//     fn gen() -> (W, S) {
//         let w = W::random(&mut OsRng);
//         let x = Self::statement(&w);
//
//         (w, x)
//     }
// }

impl<C> HardRelation<C::ProjectivePoint, NonZeroScalar<C>> for NonZeroScalar<C>
where
    C: CurveArithmetic,
{
    type PP = C::ProjectivePoint;

    fn R(pp: &Self::PP, w: &NonZeroScalar<C>, x: &C::ProjectivePoint) -> bool {
        *pp * w.as_ref() == *x
    }
    fn statement(pp: &Self::PP, w: &NonZeroScalar<C>) -> C::ProjectivePoint {
        *pp * w.as_ref()
    }
    fn gen(pp: &Self::PP) -> (NonZeroScalar<C>, C::ProjectivePoint) {
        let w = NonZeroScalar::<C>::random(&mut OsRng);
        let x = Self::statement(pp, &w);

        (w, x)
    }
}
