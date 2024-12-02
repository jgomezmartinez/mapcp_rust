use crate::hard_relation::HardRelation;

pub trait NIZK {
    type CRS;
    type Statement;
    type Witness: HardRelation<Self::Statement, Self::Witness>;
    type Proof;

    fn crs_gen() -> Self::CRS;
    fn prove(crs: &Self::CRS, x: &Self::Statement, w: &Self::Witness) -> Self::Proof;
    fn verify(crs: &Self::CRS, x: &Self::Statement, p: &Self::Proof) -> bool;
}
