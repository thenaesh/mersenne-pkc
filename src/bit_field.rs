use std::vec::Vec;
use std::iter::Iterator;
use gmp::mpz::Mpz;

use crate::finite_ring::FiniteRing;

#[derive(Debug, Clone)]
pub enum BitField {
    Sparse(usize, Vec<usize>, FiniteRing), // bitstring length, set bits, offset (for O(1) shifting)
    Dense(usize, Mpz), // bitstring length, optimized bitstring
}

impl BitField {
    pub fn new_sparse(n: usize) -> BitField {
        BitField::Sparse(n, Vec::new(), FiniteRing::new(n, 0))
    }

    pub fn new_sparse_from_str(s: &str) -> BitField {
        let n = s.len();
        let mut vec = Vec::new();
        let offset = FiniteRing::new(n, 0);

        for (i, c) in s.chars().rev().enumerate() {
            if c != '0' {
                vec.push(i);
            }
        }

        BitField::Sparse(n, vec, offset)
    }

    pub fn new_dense_from_str(s: &str) -> BitField {
        let n = s.len();
        let mut bitstring = Mpz::new_reserve(n);

        for (i, c) in s.chars().rev().enumerate() {
            if c != '0' {
                bitstring.setbit(i);
            }
        }

        BitField::Dense(n, bitstring)
    }

    pub fn new_dense(n: usize) -> BitField {
        BitField::Dense(n, Mpz::new_reserve(n))
    }

    pub fn sparse_to_dense(self: &BitField) -> BitField {
        match self {
            BitField::Dense(_, _) => self.clone(),
            BitField::Sparse(n, vec, offset) => {
                let mut bitstring = Mpz::new_reserve(*n);

                for idx in vec.iter().map(|x| (FiniteRing::new(*n, *x) + *offset).val) {
                    bitstring.setbit(idx);
                }

                BitField::Dense(*n, bitstring)
            }
        }
    }

    pub fn dense_to_sparse(self: &BitField) -> BitField {
        match self {
            BitField::Sparse(_, _, _) => self.clone(),
            BitField::Dense(n, bitstring) => {
                let mut vec = Vec::new();
                let offset = FiniteRing::new(*n, 0);

                for idx in 0..*n {
                    if bitstring.tstbit(idx) {
                        vec.push(idx);
                    }
                }

                BitField::Sparse(*n, vec, offset)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::finite_ring::FiniteRing;
    use crate::bit_field::BitField;
    use crate::bit_field::BitField::*;

    #[test]
    fn construct_sparse_field_from_string() {
        let string = "10010";
        if let Sparse(n, vec, offset) = BitField::new_sparse_from_str(string) {
            assert_eq!(n, string.len());
            assert_eq!(offset, FiniteRing::new(n, 0));
            assert_eq!(vec.len(), 2);
            assert!(vec.contains(&1));
            assert!(vec.contains(&4));
        } else {
            panic!("Sparse field expected but dense field encountered!");
        }
    }

    #[test]
    fn construct_dense_field_from_string() {
        let string = "10010";
        if let Dense(n, bitstring) = BitField::new_dense_from_str(string) {
            assert_eq!(n, string.len());
            for i in 0..n {
                assert_eq!(bitstring.tstbit(i), i == 1 || i == 4);
            }
        } else {
            panic!("Dense field expected but sparse field encountered!");
        }
    }
}
