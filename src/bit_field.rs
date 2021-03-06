use std::vec::Vec;
use std::collections::HashSet;
use std::cmp::{min, max};
use std::iter::Iterator;
use std::ops::Index;
use std::ops::{ShlAssign, ShrAssign, AddAssign, SubAssign, MulAssign, DivAssign};
use std::fmt::Display;
use gmp::mpz::Mpz;
use rand::Rng;

use crate::finite_ring::FiniteRing;

#[derive(Debug, Clone)]
pub enum BitField {
    Sparse(usize, Vec<usize>, FiniteRing), // bitstring length, set bits, offset (for O(1) shifting)
    Dense(usize, Mpz), // bitstring length, optimized bitstring
}

type SparseContents<'a> = (usize, &'a Vec<usize>, FiniteRing);
type DenseContents<'a> = (usize, &'a Mpz);

type SparseContentsMut<'a> = (usize, &'a mut Vec<usize>, FiniteRing);
type DenseContentsMut<'a> = (usize, &'a mut Mpz);

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

    pub fn new_uniform_random(n: usize, hamming_weight: usize) -> BitField {
        let mut rng = rand::thread_rng();
        let mut vec = Vec::<usize>::with_capacity(hamming_weight);

        let mut i = 0;
        while i < hamming_weight {
            let rand_idx = rng.gen::<usize>() % n;
            if vec.contains(&rand_idx) {
                continue;
            } else {
                i += 1;
                vec.push(rand_idx);
            }
        }

        vec.sort_unstable();

        BitField::Sparse(n, vec, FiniteRing::new(n, 0))
    }

    pub fn as_dense(self: &BitField) -> BitField {
        match self {
            BitField::Dense(_, _) => self.clone(),
            BitField::Sparse(n, vec, offset) => {
                let mut bitstring = Mpz::new_reserve(*n);

                for idx in vec.iter().map(|x| (FiniteRing::new(*n, *x) - *offset).val) {
                    bitstring.setbit(idx);
                }

                BitField::Dense(*n, bitstring)
            }
        }
    }

    pub fn as_sparse(self: &BitField) -> BitField {
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

    pub fn make_dense(self: &mut Self) {
        if let BitField::Sparse(..) = self {
            *self = self.as_dense();
        }
    }

    pub fn make_sparse(self: &mut Self) {
        if let BitField::Dense(..) = self {
            *self = self.as_sparse();
        }
    }

    pub fn is_dense(self: &Self) -> bool {
        match self {
            BitField::Dense(..) => true,
            BitField::Sparse(..) => false,
        }
    }

    pub fn is_sparse(self: &Self) -> bool {
        match self {
            BitField::Dense(..) => false,
            BitField::Sparse(..) => true,
        }
    }

    pub fn unwrap_dense<'a>(self: &'a BitField) -> DenseContents<'a> {
        if let BitField::Dense(n, bitstring) = self {
            (*n, bitstring)
        } else {
            panic!("Unwrapping BitField as dense failed!");
        }
    }

    pub fn unwrap_sparse<'a>(self: &'a BitField) -> SparseContents<'a> {
        if let BitField::Sparse(n, vec, offset) = self {
            (*n, vec, *offset)
        } else {
            panic!("Unwrapping BitField as sparse failed!");
        }
    }

    pub fn unwrap_dense_mut<'a>(self: &'a mut BitField) -> DenseContentsMut<'a> {
        if let BitField::Dense(n, bitstring) = self {
            (*n, bitstring)
        } else {
            panic!("Unwrapping BitField as dense failed!");
        }
    }

    pub fn unwrap_sparse_mut<'a>(self: &'a mut BitField) -> SparseContentsMut<'a> {
        if let BitField::Sparse(n, vec, offset) = self {
            (*n, vec, *offset)
        } else {
            panic!("Unwrapping BitField as sparse failed!");
        }
    }

    pub fn extend(mut self: Self, k: usize) -> Self {
        self.normalize();
        match self {
            BitField::Dense(n, bitstring) => BitField::Dense(n+k, bitstring),
            BitField::Sparse(n, vec, _) => BitField::Sparse(n+k, vec, FiniteRing::new(n+k, 0)),
        }
    }

    pub fn extend_self(self: &mut Self, k: usize) {
        self.normalize();
        match self {
            BitField::Dense(n, bitstring) => {
                *n += k;
            },
            BitField::Sparse(n, vec, modulus) => {
                *n += k;
                *modulus = FiniteRing::new(*n + k, 0);
            },
        }
    }

    pub fn set(self: &mut Self, idx: usize) {
        match self {
            BitField::Sparse(n, vec, offset) => {
                let real_idx = (FiniteRing::new(*n, idx) + *offset).val;
                if !vec.contains(&real_idx) {
                    vec.push(real_idx);
                }
            },
            BitField::Dense(_, bitstring) => {
                bitstring.setbit(idx);
            },
        }
    }

    pub fn len(self: &Self) -> usize {
        match self {
            BitField::Sparse(n, ..) => *n,
            BitField::Dense(n, ..) => *n,
        }
    }

    pub fn normalize(self: &mut Self) {
        match self {
            BitField::Dense(..) => {},
            BitField::Sparse(_, vec, FiniteRing { modulus: _, val: 0 }) => {
                vec.sort_unstable();
            },
            BitField::Sparse(n, vec, offset) => {
                for i in 0..vec.len() {
                    let x = FiniteRing::new(*n, vec[i]) - *offset;
                    vec[i] = x.val;
                }
                *offset = FiniteRing::new(*n, 0);
                vec.sort_unstable();
            }
        }
    }

    pub fn hamming_weight(self: &Self) -> usize {
        match self {
            BitField::Sparse(_, vec, _) => vec.len(),
            BitField::Dense(n, bitfield) => {
                let mut count = 0;
                for i in 0..*n {
                    if bitfield.tstbit(i) {
                        count += 1;
                    }
                }
                count
            }
        }
    }

    pub fn all_set_bits(self: &Self) -> Vec<usize> {
        let mut vec = match self {
            BitField::Sparse(n, vec, offset) => vec.iter().map(|x| (FiniteRing::new(*n, *x) - *offset).val).collect(),
            BitField::Dense(n, bitstring) => {
                let mut vec = Vec::new();
                for i in 0..*n {
                    if bitstring.tstbit(i) {
                        vec.push(i);
                    }
                }
                vec
            }
        };

        vec.sort_unstable();
        vec
    }

    pub fn all_set_bits_hashset(self: &Self) -> HashSet<usize> {
        let vec = self.all_set_bits();
        let mut hashset = HashSet::new();
        for i in vec {
            hashset.insert(i);
        }
        hashset
    }

    /*
     * PRECONDITIONS:
     * 1) minuend must be greater than or equal to subtrahend
     * 2) minuend must be sparse and normalized
     * 3) subtrahend must be sparse and normalized
     *
     * Note that self is the minuend and other is the subtrahend.
     */
    pub fn hamming_weight_change_upon_subtraction(self: &Self, other: Self) -> i64 {
        let (n, minuend_vec, _) = self.unwrap_sparse();
        let (m, subtrahend_vec, _) = other.unwrap_sparse();

        if n != m {
            panic!("Bitstrings of different length unexpected!");
        }

        let l = subtrahend_vec.len();
        let mut stop_mark = n;
        let mut skip_marks = HashSet::<usize>::new();

        let mut delta = 0 as i64;

        for i in 0..l {
            let i = l - 1 - i;

            let idx = subtrahend_vec[i];
            match minuend_vec.binary_search(&idx) {
                Ok(_) => {
                    // minuend[idx] = 1, subtrahend[idx] = 1
                    delta -= 1;
                    skip_marks.insert(idx);
                },
                Err(j) => {
                    // minuend[idx] = 0, subtrahend[idx] = 1
                    let mut j = j;
                    while skip_marks.contains(&minuend_vec[j]) {
                        j += 1;
                    }

                    let minuend_idx = min(minuend_vec[j], stop_mark) as i64;
                    let subtrahend_idx = idx as i64;

                    delta += minuend_idx - subtrahend_idx - 1;
                    stop_mark = idx as usize;
                },
            }
        }

        -delta
    }
}

impl Display for BitField {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let n = self.len();

        let mut bitvec: Vec<char> = Vec::with_capacity(n);
        for i in 0..n {
            bitvec.push(if self[i] { '1' } else { '0' });
        }

        let mut bitstring = String::new();
        for c in bitvec.iter().rev() {
            bitstring.push(*c);
        }

        write!(f, "{}", bitstring)
    }
}

impl Index<usize> for BitField {
    type Output = bool;

    fn index<'a>(self: &'a Self, idx: usize) -> &'a Self::Output {
        match self {
            BitField::Sparse(n, vec, offset) => {
                let real_idx = (FiniteRing::new(*n, idx) + *offset).val;
                if vec.contains(&real_idx) { &true } else { &false }
            },
            BitField::Dense(_, bitstring) => {
                if bitstring.tstbit(idx) { &true } else { &false }
            },
        }
    }
}

impl ShlAssign<usize> for BitField {
    fn shl_assign(&mut self, k: usize) {
        match self {
            BitField::Sparse(n, vec, offset) => { *offset = *offset - FiniteRing::new(*n, k); },
            BitField::Dense(n, bitstring) => { *bitstring <<= k; }
        }
    }
}

impl ShrAssign<usize> for BitField {
    fn shr_assign(&mut self, k: usize) {
        match self {
            BitField::Sparse(n, vec, offset) => { *offset = *offset + FiniteRing::new(*n, k); },
            BitField::Dense(n, bitstring) => { *bitstring >>= k; }
        }
    }
}

impl<'a> AddAssign<&'a BitField> for BitField {
    fn add_assign(self: &mut Self, other: &Self) {
        self.make_dense();
        let other = other.as_dense();

        let (n, self_bitstring) = self.unwrap_dense_mut();
        let (m, other_bitstring) = other.unwrap_dense();

        if n != m {
            panic!("Adding BitFields of different lengths!");
        }

        let mut p = Mpz::new_reserve(n);
        for i in 0..n {
            p.setbit(i);
        }

        *self_bitstring += other_bitstring;
        *self_bitstring %= &p;
    }
}

impl<'a> SubAssign<&'a BitField> for BitField {
    fn sub_assign(self: &mut Self, other: &Self) {
        self.make_dense();
        let other = other.as_dense();

        let (n, self_bitstring) = self.unwrap_dense_mut();
        let (m, other_bitstring) = other.unwrap_dense();

        if n != m {
            panic!("Adding BitFields of different lengths!");
        }

        let mut p = Mpz::new_reserve(n);
        for i in 0..n {
            p.setbit(i);
        }

        *self_bitstring -= other_bitstring;
        *self_bitstring += &p;
        *self_bitstring %= &p;
    }
}

impl<'a> MulAssign<&'a BitField> for BitField {
    fn mul_assign(self: &mut Self, other: &Self) {
        self.make_dense();
        let other = other.as_dense();

        let (n, self_bitstring) = self.unwrap_dense_mut();
        let (m, other_bitstring) = other.unwrap_dense();

        if n != m {
            panic!("Adding BitFields of different lengths!");
        }

        let mut p = Mpz::new_reserve(n);
        for i in 0..n {
            p.setbit(i);
        }

        *self_bitstring *= other_bitstring;
        *self_bitstring %= &p;
    }
}

impl<'a> DivAssign<&'a BitField> for BitField {
    fn div_assign(self: &mut Self, other: &Self) {
        self.make_dense();
        let other = other.as_dense();

        let (n, self_bitstring) = self.unwrap_dense_mut();
        let (m, other_bitstring) = other.unwrap_dense();

        if n != m {
            panic!("Adding BitFields of different lengths!");
        }

        let mut p = Mpz::new_reserve(n);
        for i in 0..n {
            p.setbit(i);
        }

        *self_bitstring *= other_bitstring.invert(&p).unwrap();
        *self_bitstring %= &p;
    }
}

#[cfg(test)]
mod tests {
    use crate::finite_ring::FiniteRing;
    use crate::bit_field::BitField;

    #[test]
    fn construct_sparse_field_from_string() {
        let string = "10010";
        let field = BitField::new_sparse_from_str(string);
        let (n, vec, offset) = field.unwrap_sparse();
        assert_eq!(n, string.len());
        assert_eq!(offset, FiniteRing::new(n, 0));
        assert_eq!(vec.len(), 2);
        assert!(vec.contains(&1));
        assert!(vec.contains(&4));
    }

    #[test]
    fn construct_dense_field_from_string() {
        let string = "10010";
        let field = BitField::new_dense_from_str(string);
        let (n, bitstring) = field.unwrap_dense();
        assert_eq!(n, string.len());
        for i in 0..n {
            assert_eq!(bitstring.tstbit(i), i == 1 || i == 4);
        }
    }

    #[test]
    fn display() {
        let string = "10010";
        let sparse_field = BitField::new_sparse_from_str(string);
        let dense_field = BitField::new_dense_from_str(string);

        assert_eq!(string, sparse_field.to_string());
        assert_eq!(string, dense_field.to_string());
    }

    #[test]
    fn index_sparse_without_offset() {
        let string = "10010";
        let field = BitField::new_sparse_from_str(string);
        assert_eq!(field[0], false);
        assert_eq!(field[1], true);
        assert_eq!(field[2], false);
        assert_eq!(field[3], false);
        assert_eq!(field[4], true);
    }

    #[test]
    fn index_sparse_with_offset() {
        let string = "10010";
        let mut field = BitField::new_sparse_from_str(string);
        field <<= 1;
        assert_eq!(field[0], true);
        assert_eq!(field[1], false);
        assert_eq!(field[2], true);
        assert_eq!(field[3], false);
        assert_eq!(field[4], false);
        field <<= 2;
        assert_eq!(field[0], false);
        assert_eq!(field[1], false);
        assert_eq!(field[2], true);
        assert_eq!(field[3], false);
        assert_eq!(field[4], true);
        field >>= 4;
        assert_eq!(field[0], true);
        assert_eq!(field[1], false);
        assert_eq!(field[2], false);
        assert_eq!(field[3], true);
        assert_eq!(field[4], false);
    }

    #[test]
    fn index_dense() {
        let string = "10010";
        let field = BitField::new_dense_from_str(string);
        assert_eq!(field[0], false);
        assert_eq!(field[1], true);
        assert_eq!(field[2], false);
        assert_eq!(field[3], false);
        assert_eq!(field[4], true);
    }

    #[test]
    fn sparse_to_dense_without_offset() {
        let sparse_field = BitField::new_sparse_from_str("10010");
        let dense_field = sparse_field.as_dense();
        assert_eq!(dense_field.to_string(), "10010");
    }

    #[test]
    fn sparse_to_dense_with_offset() {
        let mut sparse_field = BitField::new_sparse_from_str("10010");
        sparse_field >>= 1;
        let dense_field = sparse_field.as_dense();
        assert_eq!(dense_field.to_string(), "01001");
        sparse_field >>= 1;
        let dense_field = sparse_field.as_dense();
        assert_eq!(dense_field.to_string(), "10100");
        sparse_field <<= 2;
        let dense_field = sparse_field.as_dense();
        assert_eq!(dense_field.to_string(), "10010");
    }

    #[test]
    fn dense_to_sparse() {
        let dense_field = BitField::new_dense_from_str("10010");
        let sparse_field = dense_field.as_sparse();
        assert_eq!(sparse_field.to_string(), "10010");
    }

    #[test]
    fn add_assign_without_overflow() {
        let mut x = BitField::new_sparse_from_str("101");
        let y = BitField::new_sparse_from_str("001");
        x += &y;
        assert_eq!(x.to_string(), "110");
    }

    #[test]
    fn add_assign_with_overflow() {
        let mut x = BitField::new_sparse_from_str("101");
        let y = BitField::new_sparse_from_str("110");
        x += &y;
        assert_eq!(x.to_string(), "100");
    }

    #[test]
    fn sub_assign_without_overflow() {
        let mut x = BitField::new_sparse_from_str("101");
        let y = BitField::new_sparse_from_str("010");
        x -= &y;
        assert_eq!(x.to_string(), "011");
        let mut x = BitField::new_sparse_from_str("11001");
        let y = BitField::new_sparse_from_str("10011");
        x -= &y;
        assert_eq!(x.to_string(), "00110");
    }

    #[test]
    fn sub_assign_with_overflow() {
        let mut x = BitField::new_sparse_from_str("001");
        let y = BitField::new_sparse_from_str("101");
        x -= &y;
        assert_eq!(x.to_string(), "011");
        let mut x = BitField::new_sparse_from_str("01001");
        let y = BitField::new_sparse_from_str("10011");
        x -= &y;
        assert_eq!(x.to_string(), "10101");
        let mut x = BitField::new_sparse_from_str("10101");
        let y = BitField::new_sparse_from_str("00101");
        x -= &y;
        assert_eq!(x.to_string(), "10000");
    }

    #[test]
    fn mul_assign_without_overflow() {
        let mut x = BitField::new_sparse_from_str("01000");
        let y = BitField::new_sparse_from_str("00011");
        x *= &y;
        assert_eq!(x.to_string(), "11000");
    }

    #[test]
    fn mul_assign_with_overflow() {
        let mut x = BitField::new_sparse_from_str("11000");
        let y = BitField::new_sparse_from_str("00011");
        x *= &y;
        assert_eq!(x.to_string(), "01010");
    }

    #[test]
    fn div_assign_without_overflow() {
        let mut x = BitField::new_sparse_from_str("110");
        let y = BitField::new_sparse_from_str("011");
        x /= &y;
        assert_eq!(x.to_string(), "010");
        let mut x = BitField::new_sparse_from_str("11000");
        let y = BitField::new_sparse_from_str("00100");
        x /= &y;
        assert_eq!(x.to_string(), "00110");
    }

    #[test]
    fn div_assign_with_overflow() {
        let mut x = BitField::new_sparse_from_str("110");
        let y = BitField::new_sparse_from_str("100");
        x /= &y;
        assert_eq!(x.to_string(), "101");
        let mut x = BitField::new_sparse_from_str("11001");
        let y = BitField::new_sparse_from_str("10011");
        x /= &y;
        assert_eq!(x.to_string(), "10000");
    }

    #[test]
    fn hamming_weight() {
        let x = BitField::new_sparse_from_str("110");
        let y = BitField::new_sparse_from_str("11101010");
        let z = BitField::new_sparse_from_str("11000111010101");
        let w = BitField::new_sparse_from_str("1101111");
        assert_eq!(x.hamming_weight(), 2);
        assert_eq!(y.hamming_weight(), 5);
        assert_eq!(z.hamming_weight(), 8);
        assert_eq!(w.hamming_weight(), 6);
    }


    #[test]
    fn all_set_bits() {
        let mut x = BitField::new_sparse_from_str("11011");
        let vec = x.all_set_bits();
        assert_eq!(vec.len(), 4);
        assert_eq!(vec[0], 0);
        assert_eq!(vec[1], 1);
        assert_eq!(vec[2], 3);
        assert_eq!(vec[3], 4);
        x <<= 1;
        let vec = x.all_set_bits();
        assert_eq!(vec.len(), 4);
        assert_eq!(vec[0], 0);
        assert_eq!(vec[1], 1);
        assert_eq!(vec[2], 2);
        assert_eq!(vec[3], 4);
    }

    #[test]
    fn normalize() {
        let mut x = BitField::new_sparse_from_str("11011");
        let vec = x.all_set_bits();
        x.normalize();
        assert_eq!(vec.len(), 4);
        assert_eq!(vec[0], 0);
        assert_eq!(vec[1], 1);
        assert_eq!(vec[2], 3);
        assert_eq!(vec[3], 4);
        x <<= 1;
        let vec = x.all_set_bits();
        assert_eq!(vec.len(), 4);
        assert_eq!(vec[0], 0);
        assert_eq!(vec[1], 1);
        assert_eq!(vec[2], 2);
        assert_eq!(vec[3], 4);
        x.normalize();
        let vec = x.all_set_bits();
        assert_eq!(vec.len(), 4);
        assert_eq!(vec[0], 0);
        assert_eq!(vec[1], 1);
        assert_eq!(vec[2], 2);
        assert_eq!(vec[3], 4);
    }

    #[test]
    fn new_uniform_random() {
        for _ in 0..1000 {
            let x = BitField::new_uniform_random(44497, 128);
            assert_eq!(x.hamming_weight(), 128);
        }
    }

    #[test]
    fn hamming_weight_change_upon_subtraction() {
        let minuend = BitField::new_sparse_from_str("100000");
        let subtrahend = BitField::new_sparse_from_str("000101");
        let mut difference = minuend.clone();
        difference -= &subtrahend;
        let expected_hamming_weight_change = (difference.hamming_weight() as i64) - (minuend.hamming_weight() as i64);
        let actual_hamming_weight_change = minuend.hamming_weight_change_upon_subtraction(subtrahend);
        assert_eq!(-expected_hamming_weight_change, actual_hamming_weight_change);
        let minuend = BitField::new_sparse_from_str("10000");
        let subtrahend = BitField::new_sparse_from_str("00101");
        let mut difference = minuend.clone();
        difference -= &subtrahend;
        let expected_hamming_weight_change = (difference.hamming_weight() as i64) - (minuend.hamming_weight() as i64);
        let actual_hamming_weight_change = minuend.hamming_weight_change_upon_subtraction(subtrahend);
        assert_eq!(-expected_hamming_weight_change, actual_hamming_weight_change);
        let minuend = BitField::new_sparse_from_str("1000100");
        let subtrahend = BitField::new_sparse_from_str("0001101");
        let mut difference = minuend.clone();
        difference -= &subtrahend;
        let expected_hamming_weight_change = (difference.hamming_weight() as i64) - (minuend.hamming_weight() as i64);
        let actual_hamming_weight_change = minuend.hamming_weight_change_upon_subtraction(subtrahend);
        assert_eq!(-expected_hamming_weight_change, actual_hamming_weight_change);
        let minuend = BitField::new_sparse_from_str("1001100");
        let subtrahend = BitField::new_sparse_from_str("0101101");
        let mut difference = minuend.clone();
        difference -= &subtrahend;
        let expected_hamming_weight_change = (difference.hamming_weight() as i64) - (minuend.hamming_weight() as i64);
        let actual_hamming_weight_change = minuend.hamming_weight_change_upon_subtraction(subtrahend);
        assert_eq!(-expected_hamming_weight_change, actual_hamming_weight_change);
        let minuend = BitField::new_sparse_from_str("1011100");
        let subtrahend = BitField::new_sparse_from_str("0101101");
        let mut difference = minuend.clone();
        difference -= &subtrahend;
        let expected_hamming_weight_change = (difference.hamming_weight() as i64) - (minuend.hamming_weight() as i64);
        let actual_hamming_weight_change = minuend.hamming_weight_change_upon_subtraction(subtrahend);
        assert_eq!(-expected_hamming_weight_change, actual_hamming_weight_change);
        let minuend = BitField::new_sparse_from_str("101110011010101");
        let subtrahend = BitField::new_sparse_from_str("100110100101001");
        let mut difference = minuend.clone();
        difference -= &subtrahend;
        let expected_hamming_weight_change = (difference.hamming_weight() as i64) - (minuend.hamming_weight() as i64);
        let actual_hamming_weight_change = minuend.hamming_weight_change_upon_subtraction(subtrahend);
        assert_eq!(-expected_hamming_weight_change, actual_hamming_weight_change);
        let minuend = BitField::new_sparse_from_str("101110011000000");
        let subtrahend = BitField::new_sparse_from_str("100110100101011");
        let mut difference = minuend.clone();
        difference -= &subtrahend;
        let expected_hamming_weight_change = (difference.hamming_weight() as i64) - (minuend.hamming_weight() as i64);
        let actual_hamming_weight_change = minuend.hamming_weight_change_upon_subtraction(subtrahend);
        assert_eq!(-expected_hamming_weight_change, actual_hamming_weight_change);
        let minuend = BitField::new_sparse_from_str("101110011000000");
        let subtrahend = BitField::new_sparse_from_str("100111111111111");
        let mut difference = minuend.clone();
        difference -= &subtrahend;
        let expected_hamming_weight_change = (difference.hamming_weight() as i64) - (minuend.hamming_weight() as i64);
        let actual_hamming_weight_change = minuend.hamming_weight_change_upon_subtraction(subtrahend);
        assert_eq!(-expected_hamming_weight_change, actual_hamming_weight_change);
    }
}
