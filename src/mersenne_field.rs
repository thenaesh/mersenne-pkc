use core::cmp::Ordering;
use std::vec::Vec;
use std::iter::Iterator;
use std::iter::IntoIterator;
use std::cmp::{PartialEq, Eq, PartialOrd};
use std::str::FromStr;
use std::fmt::Display;
use std::ops::{Add, Sub, Mul, Div};
use std::ops::{AddAssign, SubAssign, MulAssign, DivAssign, ShlAssign, ShrAssign};
use rand::Rng;

use crate::finite_ring::FiniteRing;

#[derive(Debug, Clone)]
pub struct MersenneField {
    n: usize,
    pub bits: Vec<bool>,
    offset: FiniteRing,
}

pub struct MersenneFieldIterator<'a> {
    field: &'a MersenneField,
    idx: FiniteRing,
    dirty: bool,
}

impl<'a> Iterator for MersenneFieldIterator<'a> {
    type Item = bool;

    fn next(self: &mut Self) -> Option<Self::Item> {
        if self.dirty && self.idx == (*self.field).offset {
            Option::None
        } else {
            self.dirty = true;
            let i = self.idx.val;
            let bit = (*self.field).bits[i as usize];

            self.idx = (self.idx + FiniteRing::new(self.field.n, 1)).unwrap();
            Option::Some(bit)
        }
    }
}

impl<'a> IntoIterator for &'a MersenneField {
    type Item = bool;
    type IntoIter = MersenneFieldIterator<'a>;

    fn into_iter(self: Self) -> Self::IntoIter {
        MersenneFieldIterator {
            field: self,
            idx: self.offset,
            dirty: false,
        }
    }
}

impl MersenneField {
    pub fn new(n: usize) -> Self {
        let mut field = MersenneField {
            n: n,
            bits: Vec::new(),
            offset: FiniteRing::new(n, 0),
        };

        for _ in 0..n {
            field.bits.push(false);
        }

        field
    }

    pub fn new_uniform_random(n: usize, hamming_weight: usize) -> Self {
        let mut rng = rand::thread_rng();
        let mut field = MersenneField::new(n);

        let mut i = 0;
        while i < hamming_weight {
            let rand_idx = rng.gen::<usize>() % n;
            if field.bits[rand_idx] {
                continue;
            } else {
                i += 1;
                field.bits[rand_idx] = true;
            }
        }

        field
    }

    pub fn len(self: &Self) -> usize {
        self.n
    }

    pub fn set_bits(self: &Self) -> Vec<usize> {
        let mut vec: Vec<usize> = Vec::new();
        for i in 0..self.n {
            if !self.bits[i] {
                continue;
            }
            let j = (FiniteRing::new(self.n, i) - self.offset).unwrap().val;
            vec.push(j);
        }
        vec
    }

    fn rotate(self: &mut Self, k: FiniteRing) {
        if let Some(result) = self.offset + k {
            self.offset = result;
        } else {
            panic!("Adding two FiniteRings with different moduli!");
        }
    }

    fn shift_right_one_noncyclic(self: &mut Self) {
        self.bits[self.offset.val] = false;
        self.offset = (self.offset + FiniteRing::new(self.n, 1)).unwrap();
    }

    fn is_odd(self: &Self) -> bool {
        self.bits[self.offset.val]
    }

    fn is_even(self: &Self) -> bool {
        !self.is_odd()
    }

    fn is_zero(self: &Self) -> bool {
        !self.into_iter().fold(false, |acc, x| acc || x)
    }

    fn is_one(self: &Self) -> bool {
        let mut iter = self.into_iter();
        let first = iter.next().unwrap();
        first && !iter.fold(false, |acc, x| acc || x)
    }

    fn is_all_one(self: &Self) -> bool {
        self.into_iter().fold(true, |acc, x| acc && x)
    }

    fn zero_if_all_one(self: &mut Self) {
        if !self.is_all_one() {
            return;
        }

        let n = self.n;
        for i in 0..n {
            self.bits[i] = false;
        }
    }

    fn complement(self: &Self) -> MersenneField {
        let mut field = MersenneField::new(self.n);
        for i in 0..self.n {
            field.bits[i] = !self.bits[i];
        }
        field.offset = self.offset;
        field
    }

    pub fn hamming_weight(self: &Self) -> usize {
        self.into_iter().filter(|x| *x).count()
    }

    fn ones(n: usize) -> MersenneField {
        let mut field = MersenneField::new(n);
        for i in 0..n {
            field.bits[i] = true;
        }
        field
    }

    fn one(n: usize) -> MersenneField {
        let mut field = MersenneField::new(n);
        field.bits[0] = true;
        field
    }

    fn zero(n: usize) -> MersenneField {
        MersenneField::new(n)
    }

    fn add_and_div_by_2_assign(self: &mut Self, other: &Self) {
        if self.n != other.n {
            panic!("Mismatched bit vector lengths!")
        }

        let mut result: Vec<bool> = Vec::with_capacity(self.n + 1);

        let mut carry_and_bit = (false, false);
        for (i, (a,b)) in self.into_iter().zip(other.into_iter()).enumerate() {
            carry_and_bit = match (carry_and_bit.0, a, b) {
                (false, _, _) => (a && b, a != b),
                (true, false, false) => (false, true),
                (true, false, true) => (true, false),
                (true, true, false) => (true, false),
                (true, true, true) => (true, true),
            };

            result.push(carry_and_bit.1);
        }
        result.push(carry_and_bit.0);

        // division by 2 (i.e. right shifting by 1) happens implicitly here
        for i in 0..self.n {
            self.bits[i] = result[i+1];
        }
        self.offset = FiniteRing::new(self.n, 0);
    }
}

impl FromStr for MersenneField {
    type Err = &'static str;

    fn from_str(bitstring: &str) -> Result<Self, Self::Err> {
        let is_all_bits = bitstring.chars().fold(true, |acc, x| acc && (x == '0' || x == '1'));
        if !is_all_bits {
            return Result::Err("Trying to generate a MersenneField from an improper string!");
        }

        let n = bitstring.len();
        let mut field = MersenneField::new(n);

        for (i, bit) in bitstring.chars().map(|c| c != '0').rev().enumerate() {
            field.bits[i] = bit;
        }

        field.zero_if_all_one();
        Ok(field)
    }
}

impl Display for MersenneField {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let n = self.n;

        let mut bitvec: Vec<char> = Vec::with_capacity(n);
        for c in (&self).into_iter().map(|x| if x { '1' } else { '0' }) {
            bitvec.push(c);
        }

        let mut bitstring = String::new();
        for c in bitvec.iter().rev() {
            bitstring.push(*c);
        }

        write!(f, "{}", bitstring)
    }
}


impl PartialEq<&str> for MersenneField {
    fn eq(self: &Self, other: &&str) -> bool {
        let bitstring = *other;
        return if bitstring.len() != self.bits.len() {
            false
        } else {
            (&self)
                .into_iter()
                .map(|x| if x { '1' } else { '0' })
                .zip(bitstring.chars().rev())
                .fold(true, |acc, (a,b)| acc && a == b)
        }
    }
}

impl PartialEq for MersenneField {
    fn eq(self: &Self, other: &Self) -> bool {
        if self.len() != other.len() {
            false
        } else {
            self.into_iter()
                .zip(other.into_iter())
                .fold(true, |acc, (a,b)| acc && a == b)
        }
    }
}
impl Eq for MersenneField {}

impl PartialOrd for MersenneField {
    fn partial_cmp(self: &Self, other: &Self) -> Option<Ordering> {
        return if self.n != other.n {
            Option::None
        } else {
            let n = self.n;
            let mut ord = Ordering::Equal;

            let mut idx_self = (FiniteRing::new(n, n-1) + self.offset).unwrap();
            let mut idx_other = (FiniteRing::new(n, n-1) + self.offset).unwrap();

            while idx_self != self.offset {
                match (self.bits[idx_self.val], other.bits[idx_other.val]) {
                    (false, true) => { ord = Ordering::Less; break; },
                    (true, false) => { ord = Ordering::Greater; break },
                    (_, _) => {},
                }
                idx_self = (idx_self - FiniteRing::new(n, 1)).unwrap();
                idx_other = (idx_other - FiniteRing::new(n, 1)).unwrap();
            }

            Option::Some(ord)
        }
    }
}

impl<'a> AddAssign<&'a MersenneField> for MersenneField {
    fn add_assign(self: &mut Self, other: &Self) {
        if self.n != other.n {
            panic!("Mismatched bit vector lengths!")
        }

        let mut result = MersenneField::new(self.n);

        let mut carry_and_bit = (false, false);
        for (i, (a,b)) in self.into_iter().zip(other.into_iter()).enumerate() {
            carry_and_bit = match (carry_and_bit.0, a, b) {
                (false, _, _) => (a && b, a != b),
                (true, false, false) => (false, true),
                (true, false, true) => (true, false),
                (true, true, false) => (true, false),
                (true, true, true) => (true, true),
            };

            result.bits[i] = carry_and_bit.1;
        }

        if carry_and_bit.0 {
            let mut one_field = MersenneField::new(self.n);
            one_field.bits[0] = true;
            result += &one_field;
        }

        result.zero_if_all_one();

        self.bits = result.bits;
        self.offset = result.offset;
    }
}

impl<'a> SubAssign<&'a MersenneField> for MersenneField {
    fn sub_assign(self: &mut Self, other: &Self) {
        if self.n != other.n {
            panic!("Mismatched bit vector lengths!")
        }

        let mut result = MersenneField::new(self.n);
        let mut neg_other = MersenneField::new(self.n);
        let ones = MersenneField::ones(self.n);
        let one = MersenneField::one(self.n);

        // compute the negation of other, without modulo arithmetic, using method of complements
        let mut carry_and_bit = (false, false);
        for (i, (a,b)) in ones.into_iter().zip(other.complement().into_iter()).enumerate() {
            carry_and_bit = match (carry_and_bit.0, a, b) {
                (false, _, _) => (a && b, a != b),
                (true, false, false) => (false, true),
                (true, false, true) => (true, false),
                (true, true, false) => (true, false),
                (true, true, true) => (true, true),
            };

            neg_other.bits[i] = carry_and_bit.1;
        }
        carry_and_bit = (false, false);
        for (i, (a,b)) in neg_other.into_iter().zip(one.into_iter()).enumerate() {
            carry_and_bit = match (carry_and_bit.0, a, b) {
                (false, _, _) => (a && b, a != b),
                (true, false, false) => (false, true),
                (true, false, true) => (true, false),
                (true, true, false) => (true, false),
                (true, true, true) => (true, true),
            };

            result.bits[i] = carry_and_bit.1;
        }

        result.zero_if_all_one();
        result += self;

        self.bits = result.bits;
        self.offset = result.offset;
    }
}

impl<'a> MulAssign<&'a MersenneField> for MersenneField {
    fn mul_assign(self: &mut Self, other: &Self) {
        if self.n != other.n {
            panic!("Mismatched bit vector lengths!")
        }

        let mut result = MersenneField::new(self.n);
        let mut other_buffer = other.clone();

        for (i, bit) in self.into_iter().enumerate() {
            if bit {
                other_buffer <<= i;
                result += &other_buffer;
                other_buffer >>= i;
            }
        }

        self.bits = result.bits;
        self.offset = result.offset;
    }
}

impl<'a> DivAssign<&'a MersenneField> for MersenneField {
    // Fermat's Little Theorem
    fn div_assign(self: &mut Self, other: &Self) {
        if self.n != other.n {
            panic!("Mismatched bit vector lengths!")
        }

        let n = self.n;

        let mut result = self.clone();
        let mut base = other.clone();

        let mut exponent: Vec<bool> = Vec::with_capacity(n);
        let mut idx = 0;

        // setting exponent to 2^n - 1
        for _ in 0..n {
            exponent.push(true);
        }
        // subtracting 2 from exponent
        exponent[1] = false;

        // fast exponentiation
        while idx < n {
            if exponent[idx] {
                result *= &base;
                exponent[idx] = false;
            } else {
                let tmp_base = base.clone();
                base *= &tmp_base;
                idx += 1; // perform shift right on the exponent
            }
        }

        self.bits = result.bits;
        self.offset = result.offset;
    }

    // Euclidean Algorithm
    /*
    fn div_assign(self: &mut Self, other: &Self) {
        if self.n != other.n {
            panic!("Mismatched bit vector lengths!")
        }

        let n = self.n;
        let p = MersenneField::ones(n);

        let mut u = other.clone();
        let mut v = MersenneField::ones(n);

        let mut x1 = self.clone();
        let mut x2 = MersenneField::zero(n);

        while !(u.is_one() || v.is_one()) {
            while u.is_even() {
                u.shift_right_one_noncyclic();
                if x1.is_even() {
                    x1.shift_right_one_noncyclic();
                } else {
                    x1.add_and_div_by_2_assign(&p);
                }
            }
            while v.is_even() {
                v.shift_right_one_noncyclic();
                if x2.is_even() {
                    x2.shift_right_one_noncyclic();
                } else {
                    x2.add_and_div_by_2_assign(&p);
                }
            }


            if u >= v {
                u -= &v;
                x1 -= &x2;
            } else {
                v -= &u;
                x2 -= &x1;
            }
        }

        if u.is_one() {
            self.bits = x1.bits;
            self.offset = x1.offset;
        } else {
            self.bits = x2.bits;
            self.offset = x2.offset;
        }
    }
    */

    // Montgomery Inversion
    /*
    fn div_assign(self: &mut Self, other: &Self) {
        if self.n != other.n {
            panic!("Mismatched bit vector lengths!")
        }

        let n = self.n;
        let p = MersenneField::ones(n);

        let mut u = other.clone();
        let mut v = p.clone();

        let mut x1 = MersenneField::one(n);
        let mut x2 = MersenneField::zero(n);

        let mut k = 0;

        while !v.is_zero() {
            k += 1;
        }

        if !u.is_one() {
            panic!("Attempting to compute inverse of non-invertible element!");
        }

        if x1 > p {
            x1 -= &p;
        }
    }
    */
}

impl ShlAssign<usize> for MersenneField {
    fn shl_assign(self: &mut Self, k: usize) {
        self.rotate(-FiniteRing::new(self.n, k));
    }
}

impl ShrAssign<usize> for MersenneField {
    fn shr_assign(self: &mut Self, k: usize) {
        self.rotate(FiniteRing::new(self.n, k));
    }
}


#[cfg(test)]
mod tests {
    use crate::mersenne_field::MersenneField;
    use crate::finite_ring::FiniteRing;

    #[test]
    fn new_zeros_everything() {
        let n = 12345;
        let field = MersenneField::new(n);

        assert_eq!(field.n, n);
        assert!(field.offset == FiniteRing::new(n, 0));

        for i in 0..n {
            assert_eq!(field.bits[i], false);
        }
    }

    #[test]
    fn from_str_proper_bitstring() {
        let bitstring = "01101111100111001";
        let field: MersenneField = bitstring.parse().unwrap();

        assert_eq!(field.n, bitstring.len());
        assert_eq!(field.n, field.bits.len());

        for (i, bit) in bitstring.chars().rev().map(|c| c != '0').enumerate() {
            assert_eq!(field.bits[i], bit);
        }
    }

    #[test]
    fn from_str_improper_bitstring() {
        let bitstring = "the cake is a lie";
        bitstring.parse::<MersenneField>().expect_err("Unexpected MersenneField generated from improper bitstring");
    }

    #[test]
    fn rotate_by_zero() {
        let bitstring = "0110001001";
        let mut field: MersenneField = bitstring.parse().unwrap();

        let original_bits = field.bits.clone();
        assert_eq!(field.bits, original_bits);
        let original_offset = field.offset;
        assert_eq!(field.offset, original_offset);

        field.rotate(FiniteRing::new(field.n, 0));
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, original_offset);
    }

    #[test]
    fn rotate_by_nonzero() {
        let bitstring = "0110001001";
        let mut field: MersenneField = bitstring.parse().unwrap();

        let original_bits = field.bits.clone();
        assert_eq!(field.bits, original_bits);
        let original_offset = field.offset;
        assert_eq!(field.offset, original_offset);

        field.rotate(-FiniteRing::new(field.n, 1));
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, (original_offset - FiniteRing::new(field.n, 1)).unwrap());

        field.rotate(-FiniteRing::new(field.n, 2));
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, (original_offset - FiniteRing::new(field.n, 3)).unwrap());

        field.rotate(-FiniteRing::new(field.n, 4));
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, (original_offset - FiniteRing::new(field.n, 7)).unwrap());

        field.rotate(FiniteRing::new(field.n, 4));
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, (original_offset - FiniteRing::new(field.n, 3)).unwrap());

        field.rotate(FiniteRing::new(field.n, 2));
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, (original_offset - FiniteRing::new(field.n, 1)).unwrap());


        field.rotate(FiniteRing::new(field.n, 1));
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, original_offset);
    }

    #[test]
    fn iterator_zero_offset() {
        let bitstring = "00101";
        let field: MersenneField = bitstring.parse().unwrap();

        let mut iter = (&field).into_iter();

        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iterator_nonzero_offset() {
        let bitstring = "00101";
        let mut field: MersenneField = bitstring.parse().unwrap();

        field <<= 1; // 01010
        {
            let mut iter = (&field).into_iter();
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(true));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(true));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), None);
        }

        field <<= 2; // 01001
        {
            let mut iter = (&field).into_iter();
            assert_eq!(iter.next(), Some(true));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(true));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), None);
        }

        field <<= 4; // 10100
        {
            let mut iter = (&field).into_iter();
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(true));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(true));
            assert_eq!(iter.next(), None);
        }
    }

    #[test]
    fn to_string_returns_unrotated_bitstring() {
        let bitstring = "10010111011101";
        let field: MersenneField = bitstring.parse().unwrap();

        assert_eq!(bitstring, field.to_string());
    }

    #[test]
    fn to_string_returns_rotated_bitstring() {
        let bitstring = "10010111011101";
        let rotated_bitstring = "11101110110010";
        let mut field: MersenneField = bitstring.parse().unwrap();

        field <<= 5;
        assert_eq!(rotated_bitstring, field.to_string());
    }

    #[test]
    fn eq_bitstring() {
        let bitstring = "10010111011101";
        let rotated_bitstring = "11001011101110";
        let mut field: MersenneField = bitstring.parse().unwrap();

        assert_eq!(field, bitstring);
        assert_ne!(field, rotated_bitstring);

        field.rotate(FiniteRing::new(field.n, 1));

        assert_ne!(field, bitstring);
        assert_eq!(field, rotated_bitstring);
    }

    #[test]
    fn comparisons() {
        let mut x = "1011010".parse::<MersenneField>().unwrap();
        let mut y = "0011110".parse::<MersenneField>().unwrap();
        let mut z = "1011110".parse::<MersenneField>().unwrap();

        assert!(x > y);
        assert!(x < z);
        assert!(y < z);
        assert!(x == x);
        assert!(x != y);
    }

    #[test]
    fn non_cyclic_right_shift_one() {
        let mut x = "1011010".parse::<MersenneField>().unwrap();
        let y = "0101101".parse::<MersenneField>().unwrap();
        let z = "0010110".parse::<MersenneField>().unwrap();

        x.shift_right_one_noncyclic();
        assert_eq!(x, y);
        x.shift_right_one_noncyclic();
        assert_eq!(x, z);
    }

    #[test]
    fn shl_by_zero() {
        let bitstring = "10010111011101";
        let mut field: MersenneField = bitstring.parse().unwrap();

        field <<= 0;
        assert_eq!(field, bitstring);
    }

    #[test]
    fn shr_by_zero() {
        let bitstring = "10010111011101";
        let mut field: MersenneField = bitstring.parse().unwrap();

        field >>= 0;
        assert_eq!(field, bitstring);
    }

    #[test]
    fn shl_by_nonzero() {
        let bitstring = "00101";
        let mut field: MersenneField = bitstring.parse().unwrap();

        field <<= 1;
        assert_eq!(field, "01010");

        field <<= 2;
        assert_eq!(field, "01001");

        field <<= 4;
        assert_eq!(field, "10100");
    }

    #[test]
    fn shr_by_nonzero() {
        let bitstring = "00101";
        let mut field: MersenneField = bitstring.parse().unwrap();

        field >>= 1;
        assert_eq!(field, "10010");

        field >>= 2;
        assert_eq!(field, "10100");

        field >>= 4;
        assert_eq!(field, "01001");
    }

    #[test]
    fn add_assign_without_overflow() {
        let mut x = "101".parse::<MersenneField>().unwrap();
        let y = "001".parse::<MersenneField>().unwrap();
        x += &y;
        assert_eq!(x, "110");
    }

    #[test]
    fn add_assign_with_overflow() {
        let mut x = "101".parse::<MersenneField>().unwrap();
        let y = "110".parse::<MersenneField>().unwrap();
        x += &y;
        assert_eq!(x, "100");
    }

    #[test]
    fn add_rotated_value() {
        let mut x = "10101".parse::<MersenneField>().unwrap();
        let mut y = "00011".parse::<MersenneField>().unwrap();
        y <<= 1;
        x += &y;
        assert_eq!(x, "11011");
    }

    #[test]
    fn sub_assign_without_overflow() {
        let mut x = "101".parse::<MersenneField>().unwrap();
        let y = "010".parse::<MersenneField>().unwrap();
        x -= &y;
        assert_eq!(x, "011");
        let mut z = "11001".parse::<MersenneField>().unwrap();
        let w = "10011".parse::<MersenneField>().unwrap();
        z -= &w;
        assert_eq!(z, "00110");
    }

    #[test]
    fn sub_assign_with_overflow() {
        let mut x = "001".parse::<MersenneField>().unwrap();
        let y = "101".parse::<MersenneField>().unwrap();
        x -= &y;
        assert_eq!(x, "011");
        let mut z = "01001".parse::<MersenneField>().unwrap();
        let w = "10011".parse::<MersenneField>().unwrap();
        z -= &w;
        assert_eq!(z, "10101");
        let mut z = "10101".parse::<MersenneField>().unwrap();
        let w = "00101".parse::<MersenneField>().unwrap();
        z -= &w;
        assert_eq!(z, "10000");
    }

    #[test]
    fn sub_rotated_value() {
        let mut x = "10101".parse::<MersenneField>().unwrap();
        let mut y = "10010".parse::<MersenneField>().unwrap();
        y <<= 1;
        x -= &y;
        assert_eq!(x, "10000");
    }

    #[test]
    fn mul_without_offset() {
        let mut x = "0011".parse::<MersenneField>().unwrap();
        let y = "0010".parse::<MersenneField>().unwrap();
        x *= &y;
        assert_eq!(x, "0110");
    }

    #[test]
    fn mul_with_offset() {
        let mut x = "0110".parse::<MersenneField>().unwrap();
        let y = "0011".parse::<MersenneField>().unwrap();
        x *= &y;
        assert_eq!(x, "0011");

        let mut z = "1001".parse::<MersenneField>().unwrap();
        let w = "0111".parse::<MersenneField>().unwrap();
        z *= &w;
        assert_eq!(z, "0011");
    }

    #[test]
    fn div_without_offset() {
        let mut x = "110".parse::<MersenneField>().unwrap();
        let y = "011".parse::<MersenneField>().unwrap();
        x /= &y;
        assert_eq!(x, "010");

        let mut z = "11000".parse::<MersenneField>().unwrap();
        let w = "00100".parse::<MersenneField>().unwrap();
        z /= &w;
        assert_eq!(z, "00110");
    }

    #[test]
    fn div_with_offset() {
        let mut x = "110".parse::<MersenneField>().unwrap();
        let y = "100".parse::<MersenneField>().unwrap();
        x /= &y;
        assert_eq!(x, "101");

        let mut z = "11001".parse::<MersenneField>().unwrap();
        let w = "10011".parse::<MersenneField>().unwrap();
        z /= &w;
        assert_eq!(z, "10000");
    }

    #[test]
    fn hamming_weight() {
        let x = "110".parse::<MersenneField>().unwrap();
        let y = "11101010".parse::<MersenneField>().unwrap();
        let z = "11000111010101".parse::<MersenneField>().unwrap();
        let w = "1101111".parse::<MersenneField>().unwrap();
        assert_eq!(x.hamming_weight(), 2);
        assert_eq!(y.hamming_weight(), 5);
        assert_eq!(z.hamming_weight(), 8);
        assert_eq!(w.hamming_weight(), 6);
    }

    #[test]
    fn new_uniform_random() {
        for _ in 0..10000 {
            let x = MersenneField::new_uniform_random(128, 34);
            assert_eq!(x.hamming_weight(), 34);
        }
    }
}
