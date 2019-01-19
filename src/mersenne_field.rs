use std::vec::Vec;
use std::iter::Iterator;
use std::iter::IntoIterator;
use std::cmp::PartialEq;
use std::str::FromStr;
use std::fmt::Display;
use std::ops::Add;
use std::ops::{ShlAssign, ShrAssign};

use crate::finite_ring::FiniteRing;

#[derive(Debug, Clone)]
pub struct MersenneField {
    n: usize,
    bits: Vec<bool>,
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

    pub fn rotate(self: &mut Self, k: FiniteRing) {
        if let Some(result) = self.offset + k {
            self.offset = result;
        } else {
            panic!("Adding two FiniteRings with different moduli!");
        }
    }

    fn zero_if_all_one(self: &mut Self) {
        let is_all_one = (&self).into_iter().fold(true, |acc, x| acc && x);

        if !is_all_one {
            return;
        }

        let n = self.n;
        for i in 0..n {
            self.bits[i] = false;
        }
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

impl<'a> Add for &'a MersenneField {
    type Output = Result<MersenneField, &'static str>;

    fn add(self: Self, other: Self) -> Self::Output {
        if self.n != other.n {
            return Result::Err("Mismatched bit vector lengths!");
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
            result = (&result + &one_field).unwrap();
        }

        result.zero_if_all_one();
        Result::Ok(result)
    }
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
    fn add_different_length_should_error() {
        let x = "1001".parse::<MersenneField>().unwrap();
        let y = "10010".parse::<MersenneField>().unwrap();
        (&x + &y).expect_err("Unexpected successful addition of two MersenneFields of unequal length!");
    }

    #[test]
    fn add_without_overflow() {
        let x = "101".parse::<MersenneField>().unwrap();
        let y = "001".parse::<MersenneField>().unwrap();
        assert_eq!((&x + &y).unwrap(), "110");
    }

    #[test]
    fn add_with_overflow() {
        let x = "101".parse::<MersenneField>().unwrap();
        let y = "110".parse::<MersenneField>().unwrap();
        assert_eq!((&x + &y).unwrap(), "100");
    }
}