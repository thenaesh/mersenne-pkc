use std::vec::Vec;
use std::iter::Iterator;
use std::iter::IntoIterator;
use std::cmp::PartialEq;
use std::str::FromStr;
use std::fmt::Display;

use crate::finite_ring::FiniteRing;

#[derive(Debug)]
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

    pub fn rotate(self: &mut Self, k: usize) {
        if let Some(result) = self.offset + FiniteRing::new(self.n, k) {
            self.offset = result;
        } else {
            // should never happen unless code within this function is wrong
            panic!("Adding two FiniteRings with different moduli!");
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

        for (i, bit) in bitstring.chars().map(|c| c != '0').enumerate() {
            field.bits[i] = bit;
        }

        Ok(field)
    }
}

impl Display for MersenneField {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut bitstring = String::new();
        for c in (&self).into_iter().map(|x| if x { '1' } else { '0' }) {
            bitstring.push(c);
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
                .zip(bitstring.chars())
                .fold(true, |acc, (a,b)| acc && a == b)
        }
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

        for (i, bit) in bitstring.chars().map(|c| c != '0').enumerate() {
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

        field.rotate(0);
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

        field.rotate(1);
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, (original_offset + FiniteRing::new(field.n, 1)).unwrap());

        field.rotate(2);
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, (original_offset + FiniteRing::new(field.n, 3)).unwrap());

        field.rotate(4);
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, (original_offset + FiniteRing::new(field.n, 7)).unwrap());
    }

    #[test]
    fn iterator_zero_offset() {
        let bitstring = "10100";
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
        let bitstring = "10100";
        let mut field: MersenneField = bitstring.parse().unwrap();

        field.rotate(1);
        {
            let mut iter = (&field).into_iter();
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(true));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(true));
            assert_eq!(iter.next(), None);
        }

        field.rotate(2);
        {
            let mut iter = (&field).into_iter();
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(true));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(true));
            assert_eq!(iter.next(), None);
        }

        field.rotate(4);
        {
            let mut iter = (&field).into_iter();
            assert_eq!(iter.next(), Some(true));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(false));
            assert_eq!(iter.next(), Some(true));
            assert_eq!(iter.next(), Some(false));
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

        field.rotate(5);
        assert_eq!(rotated_bitstring, field.to_string());
    }

    #[test]
    fn eq_bitstring() {
        let bitstring = "10010111011101";
        let rotated_bitstring = "11101110110010";
        let mut field: MersenneField = bitstring.parse().unwrap();

        assert_eq!(field, bitstring);
        assert_ne!(field, rotated_bitstring);

        field.rotate(5);

        assert_ne!(field, bitstring);
        assert_eq!(field, rotated_bitstring);
    }
}
