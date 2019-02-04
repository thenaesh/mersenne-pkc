use core::cmp::Ordering;
use std::vec::Vec;
use std::iter::Iterator;
use std::iter::IntoIterator;
use std::cmp::{PartialEq, Eq, PartialOrd};
use std::str::FromStr;
use std::fmt::Display;
use std::ops::{AddAssign, SubAssign, MulAssign, DivAssign, ShlAssign, ShrAssign};
use rand::Rng;
use gmp::mpz::Mpz;

use crate::finite_ring::FiniteRing;

#[derive(Debug, Clone)]
pub struct MersenneField {
    n: usize,
    pub bits: Mpz,
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
            let bit = (*self.field).bits.tstbit(i as usize);

            self.idx = self.idx + FiniteRing::new(self.field.n, 1);
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
        MersenneField {
            n: n,
            bits: Mpz::new_reserve(n),
            offset: FiniteRing::new(n, 0),
        }
    }

    pub fn new_uniform_random(n: usize, hamming_weight: usize) -> Self {
        let mut rng = rand::thread_rng();
        let mut field = MersenneField::new(n);

        let mut i = 0;
        while i < hamming_weight {
            let rand_idx = rng.gen::<usize>() % n;
            if field.bits.tstbit(rand_idx) {
                continue;
            } else {
                i += 1;
                field.bits.setbit(rand_idx);
            }
        }

        field
    }

    pub fn len(self: &Self) -> usize {
        self.n
    }

    pub fn get(self: &Self, k: usize) -> bool {
        let i = (self.offset + FiniteRing::new(self.n, k)).val;
        self.bits.tstbit(i)
    }

    pub fn set(self: &mut Self, k: usize, bit: bool) {
        let i = (self.offset + FiniteRing::new(self.n, k)).val;
        if bit { self.bits.setbit(i); } else { self.bits.clrbit(i); }
    }

    pub fn set_bits(self: &Self) -> Vec<usize> {
        let mut vec: Vec<usize> = Vec::new();
        for i in 0..self.n {
            if !self.bits.tstbit(i) {
                continue;
            }
            let j = (FiniteRing::new(self.n, i) - self.offset).val;
            vec.push(j);
        }
        vec
    }

    fn rotate(self: &mut Self, k: FiniteRing) {
        self.offset = self.offset + k;
    }

    fn apply_rotation(self: &mut Self) {
        if self.offset.val == 0 {
            return;
        }

        let n = self.n;
        for _ in 0..self.offset.val {
            let lowest_order_bit = self.bits.tstbit(0);
            self.bits >>= 1;
            if lowest_order_bit { self.bits.setbit(n-1); } else { self.bits.clrbit(n-1); }
        }
        self.offset = FiniteRing::new(n, 0);
    }

    fn shift_right_one_noncyclic(self: &mut Self) {
        self.bits.clrbit(self.offset.val);
        self.offset = self.offset + FiniteRing::new(self.n, 1);
    }

    fn is_odd(self: &Self) -> bool {
        self.bits.tstbit(self.offset.val)
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
            self.bits.clrbit(i);
        }
    }

    fn complement(self: &Self) -> MersenneField {
        MersenneField {
            n: self.n,
            bits: self.bits.compl(),
            offset: self.offset,
        }
    }

    pub fn hamming_weight(self: &Self) -> usize {
        self.into_iter().filter(|x| *x).count()
    }

    fn ones(n: usize) -> MersenneField {
        let mut field = MersenneField::new(n);
        for i in 0..n {
            field.bits.setbit(i);
        }
        field
    }

    fn one(n: usize) -> MersenneField {
        let mut field = MersenneField::new(n);
        field.bits.setbit(0);
        field
    }

    fn zero(n: usize) -> MersenneField {
        MersenneField::new(n)
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
            if bit { field.bits.setbit(i); } else { field.bits.clrbit(i); }
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
        return if bitstring.len() != self.n {
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
        if self.n != other.n {
            panic!("Mismatched bit vector lengths!")
        }

        self.bits.partial_cmp(&other.bits)
    }
}

impl<'a> AddAssign<&'a MersenneField> for MersenneField {
    fn add_assign(self: &mut Self, other: &Self) {
        if self.n != other.n {
            panic!("Mismatched bit vector lengths!")
        }

        let n = self.n;

        let mut p = Mpz::new_reserve(n);
        for i in 0..n {
            p.setbit(i);
        }

        self.bits += &other.bits;
        self.bits %= &p;
    }
}

impl<'a> SubAssign<&'a MersenneField> for MersenneField {
    fn sub_assign(self: &mut Self, other: &Self) {
        if self.n != other.n {
            panic!("Mismatched bit vector lengths!")
        }

        let n = self.n;

        let mut p = Mpz::new_reserve(n);
        for i in 0..n {
            p.setbit(i);
        }

        self.bits -= &other.bits;
        self.bits += &p;
        self.bits %= &p;
    }
}

impl<'a> MulAssign<&'a MersenneField> for MersenneField {
    fn mul_assign(self: &mut Self, other: &Self) {
        if self.n != other.n {
            panic!("Mismatched bit vector lengths!")
        }

        let n = self.n;

        let mut p = Mpz::new_reserve(n);
        for i in 0..n {
            p.setbit(i);
        }

        self.bits *= &other.bits;
        self.bits %= &p;
    }
}

impl<'a> DivAssign<&'a MersenneField> for MersenneField {
    fn div_assign(self: &mut Self, other: &Self) {
        if self.n != other.n {
            panic!("Mismatched bit vector lengths!")
        }

        let n = self.n;

        // want to compute b/a
        // b is self, a is other
        let mut p = Mpz::new_reserve(n);
        for i in 0..n {
            p.setbit(i);
        }

        self.bits *= other.bits.invert(&p).unwrap();
        self.bits %= &p;
    }
}

impl ShlAssign<usize> for MersenneField {
    fn shl_assign(self: &mut Self, k: usize) {
        let n = self.n;
        self.bits <<= k;
        for i in 0..k {
             if self.bits.tstbit(n+i) {
                 self.bits.setbit(i);
             } else{
                 self.bits.clrbit(i);
             }
        }
        for i in 0..k {
            self.bits.clrbit(n+i);
        }
    }
}

impl ShrAssign<usize> for MersenneField {
    fn shr_assign(self: &mut Self, k: usize) {
        let n = self.n;
        for i in 0..k {
             if self.bits.tstbit(i) {
                 self.bits.setbit(n+i);
             } else{
                 self.bits.clrbit(n+i);
             }
        }
        self.bits >>= k;
    }
}


#[cfg(test)]
mod tests {
    use crate::mersenne_field::MersenneField;
    use crate::finite_ring::FiniteRing;
    use gmp::mpz::Mpz;

    #[test]
    fn new_zeros_everything() {
        let n = 12345;
        let field = MersenneField::new(n);

        assert_eq!(field.n, n);
        assert!(field.offset == FiniteRing::new(n, 0));

        for i in 0..n {
            assert_eq!(field.bits.tstbit(i), false);
        }
    }

    #[test]
    fn from_str_proper_bitstring() {
        let bitstring = "01101111100111001";
        let field: MersenneField = bitstring.parse().unwrap();

        assert_eq!(field.n, bitstring.len());

        for (i, bit) in bitstring.chars().rev().map(|c| c != '0').enumerate() {
            assert_eq!(field.bits.tstbit(i), bit);
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
        assert_eq!(field.offset, original_offset - FiniteRing::new(field.n, 1));

        field.rotate(-FiniteRing::new(field.n, 2));
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, original_offset - FiniteRing::new(field.n, 3));

        field.rotate(-FiniteRing::new(field.n, 4));
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, original_offset - FiniteRing::new(field.n, 7));

        field.rotate(FiniteRing::new(field.n, 4));
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, original_offset - FiniteRing::new(field.n, 3));

        field.rotate(FiniteRing::new(field.n, 2));
        assert_eq!(field.bits, original_bits);
        assert_eq!(field.offset, original_offset - FiniteRing::new(field.n, 1));


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
    fn mul_rotated_value() {
        let mut x = "10101".parse::<MersenneField>().unwrap();
        let mut y = "10010".parse::<MersenneField>().unwrap();
        y <<= 1;
        x *= &y;
        assert_eq!(x, "01100");
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

    #[test]
    fn mpz() {
        let x = "10011".parse::<MersenneField>().unwrap();
        let y = "00111".parse::<MersenneField>().unwrap();

        let n = x.len();

        let mut p = Mpz::new_reserve(n);
        let mut a = Mpz::new_reserve(n);
        let mut b = Mpz::new_reserve(n);

        for i in 0..n {
            p.setbit(i);
            if x.get(i) { a.setbit(i); } else { a.clrbit(i); }
            if y.get(i) { b.setbit(i); } else { b.clrbit(i); }
        }

        let c = (a * b) % p;

        let mut z = MersenneField::new(n);
        for i in 0..n {
            z.set(i, c.tstbit(i));
        }

        let w = "01001".parse::<MersenneField>().unwrap();
        assert_eq!(w, z);
    }
}
