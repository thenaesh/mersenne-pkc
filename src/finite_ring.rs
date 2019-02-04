use std::ops::{Add, Sub};
use std::ops::Neg;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct FiniteRing {
    pub modulus: usize,
    pub val: usize,
}

impl FiniteRing {
    pub fn new(modulus: usize, val: usize) -> Self {
        let mut corrected_val = val;

        while corrected_val >= modulus {
            corrected_val -= modulus;
        }

        FiniteRing { modulus: modulus, val: corrected_val }
    }
}

impl Neg for FiniteRing {
    type Output = FiniteRing;

    fn neg(self: Self) -> Self::Output {
        FiniteRing::new(self.modulus, self.modulus - self.val)
    }
}

impl Add<FiniteRing> for FiniteRing {
    type Output = FiniteRing;

    fn add(self, other: FiniteRing) -> Self::Output {
        if self.modulus != other.modulus {
            panic!("Adding FiniteRings with different moduli!");
        }

        let mut sum = self.val + other.val;
        if sum >= self.modulus { sum = sum - self.modulus; }

        FiniteRing { modulus: self.modulus, val: sum }
    }
}

impl Sub<FiniteRing> for FiniteRing {
    type Output = FiniteRing;

    fn sub(self, other: FiniteRing) -> Self::Output {
        self + (-other)
    }
}


#[cfg(test)]
mod tests {
    use crate::finite_ring::FiniteRing;

    #[test]
    fn new_val_remains_unchanged_if_less_than_modulus() {
        let x = FiniteRing::new(3425, 2544);
        assert_eq!(x.val, 2544);
    }

    #[test]
    fn new_val_changes_if_greater_than_modulus_but_less_than_2_modulus() {
        let x = FiniteRing::new(42, 76);
        assert_eq!(x.val, 34);
    }

    #[test]
    fn new_val_changes_if_greater_than_modulus_but_less_than_5_modulus() {
        let x = FiniteRing::new(32, 137);
        assert_eq!(x.val, 9);
    }

    #[test]
    fn neg() {
        let x = FiniteRing::new(32, 18);
        let y = FiniteRing::new(32, 14);
        let z = FiniteRing::new(32, 0);

        assert_eq!(-x, y);
        assert_eq!(x, -y);
        assert_eq!(-z, z);
    }

    #[test]
    fn add_zero_val_correct() {
        let x = FiniteRing::new(15, 3);
        let y = FiniteRing::new(15, 0);
        let z = x + y;
        assert_eq!(z.val, 3);
    }

    #[test]
    fn add_zero_modulus_correct() {
        let x = FiniteRing::new(15, 3);
        let y = FiniteRing::new(15, 0);
        let z = x + y;
        assert_eq!(z.modulus, 15);
    }

    #[test]
    fn add_modulus_val_correct() {
        let x = FiniteRing::new(15, 3);
        let y = FiniteRing::new(15, 12);
        let z = x + y;
        assert_eq!(z.val, 0);
    }

    #[test]
    fn add_modulus_modulus_correct() {
        let x = FiniteRing::new(15, 3);
        let y = FiniteRing::new(15, 12);
        let z = x + y;
        assert_eq!(z.modulus, 15);
    }

    #[test]
    fn add_nowrap_val_correct() {
        let x = FiniteRing::new(15, 3);
        let y = FiniteRing::new(15, 11);
        let z = x + y;
        assert_eq!(z.val, 14);
    }

    #[test]
    fn add_nowrap_modulus_correct() {
        let x = FiniteRing::new(15, 3);
        let y = FiniteRing::new(15, 11);
        let z = x + y;
        assert_eq!(z.modulus, 15);
    }

    #[test]
    fn add_wrap_val_correct() {
        let x = FiniteRing::new(15, 3);
        let y = FiniteRing::new(15, 14);
        let z = x + y;
        assert_eq!(z.val, 2);
    }

    #[test]
    fn add_wrap_modulus_correct() {
        let x = FiniteRing::new(15, 3);
        let y = FiniteRing::new(15, 14);
        let z = x + y;
        assert_eq!(z.modulus, 15);
    }

    #[test]
    fn pass_by_value() {
        let x = FiniteRing::new(15, 3);
        let y = FiniteRing::new(15, 4);
        let z1 = x + y;
        let z2 = x + y;
        assert_eq!(z1.val, z2.val);
        assert_eq!(z1.modulus, z2.modulus);
    }

    #[test]
    fn eq() {
        let x = FiniteRing::new(15, 12);
        let y = FiniteRing::new(15, 12);
        assert!(x == y);
    }

    #[test]
    fn neq() {
        let x = FiniteRing::new(15, 12);
        let y = FiniteRing::new(15, 11);
        assert!(x != y);
    }
}
