use std::vec::Vec;
use std::str::FromStr;
use std::fmt::Display;

// the 0th element is the highest-order bit
type BitVector = Vec<bool>;

pub fn shift_left(a: &mut BitVector) {
    a.push(false);
}

pub fn shift_right(a: &mut BitVector) {
    a.pop();
}
