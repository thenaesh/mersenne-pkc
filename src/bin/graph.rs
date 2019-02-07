use mersennepkc::*;
use crate::bit_field::BitField;
use std::vec::Vec;
use std::iter::Iterator;

fn main() {
    let n = 9689;
    let h = 32;

    let (f, g) = randomly_generate_message(n, h);
    println!("F, G: {:?}, {:?}", f.all_set_bits(), g.all_set_bits());

    let mut pub_key = f.clone();
    pub_key /= &g;

    let msg = randomly_generate_message(n, h);
    let (a,b) = msg.clone();

    let mut c = encrypt(msg, pub_key, h);
    c *= &g;

    let mut f_deltas: Vec<(usize, i64)> = (0..n).map(|i| (i, delta(&c, &f, i))).collect();
    f_deltas.sort_unstable_by_key(|(_, b)| *b);

    let mut expected = Vec::<usize>::with_capacity(h);
    for i in 0..h {
        expected.push(f_deltas[i].0);
    }
    expected.sort_unstable();
    println!("Result for A: {:?}", expected);
}

fn delta(minuend: &BitField, subtrahend: &BitField, shift_amt: usize) -> i64 {
    let original_hw = minuend.hamming_weight() as i64;

    let mut subtrahend = subtrahend.clone();
    subtrahend <<= shift_amt;

    let mut difference = minuend.clone();
    difference -= &subtrahend;

    let new_hw = difference.hamming_weight() as i64;

    new_hw - original_hw
}