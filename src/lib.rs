pub mod finite_ring;
pub mod bit_field;

use std::iter::Iterator;

use crate::bit_field::BitField;
use crate::finite_ring::FiniteRing;

pub type PublicKey = BitField;
pub type PrivateKey = (BitField, BitField);

pub type PlainText = (BitField, BitField);
pub type CipherText = BitField;

const N_WORKERS: usize = 2;
const N_JOBS: usize = 2;

pub fn randomly_generate_message(n: usize, h: usize) -> PlainText {
    let a = BitField::new_uniform_random(n, h);
    let b = BitField::new_uniform_random(n, h);

    (a, b)
}

pub fn encrypt(m: PlainText, pub_key: PublicKey, h: usize) -> CipherText {
    let (a, b) = m;
    let mut c = pub_key;
    c *= &a;
    c += &b;
    c
}

pub fn decrypt(c: CipherText, pri_key: PrivateKey, h: usize) -> PlainText {
    let n = c.len();

    let (mut f, mut g) = pri_key;
    f.make_sparse();
    g.make_sparse();

    let mut z = c;
    z *= &g;
    let mut z = z.extend(1);
    z.make_sparse();
    z.set(n);
    z.normalize();

    let potential_a_bits = get_hamming_weight_changes_on_subtraction(&z, &f);
    let potential_b_bits = get_hamming_weight_changes_on_subtraction(&z, &g);

    let mut a = BitField::new_dense(n);
    let mut b = BitField::new_dense(n);

    for idx in 0..h {
        let (i, _) = potential_a_bits[idx];
        let (j, _) = potential_b_bits[idx];
        a.set(i);
        b.set(j);
    }

    (a, b)
}

// computes the list [x - y * 2^i for i in 0..n]
pub fn get_hamming_weight_changes_on_subtraction(minuend: &BitField, subtrahend: &BitField) -> Vec<(usize, i64)> {
    let n = minuend.len();
    let m = subtrahend.len();

    let mut result: Vec<(usize, i64)> = (0..n).map(|i| {
        let mut subtrahend = subtrahend.clone();
        subtrahend <<= i;
        subtrahend.normalize();
        let mut subtrahend = subtrahend.extend(1);
        let hamming_weight_change = minuend.hamming_weight_change_upon_subtraction(subtrahend);
        (i, hamming_weight_change)
    }).collect();
    result.sort_unstable_by_key(|(i, hwc)| -hwc);
    result
}
