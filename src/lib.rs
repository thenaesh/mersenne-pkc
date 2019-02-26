pub mod finite_ring;
pub mod bit_field;

use std::iter::Iterator;

extern crate crypto;
use crypto::digest::Digest;
use crypto::sha3::Sha3;

use crate::bit_field::BitField;

pub type PublicKey = BitField;
pub type PrivateKey = (BitField, BitField);

pub type PlainText = (BitField, BitField);
pub type CipherText = BitField;

pub fn extract_session_key((a, b): &PlainText) -> String {
    let input_str = a.to_string() + &b.to_string();
    let mut hasher = Sha3::sha3_256();
    hasher.input_str(&input_str);
    hasher.result_str()
}

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

// currently does 2 passes
pub fn decrypt(c: CipherText, pri_key: PrivateKey, h: usize) -> PlainText {
    let n = c.len();

    let (mut f, mut g) = pri_key;
    f.make_sparse();
    g.make_sparse();

    let mut cg = c.clone();
    cg *= &g;

    let potential_a_bits = get_hamming_weight_changes_on_subtraction(&cg, &f);
    let potential_b_bits = get_hamming_weight_changes_on_subtraction(&cg, &g);

    let mut a = BitField::new_dense(n);
    let mut b = BitField::new_dense(n);

    for idx in 0..h/2 {
        let (i, _) = potential_a_bits[idx];
        let (j, _) = potential_b_bits[idx];
        a.set(i);
        b.set(j);
    }

    let mut tmp_af = a.clone();
    let mut tmp_bg = b.clone();
    tmp_af *= &f;
    tmp_bg *= &g;
    cg -= &tmp_af;
    cg -= &tmp_bg;

    let potential_a_bits = get_hamming_weight_changes_on_subtraction(&cg, &f);
    let potential_b_bits = get_hamming_weight_changes_on_subtraction(&cg, &g);

    for idx in 0..h/2 {
        let (i, _) = potential_a_bits[idx];
        let (j, _) = potential_b_bits[idx];
        a.set(i);
        b.set(j);
    }

    (a, b)
}

pub fn get_possible_coefficient_bits(minuend: &BitField, subtrahend: &BitField, threshold: i64) -> Vec<usize> {
    let mut result = Vec::new();

    let n = minuend.len();
    let mut minuend = minuend.clone();
    minuend.extend_self(1);
    minuend.make_sparse();
    minuend.set(n);
    minuend.normalize();

    for i in 0..n {
        let mut subtrahend = subtrahend.clone();
        subtrahend <<= i;
        subtrahend.normalize();
        subtrahend.extend_self(1);
        let hamming_weight_change = minuend.hamming_weight_change_upon_subtraction(subtrahend);
        if hamming_weight_change >= threshold {
            result.push(i)
        }
    }

    result
}

pub fn get_hamming_weight_changes_on_subtraction(minuend: &BitField, subtrahend: &BitField) -> Vec<(usize, i64)> {
    let n = minuend.len();

    let mut minuend = minuend.clone();
    minuend.extend_self(1);
    minuend.make_sparse();
    minuend.set(n);
    minuend.normalize();

    let mut result: Vec<(usize, i64)> = (0..n).map(|i| {
        let mut subtrahend = subtrahend.clone();
        subtrahend <<= i;
        subtrahend.normalize();
        subtrahend.extend_self(1);
        let hamming_weight_change = minuend.hamming_weight_change_upon_subtraction(subtrahend);
        (i, hamming_weight_change)
    }).collect();
    result.sort_unstable_by_key(|(i, hwc)| -hwc);

    result
}
