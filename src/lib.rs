mod finite_ring;
pub mod mersenne_field;

use std::collections::HashSet;
use crate::mersenne_field::MersenneField;

pub type PublicKey = MersenneField;
pub type PrivateKey = (MersenneField, MersenneField);

pub type PlainText = (MersenneField, MersenneField);
pub type CipherText = MersenneField;

pub fn randomly_generate_message(n: usize, h: usize) -> PlainText {
    let a = MersenneField::new_uniform_random(n, h);
    let b = MersenneField::new_uniform_random(n, h);

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
    let mut z = c;
    let (f, g) = pri_key;

    z *= &g;

    let mut f_indices: Vec<usize> = Vec::with_capacity(h);
    let mut g_indices: Vec<usize> = Vec::with_capacity(h);

    while f_indices.len() < h {
        let vec = pick_smallest_subtraction_powers(&z, &f);
        let mut i = 0;
        let mut p = &vec[i];
        while f_indices.contains(&p.0) {
            i += 1;
            if i >= vec.len() {
                break;
            }
            p = &vec[i];
        }
        let (idx, field) = p;
        z = field.clone();
        /*
        if f_indices.contains(&idx) {
            continue;
        }
        */
        f_indices.push(idx.clone());
    }

    while g_indices.len() < h {
        let vec = pick_smallest_subtraction_powers(&z, &g);
        let mut i = 0;
        let mut p = &vec[i];
        while g_indices.contains(&p.0) {
            i += 1;
            if i >= vec.len() {
                break;
            }
            p = &vec[i];
        }
        let (idx, field) = p;
        z = field.clone();
        /*
        if g_indices.contains(&idx) {
            continue;
        }
        */
        g_indices.push(idx.clone());
    }

    let mut a = MersenneField::new(n);
    let mut b = MersenneField::new(n);

    for idx in f_indices {
        a.bits[idx] = true;
    }

    for idx in g_indices {
        b.bits[idx] = true;
    }

    (a, b)
}

fn pick_smallest_subtraction_powers(z: &MersenneField, s: &MersenneField) -> Vec<(usize, MersenneField)> {
    let n = z.len();

    let mut subtraction_powers_and_values = (0..n)
        .map(|i| {
            let mut d_i = z.clone();
            let mut ss = s.clone();
            ss <<= i;
            d_i -= &ss;
            (ss, d_i)
        })
        .enumerate()
        .collect::<Vec<(usize, (MersenneField, MersenneField))>>();

        subtraction_powers_and_values.sort_by_key(|(_, (_, field))| field.hamming_weight());
        let diffs: Vec<(String, String, usize, i64)> = subtraction_powers_and_values.iter().map(|(idx, (delta, field))| (delta.to_string(), field.to_string(), *idx, field.hamming_weight() as i64)).collect();
        println!("S: {}", s.to_string());
        println!("Z: {}, Hamming Weight: {}", z.to_string(), z.hamming_weight());
        println!("Diffs: {:?}", diffs);

        subtraction_powers_and_values.iter().map(|(idx, (delta, field))| (*idx, field.clone())).collect()
}
