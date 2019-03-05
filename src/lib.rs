pub mod finite_ring;
pub mod bit_field;

use std::thread;
use crossbeam_channel::bounded;

extern crate crypto;
use crypto::digest::Digest;
use crypto::sha3::Sha3;
use std::time::SystemTime;

use crate::bit_field::BitField;

pub type PublicKey = BitField;
pub type PrivateKey = (BitField, BitField);

pub type PlainText = (BitField, BitField);
pub type CipherText = BitField;

pub fn get_threshold_for_parameters(n: usize, h: usize) -> i64 {
    match (n, h) {
        (44497, 64) => 50,
        (86243, 128) => 70,
        _ => panic!("Parameters n = {}, h = {} Unexpected!", n, h)
    }
}

pub fn extract_session_key((a, b): &PlainText) -> String {
    let a = a.as_sparse();
    let b = b.as_sparse();

    let (n, a_bits, _) = a.unwrap_sparse();
    let (m, b_bits, _) = b.unwrap_sparse();

    if n != m {
        panic!("Unexpectedly encountered bitstrings of different length!");
    }

    let mut a_deltas: Vec<usize> = Vec::with_capacity(a_bits.len());
    let mut b_deltas: Vec<usize> = Vec::with_capacity(b_bits.len());

    for i in 1..a_bits.len() {
        a_deltas.push(a_bits[i] - a_bits[i-1]);
    }
    for i in 1..b_bits.len() {
        b_deltas.push(b_bits[i] - b_bits[i-1]);
    }

    let a_final = a_deltas.iter()
        .fold(String::new(), |acc, x| acc + &format!("{:b}", *x))
        .as_bytes()
        .chunks(64)
        .map(std::str::from_utf8)
        .collect::<Result<Vec<&str>, _>>()
        .unwrap().iter()
        .map(|s| u64::from_str_radix(*s, 2).unwrap())
        .collect::<Vec<u64>>();
    let b_final = b_deltas.iter()
        .fold(String::new(), |acc, x| acc + &format!("{:b}", *x))
        .as_bytes()
        .chunks(64)
        .map(std::str::from_utf8)
        .collect::<Result<Vec<&str>, _>>()
        .unwrap().iter()
        .map(|s| u64::from_str_radix(*s, 2).unwrap())
        .collect::<Vec<u64>>();

    let innerpdt = a_final.iter().zip(b_final.iter())
        .map(|(a, b)| a + b)
        .fold(0 as u64, |acc, x| acc + x);

    format!("{:x}", innerpdt)
}

pub fn randomly_generate_message(n: usize, h: usize) -> PlainText {
    let a = BitField::new_uniform_random(n, h);
    let b = BitField::new_uniform_random(n, h);

    (a, b)
}

pub fn encrypt(m: PlainText, pub_key: PublicKey) -> CipherText {
    let (a, b) = m;
    let mut c = pub_key;
    c *= &a;
    c += &b;

    c
}

// currently does 2 passes
pub fn decrypt(c: CipherText, pri_key: PrivateKey, n: usize, h: usize) -> PlainText {
    let start_time = SystemTime::now();
    let n = c.len();
    let threshold = get_threshold_for_parameters(n, h);

    let (mut f, mut g) = pri_key;
    f.make_sparse();
    g.make_sparse();

    let mut cg = c.clone();
    cg *= &g;

    let mut a = BitField::new_dense(n);
    let mut b = BitField::new_dense(n);

    for _ in 0..2 {
        let potential_a_bits = get_possible_coefficient_bits(&cg, &f, threshold);
        let potential_b_bits = get_possible_coefficient_bits(&cg, &g, threshold);

        for idx in potential_a_bits {
            a.set(idx)
        }
        for idx in potential_b_bits {
            b.set(idx)
        }

        let mut tmp_af = a.clone();
        let mut tmp_bg = b.clone();
        tmp_af *= &f;
        tmp_bg *= &g;
        cg -= &tmp_af;
        cg -= &tmp_bg;
    }

    println!("Decryption Time: {}ms", start_time.elapsed().unwrap().as_millis());
    (a, b)
}

pub fn get_possible_coefficient_bits(minuend: &BitField, subtrahend: &BitField, threshold: i64) -> Vec<usize> {
    let start_time = SystemTime::now();

    let n = minuend.len();
    let mut minuend = minuend.clone();
    minuend.extend_self(1);
    minuend.make_sparse();
    minuend.set(n);
    minuend.normalize();

    const NUM_THREADS: usize = 8;
    let job_size = n / NUM_THREADS + 1;
    let (s, r) = bounded(n);

    for thread_idx in 0..NUM_THREADS {
        let subtrahend = subtrahend.clone();
        let minuend = minuend.clone();
        let s = s.clone();

        thread::spawn(move || {
            let start_idx = thread_idx * job_size;
            let end_idx = std::cmp::min(n, start_idx + job_size);

            for i in start_idx..end_idx {
                let mut subtrahend = subtrahend.clone();
                subtrahend <<= i;
                subtrahend.normalize();
                subtrahend.extend_self(1);
                let hamming_weight_change = minuend.hamming_weight_change_upon_subtraction(subtrahend);
                if hamming_weight_change >= threshold {
                    s.send(i).unwrap();
                }
            }

            drop(s);
        });
    }

    drop(s);
    let result: Vec<usize> = r.iter().collect();

    println!("Partial Decryption Time: {}ms", start_time.elapsed().unwrap().as_millis());
    result
}
