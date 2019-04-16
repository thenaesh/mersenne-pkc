pub mod finite_ring;
pub mod bit_field;

use std::thread;
use crossbeam_channel::bounded;

extern crate crypto;
use std::time::SystemTime;

use crate::bit_field::BitField;

pub type PublicKey = BitField;
pub type PrivateKey = (BitField, BitField);

pub type PlainText = (BitField, BitField);
pub type CipherText = BitField;

/*
 * Gets the proper experimentally-determined parameters for each value of n and h
 * Fully defined only for n = 86243, h = 128 for now, but may be extended in the future
 */
pub fn get_threshold_for_parameters(n: usize, h: usize, n_iter: usize) -> i64 {
    match (n, h, n_iter) {
        (44497, 64, 0) => 50, // used only for plotting graphs
        (86243, 128, 0) => 74,
        (86243, 128, 1) => 60,
        (86243, 128, _) => 60,
        _ => panic!("Parameters n = {}, h = {}, n_iter = {} Unexpected!", n, h, n_iter)
    }
}

/*
 * Takes (A, B) as input and computes Ext(A, B)
 * The extractor used is the inner product extractor.
 */
pub fn extract_128_bit_key((a, b): &PlainText) -> String {
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
        .chunks(128)
        .map(std::str::from_utf8)
        .collect::<Result<Vec<&str>, _>>()
        .unwrap().iter()
        .map(|s| u128::from_str_radix(*s, 2).unwrap())
        .collect::<Vec<u128>>();
    let b_final = b_deltas.iter()
        .fold(String::new(), |acc, x| acc + &format!("{:b}", *x))
        .as_bytes()
        .chunks(128)
        .map(std::str::from_utf8)
        .collect::<Result<Vec<&str>, _>>()
        .unwrap().iter()
        .map(|s| u128::from_str_radix(*s, 2).unwrap())
        .collect::<Vec<u128>>();

    let innerpdt = a_final.iter().zip(b_final.iter())
        .map(|(a, b)| a + b)
        .fold(0 as u128, |acc, x| acc + x);

    format!("{:x}", innerpdt)
}

/*
 * Randomly chooses (A, B)
 */
pub fn randomly_generate_message(n: usize, h: usize) -> PlainText {
    let a = BitField::new_uniform_random(n, h);
    let b = BitField::new_uniform_random(n, h);

    (a, b)
}

/*
 * Computes A*H+B given (A, B) and public key H
 */
pub fn encrypt(m: PlainText, pub_key: PublicKey) -> CipherText {
    let (a, b) = m;
    let mut c = pub_key;
    c *= &a;
    c += &b;

    c
}

/*
 * Computes (A, B) with high probability given AH+B and corresponding private key (F, G)
 * where H = F/G
 */
pub fn decrypt(c: CipherText, pri_key: PrivateKey, n: usize, h: usize) -> PlainText {
    let start_time = SystemTime::now();
    let n = c.len();

    let (mut f, mut g) = pri_key;
    f.make_sparse();
    g.make_sparse();

    let mut cg = c.clone();
    cg *= &g;

    let mut a = BitField::new_dense(n);
    let mut b = BitField::new_dense(n);

    let mut num_a_bits_left = h;
    let mut num_b_bits_left = h;

    for iter in 0.. {
        let threshold = get_threshold_for_parameters(n, h, iter);

        let potential_a_bits = get_possible_coefficient_bits(&cg, &f, threshold);
        let potential_b_bits = get_possible_coefficient_bits(&cg, &g, threshold);

        let num_a_bits_obtained = potential_a_bits.len();
        let num_b_bits_obtained = potential_b_bits.len();
        num_a_bits_left = std::cmp::max(0, num_a_bits_left - num_a_bits_obtained);
        num_b_bits_left = std::cmp::max(0, num_b_bits_left - num_b_bits_obtained);

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

        if num_a_bits_left == 0 && num_b_bits_left == 0 {
            break;
        }
        if num_a_bits_obtained == 0 && num_b_bits_obtained == 0 {
            break;
        }
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
