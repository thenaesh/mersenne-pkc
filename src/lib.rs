pub mod finite_ring;
pub mod mersenne_field;
pub mod bit_field;

use std::time::SystemTime;
use std::cmp::min;
use std::sync::mpsc::channel;
use threadpool::ThreadPool;
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
    let mut pool = ThreadPool::new(N_WORKERS);
    let start_time = SystemTime::now();
    let n = c.len();
    let mut z = c;
    let (f, g) = pri_key;

    z *= &g;

    let mut f_indices: Vec<usize> = Vec::with_capacity(h);
    let mut g_indices: Vec<usize> = Vec::with_capacity(h);

    while f_indices.len() < h {
        let vec = pick_smallest_subtraction_powers(&z, &f, &mut pool);
        let mut i = 0;
        let mut p = &vec[i];
        while f_indices.contains(&p.0) {
            i += 1;
            if i >= vec.len() {
                break;
            }
            p = &vec[i];
        }
        let (idx, _) = p;
        //z = shift_and_subtract(z.clone(), f.clone(), *idx);
        z = shift_and_subtract(&z, &f, *idx);
        f_indices.push(idx.clone());
        println!("Obtained {} out of {} indices for A... Elapsed Time: {}s", f_indices.len(), h, start_time.elapsed().unwrap().as_secs());
    }

    while g_indices.len() < h {
        let vec = pick_smallest_subtraction_powers(&z, &g, &mut pool);
        let mut i = 0;
        let mut p = &vec[i];
        while g_indices.contains(&p.0) {
            i += 1;
            if i >= vec.len() {
                break;
            }
            p = &vec[i];
        }
        let (idx, _) = p;
        //z = shift_and_subtract(z.clone(), g.clone(), *idx);
        z = shift_and_subtract(&z, &g, *idx);
        g_indices.push(idx.clone());
        println!("Obtained {} out of {} indices for B... Elapsed Time: {}s", g_indices.len(), h, start_time.elapsed().unwrap().as_secs());
    }

    let a = BitField::Sparse(n, f_indices, FiniteRing::new(n, 0));
    let b = BitField::Sparse(n, g_indices, FiniteRing::new(n, 0));

    (a, b)
}

fn pick_smallest_subtraction_powers(z: &BitField, s: &BitField, pool: &mut ThreadPool) -> Vec<(usize, i64)> {
    let n = z.len();
    let n_items_per_job = (n / N_JOBS) + 1;

    // ensure z >= s
    let mut z = z.clone();
    z.normalize();

    let (tx, rx) = channel();
    for i in 0..N_JOBS {
        let z = z.as_sparse();
        let s = s.as_sparse();

        let tx = tx.clone();
        pool.execute(move || {
            let start_idx = i * n_items_per_job;
            let end_idx = min(n, start_idx + n_items_per_job);

            let mut subtraction_powers_and_values = (start_idx..end_idx)
                .map(|idx| {
                    /*
                    let d_i = shift_and_subtract(&z, &s, idx);
                    (idx, d_i.hamming_weight())
                    */
                    let mut s = s.clone();
                    s <<= idx;
                    s.normalize();
                    (idx, z.hamming_weight_change_upon_subtraction(s))
                })
                .collect::<Vec<(usize, i64)>>();

            subtraction_powers_and_values.sort_unstable_by_key(|p| p.1);
            tx.send(subtraction_powers_and_values[0]);
        });
    }

    let mut result: Vec<(usize, i64)> = Vec::new();
    for p in rx.iter().take(N_JOBS) {
        result.push(p);
    }
    result.sort_unstable_by_key(|p| p.1);
    result
}

fn shift_and_subtract(z: &BitField, s: &BitField, idx: usize) -> BitField {
    let mut d_i = z.clone();
    let mut ss = s.clone();
    ss <<= idx;
    d_i -= &ss;
    d_i
}
