mod finite_ring;
pub mod mersenne_field;

use std::time::SystemTime;
use std::cmp::min;
use std::sync::mpsc::channel;
use threadpool::ThreadPool;
use crate::mersenne_field::MersenneField;

pub type PublicKey = MersenneField;
pub type PrivateKey = (MersenneField, MersenneField);

pub type PlainText = (MersenneField, MersenneField);
pub type CipherText = MersenneField;

const n_workers: usize = 8;
const n_jobs: usize = 8;

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
    let mut pool = ThreadPool::new(n_workers);
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

fn pick_smallest_subtraction_powers(z: &MersenneField, s: &MersenneField, pool: &mut ThreadPool) -> Vec<(usize, usize)> {
    let n = z.len();
    let n_items_per_job = (n / n_jobs) + 1;

    let (tx, rx) = channel();
    for i in 0..n_jobs {
        let z = z.clone();
        let s = s.clone();

        let tx = tx.clone();
        pool.execute(move || {
            let start_idx = i * n_items_per_job;
            let end_idx = min(n, start_idx + n_items_per_job);

            let mut subtraction_powers_and_values = (start_idx..end_idx)
                .map(|idx| {
                    let d_i = shift_and_subtract(&z, &s, idx);
                    (idx, d_i.hamming_weight())
                })
                .collect::<Vec<(usize, usize)>>();

            subtraction_powers_and_values.sort_unstable_by_key(|p| p.1);
            tx.send(subtraction_powers_and_values[0]);
        });
    }

    let mut result: Vec<(usize, usize)> = Vec::new();
    for p in rx.iter().take(n_jobs) {
        result.push(p);
    }
    result.sort_unstable_by_key(|p| p.1);
    result
}

fn shift_and_subtract(z: &MersenneField, s: &MersenneField, idx: usize) -> MersenneField {
    let mut d_i = z.clone();
    let mut ss = s.clone();
    ss <<= idx;
    d_i -= &ss;
    d_i
}
