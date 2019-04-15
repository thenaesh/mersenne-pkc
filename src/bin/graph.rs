use mersennepkc::*;
use crate::bit_field::BitField;
use std::io::Write;
use std::vec::Vec;
use std::iter::Iterator;
use std::collections::HashSet;
use std::collections::HashMap;
use std::{i64, f64};
use std::time::SystemTime;
extern crate plotlib;
use plotlib::scatter::Scatter;
use plotlib::scatter;
use plotlib::style::{Marker, Point};
use plotlib::view::View;
use plotlib::page::Page;

const N: usize = 86243;
const H: usize = 128;

fn main() {
    let start_time = SystemTime::now();

    println!("n = {}, h = {}", N, H);
    generate_and_plot_frequencies(N, H);

    println!("Elapsed Time: {}s", start_time.elapsed().unwrap().as_secs());
}

fn generate_and_plot_frequencies(n: usize, h: usize) {
    let mut expected_frequency_map = HashMap::<i64, usize>::new();
    let mut unexpected_max_frequency_map = HashMap::<i64, usize>::new();
    let mut expected_min_frequency_map = HashMap::<i64, usize>::new();
    let mut expected_max_frequency_map = HashMap::<i64, usize>::new();

    let mut expected_frequency_map_after = HashMap::<i64, usize>::new();
    let mut unexpected_max_frequency_map_after = HashMap::<i64, usize>::new();
    let mut expected_min_frequency_map_after = HashMap::<i64, usize>::new();
    let mut expected_max_frequency_map_after = HashMap::<i64, usize>::new();

    let threshold = get_threshold_for_parameters(n, h, 0);

    for i in 0..100 {
        let (pub_key, (f, g), (a, b), c) = initialize(n, h);

        let mut cg = c.clone();
        cg *= &g;
        let (deltas, xs, y, w, z) = generate_reductions(n, &f, &a, &cg);

        unexpected_max_frequency_map.insert(y, match unexpected_max_frequency_map.get(&y) {
            Some(a) => a + 1,
            None => 1,
        });

        expected_min_frequency_map.insert(w, match expected_min_frequency_map.get(&z) {
            Some(a) => a + 1,
            None => 1,
        });

        expected_max_frequency_map.insert(z, match expected_max_frequency_map.get(&z) {
            Some(a) => a + 1,
            None => 1,
        });

        for x in xs {
            expected_frequency_map.insert(x, match expected_frequency_map.get(&x) {
                Some(b) => b + 1,
                None => 1,
            });
        }

        let mut partial_a = BitField::new_dense(n);
        for (idx, hwc) in deltas.iter() {
            if *hwc >= threshold {
                partial_a.set(*idx);
            }
        }

        let mut a = a.clone();
        a -= &partial_a;

        let mut subtrahend = partial_a.clone();
        subtrahend *= &f;
        let mut cg = c.clone();
        cg *= &g;
        cg -= &subtrahend;

        let (deltas, xs, y, w, z) = generate_reductions(n, &f, &a, &cg);

        unexpected_max_frequency_map_after.insert(y, match unexpected_max_frequency_map_after.get(&y) {
            Some(a) => a + 1,
            None => 1,
        });

        expected_min_frequency_map_after.insert(w, match expected_min_frequency_map_after.get(&z) {
            Some(a) => a + 1,
            None => 1,
        });

        expected_max_frequency_map_after.insert(z, match expected_max_frequency_map_after.get(&z) {
            Some(a) => a + 1,
            None => 1,
        });

        for x in xs {
            expected_frequency_map_after.insert(x, match expected_frequency_map_after.get(&x) {
                Some(b) => b + 1,
                None => 1,
            });
        }

        print!("\r                                                \rIterations: {}", i + 1);
        std::io::stdout().flush().ok().expect("Error flushing stdout!");
    }
    println!("");

    // First Run

    let expected_points: Vec<(f64, f64)> = expected_frequency_map.iter().map(|(hw, freq)| (*hw as f64, *freq as f64)).collect();
    let unexpected_max_points: Vec<(f64, f64)> = unexpected_max_frequency_map.iter().map(|(hw, freq)| (*hw as f64, *freq as f64)).collect();
    let expected_min_points: Vec<(f64, f64)> = expected_min_frequency_map.iter().map(|(hw, freq)| (*hw as f64, *freq as f64)).collect();
    let expected_max_points: Vec<(f64, f64)> = expected_max_frequency_map.iter().map(|(hw, freq)| (*hw as f64, *freq as f64)).collect();

    println!("First Run: {} expected points, {} unexpected max points, {} expected min points, {} expected max points",
        expected_points.iter().fold(0., |acc, (_, n)| acc + n),
        unexpected_max_points.iter().fold(0., |acc, (_, n)| acc + n),
        expected_min_points.iter().fold(0., |acc, (_, n)| acc + n),
        expected_max_points.iter().fold(0., |acc, (_, n)| acc + n));

    plot_frequencies(&format!("graphs/freq_plot_{}_{}_first.svg", n.to_string(), h.to_string()), &expected_points, &unexpected_max_points, &expected_min_points, &expected_max_points);

    let (ex_mean, ex_var) = get_mean_and_variance(expected_points);
    let (unex_max_mean, unex_max_var) = get_mean_and_variance(unexpected_max_points);
    let (ex_min_mean, ex_min_var) = get_mean_and_variance(expected_min_points);
    let (ex_max_mean, ex_max_var) = get_mean_and_variance(expected_max_points);

    println!("Expected Points: mean = {}, stddev = {}", ex_mean, ex_var.sqrt());
    println!("Unexpected Max Points: mean = {}, stddev = {}", unex_max_mean, unex_max_var.sqrt());
    println!("Expected Min Points: mean = {}, stddev = {}", ex_min_mean, ex_min_var.sqrt());
    println!("Expected Max Points: mean = {}, stddev = {}", ex_max_mean, ex_max_var.sqrt());

    // Second Run

    let expected_points: Vec<(f64, f64)> = expected_frequency_map_after.iter().map(|(hw, freq)| (*hw as f64, *freq as f64)).collect();
    let unexpected_max_points: Vec<(f64, f64)> = unexpected_max_frequency_map_after.iter().map(|(hw, freq)| (*hw as f64, *freq as f64)).collect();
    let expected_min_points: Vec<(f64, f64)> = expected_min_frequency_map_after.iter().map(|(hw, freq)| (*hw as f64, *freq as f64)).collect();
    let expected_max_points: Vec<(f64, f64)> = expected_max_frequency_map_after.iter().map(|(hw, freq)| (*hw as f64, *freq as f64)).collect();

    println!("Second Run: {} expected points, {} unexpected max points, {} expected min points, {} expected max points",
        expected_points.iter().fold(0., |acc, (_, n)| acc + n),
        unexpected_max_points.iter().fold(0., |acc, (_, n)| acc + n),
        expected_min_points.iter().fold(0., |acc, (_, n)| acc + n),
        expected_max_points.iter().fold(0., |acc, (_, n)| acc + n));

    plot_frequencies(&format!("graphs/freq_plot_{}_{}_second.svg", n.to_string(), h.to_string()), &expected_points, &unexpected_max_points, &expected_min_points, &expected_max_points);

    let (ex_mean, ex_var) = get_mean_and_variance(expected_points);
    let (unex_max_mean, unex_max_var) = get_mean_and_variance(unexpected_max_points);
    let (ex_min_mean, ex_min_var) = get_mean_and_variance(expected_min_points);
    let (ex_max_mean, ex_max_var) = get_mean_and_variance(expected_max_points);

    println!("Expected Points: mean = {}, stddev = {}", ex_mean, ex_var.sqrt());
    println!("Unexpected Max Points: mean = {}, stddev = {}", unex_max_mean, unex_max_var.sqrt());
    println!("Expected Min Points: mean = {}, stddev = {}", ex_min_mean, ex_min_var.sqrt());
    println!("Expected Max Points: mean = {}, stddev = {}", ex_max_mean, ex_max_var.sqrt());
}

fn plot_frequencies(output_filename: &str, expected_points: &Vec<(f64, f64)>, unexpected_max_points: &Vec<(f64, f64)>, expected_min_points: &Vec<(f64, f64)>, expected_max_points: &Vec<(f64, f64)>) {
    println!("Plotting Frequency Graph: {}", output_filename);


    let (expected_max_hw, expected_max_freq) = expected_points.iter()
        .fold((0. as f64, 0. as f64), |(acc_hw, acc_freq), (x, y)| (acc_hw.max(*x), acc_freq.max(*y)));

    let (unexpected_max_hw, unexpected_max_freq) = unexpected_max_points.iter()
        .fold((0. as f64, 0. as f64), |(acc_hw, acc_freq), (x, y)| (acc_hw.max(*x), acc_freq.max(*y)));

    let (max_hw, max_freq) = (expected_max_hw.max(unexpected_max_hw), expected_max_freq.max(unexpected_max_freq));

    println!("Expected: {:?}", expected_points);
    println!("Unexpected: {:?}", unexpected_max_points);
    println!("Expected Min: {:?}", expected_min_points);
    println!("Expected Max: {:?}", expected_max_points);

    let s1 = Scatter::from_vec(unexpected_max_points.as_slice())
        .style(scatter::Style::new()
            .marker(Marker::Square)
            .colour("#222222"));

    let s2 = Scatter::from_vec(expected_points.as_slice())
        .style(scatter::Style::new()
            .colour("#0000FF"));

    let s3 = Scatter::from_vec(expected_min_points.as_slice())
        .style(scatter::Style::new()
            .colour("#FF0000"));

    let s4 = Scatter::from_vec(expected_max_points.as_slice())
        .style(scatter::Style::new()
            .colour("#00FF00"));

    let v = View::new()
        .add(&s1)
        .add(&s2)
        .add(&s3)
        .add(&s4)
        .x_range(0., max_hw)
        .y_range(0., max_freq)
        .x_label("Hamming Weight Reduction")
        .y_label("Frequency");

    Page::single(&v).save(output_filename);

    println!("Done");
}

fn initialize(n: usize, h: usize) -> (PublicKey, PrivateKey, PlainText, CipherText) {
    let (f, g) = randomly_generate_message(n, h);

    let mut pub_key = f.clone();
    pub_key /= &g;

    let msg = randomly_generate_message(n, h);

    let c = encrypt(msg.clone(), pub_key.clone());

    (pub_key, (f, g), msg, c)
}

fn generate_reductions(n: usize, f: &BitField, a: &BitField, cg: &BitField) -> (Vec<(usize, i64)>, Vec<i64>, i64, i64, i64) {
    let mut cg = cg.clone();
    cg.extend_self(1);
    cg.make_sparse();
    cg.set(n);

    // we just care about the values of a, since the results will be similar for b
    let deltas: Vec<(usize, i64)> = (0..n).map(|i| (i, delta_efficient(&cg, &f, i))).collect();
    let expected_bits = a.all_set_bits_hashset();

    let expected_point_hamming_weight_reductions: Vec<i64> = deltas.iter()
        .filter(|(i, x)| expected_bits.contains(i))
        .map(|(i, x)| *x)
        .collect();

    let unexpected_points_max_hamming_weight_reduction = deltas.iter()
        .filter(|(i, x)| !expected_bits.contains(i))
        .fold(i64::MIN, |acc, (_, x)| acc.max(*x));

    let expected_points_min_hamming_weight_reduction = deltas.iter()
        .filter(|(i, x)| expected_bits.contains(i))
        .fold(i64::MAX, |acc, (_, x)| acc.min(*x));

    let expected_points_max_hamming_weight_reduction = deltas.iter()
        .filter(|(i, x)| expected_bits.contains(i))
        .fold(i64::MIN, |acc, (_, x)| acc.max(*x));

    (deltas, expected_point_hamming_weight_reductions, unexpected_points_max_hamming_weight_reduction, expected_points_min_hamming_weight_reduction, expected_points_max_hamming_weight_reduction)
}

fn delta(minuend: &BitField, subtrahend: &BitField, shift_amt: usize) -> i64 {
    let original_hw = minuend.hamming_weight() as i64;

    let mut subtrahend = subtrahend.clone();
    subtrahend <<= shift_amt;

    let mut difference = minuend.clone();
    difference -= &subtrahend;

    let new_hw = difference.hamming_weight() as i64;

    original_hw - new_hw
}

fn delta_efficient(minuend: &BitField, subtrahend: &BitField, shift_amt: usize) -> i64 {
    let mut subtrahend = subtrahend.clone();
    subtrahend <<= shift_amt;
    subtrahend.normalize();
    subtrahend.extend_self(1);
    minuend.hamming_weight_change_upon_subtraction(subtrahend)
}

fn get_mean_and_variance(data: Vec<(f64, f64)>) -> (f64, f64) {
    let mean = {
        let (sum, n) = data.iter().fold((0., 0.), |(sum, n), (hw, freq)| (sum + *hw * *freq, n + *freq));
        sum / n
    };

    let variance = {
        let (var, n) = data.iter().fold((0., 0.), |(sumsq, n), (hw, freq)| {
            let delta = *hw - mean;
            (sumsq + freq * delta * delta, n + freq)
        });
        var / (n - 1.)
    };

    (mean, variance)
}
