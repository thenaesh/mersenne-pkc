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

fn main() {
    let ns = vec![86243];
    let hs = vec![128];

    let start_time = SystemTime::now();

    for h in hs.iter() {
        for n in ns.iter() {
            println!("n = {}, h = {}", *n, *h);
            let (ex_mean, ex_var, unex_max_mean, unex_max_var, ex_min_mean, ex_min_var, ex_max_mean, ex_max_var) = generate_and_plot_frequencies(*n, *h);
            println!("Expected Points: mean = {}, stddev = {}", ex_mean, ex_var.sqrt());
            println!("Unexpected Max Points: mean = {}, stddev = {}", unex_max_mean, unex_max_var.sqrt());
            println!("Expected Min Points: mean = {}, stddev = {}", ex_min_mean, ex_min_var.sqrt());
            println!("Expected Max Points: mean = {}, stddev = {}", ex_max_mean, ex_max_var.sqrt());
        }
    }

    println!("Elapsed Time: {}s", start_time.elapsed().unwrap().as_secs());
}

fn generate_and_plot_frequencies(n: usize, h: usize) -> (f64, f64, f64, f64, f64, f64, f64, f64) {
    let mut expected_frequency_map = HashMap::<i64, usize>::new();
    let mut unexpected_max_frequency_map = HashMap::<i64, usize>::new();
    let mut expected_min_frequency_map = HashMap::<i64, usize>::new();
    let mut expected_max_frequency_map = HashMap::<i64, usize>::new();

    for i in 0..5000 {
        let (xs, y, w, z) = generate_reductions(n, h);

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

        print!("\r                                                \rIterations: {}", i + 1);
        std::io::stdout().flush().ok().expect("Error flushing stdout!");
    }
    println!("");

    let expected_points: Vec<(f64, f64)> = expected_frequency_map.iter().map(|(hw, freq)| (*hw as f64, *freq as f64)).collect();
    let unexpected_max_points: Vec<(f64, f64)> = unexpected_max_frequency_map.iter().map(|(hw, freq)| (*hw as f64, *freq as f64)).collect();
    let expected_min_points: Vec<(f64, f64)> = expected_min_frequency_map.iter().map(|(hw, freq)| (*hw as f64, *freq as f64)).collect();
    let expected_max_points: Vec<(f64, f64)> = expected_max_frequency_map.iter().map(|(hw, freq)| (*hw as f64, *freq as f64)).collect();

    println!("{} expected points, {} unexpected max points, {} expected min points, {} expected max points",
        expected_points.iter().fold(0., |acc, (_, n)| acc + n),
        unexpected_max_points.iter().fold(0., |acc, (_, n)| acc + n),
        expected_min_points.iter().fold(0., |acc, (_, n)| acc + n),
        expected_max_points.iter().fold(0., |acc, (_, n)| acc + n));

    plot_frequencies(&format!("graphs/freq_plot_{}_{}.svg", n.to_string(), h.to_string()), &expected_points, &unexpected_max_points, &expected_min_points, &expected_max_points);

    let expected_points_sample_mean = {
        let (sum, n) = expected_points.iter().fold((0., 0.), |(sum, n), (hw, freq)| (sum + *hw * *freq, n + *freq));
        sum / n
    };
    let expected_points_sample_variance = {
        let (var, n) = expected_points.iter().fold((0., 0.), |(sumsq, n), (hw, freq)| {
            let delta = *hw - expected_points_sample_mean;
            (sumsq + freq * delta * delta, n + freq)
        });
        var / (n - 1.)
    };

    let unexpected_max_points_sample_mean = {
        let (sum, n) = unexpected_max_points.iter().fold((0., 0.), |(sum, n), (hw, freq)| (sum + *hw * *freq, n + *freq));
        sum / n
    };
    let unexpected_max_points_sample_variance = {
        let (var, n) = unexpected_max_points.iter().fold((0., 0.), |(sumsq, n), (hw, freq)| {
            let delta = *hw - unexpected_max_points_sample_mean;
            (sumsq + freq * delta * delta, n + freq)
        });
        var / (n - 1.)
    };

    let expected_min_points_sample_mean = {
        let (sum, n) = expected_min_points.iter().fold((0., 0.), |(sum, n), (hw, freq)| (sum + *hw * *freq, n + *freq));
        sum / n
    };
    let expected_min_points_sample_variance = {
        let (var, n) = expected_min_points.iter().fold((0., 0.), |(sumsq, n), (hw, freq)| {
            let delta = *hw - expected_min_points_sample_mean;
            (sumsq + freq * delta * delta, n + freq)
        });
        var / (n - 1.)
    };

    let expected_max_points_sample_mean = {
        let (sum, n) = expected_max_points.iter().fold((0., 0.), |(sum, n), (hw, freq)| (sum + *hw * *freq, n + *freq));
        sum / n
    };
    let expected_max_points_sample_variance = {
        let (var, n) = expected_max_points.iter().fold((0., 0.), |(sumsq, n), (hw, freq)| {
            let delta = *hw - expected_max_points_sample_mean;
            (sumsq + freq * delta * delta, n + freq)
        });
        var / (n - 1.)
    };

    (expected_points_sample_mean, expected_points_sample_variance,
        unexpected_max_points_sample_mean, unexpected_max_points_sample_variance,
        expected_min_points_sample_mean, expected_min_points_sample_variance,
        expected_max_points_sample_mean, expected_max_points_sample_variance)
}

fn generate_and_plot_points(n: usize, h: usize) {
    let start_time = SystemTime::now();

    let (f, g) = randomly_generate_message(n, h);
    println!("F, G: {:?}, {:?}", f.all_set_bits(), g.all_set_bits());

    let mut pub_key = f.clone();
    pub_key /= &g;

    let msg = randomly_generate_message(n, h);
    let (a,b) = msg.clone();

    let mut c = encrypt(msg, pub_key, h);
    c *= &g;

    let mut c = c.extend(1);
    c.make_sparse();
    c.set(n);

    let f_deltas: Vec<(usize, i64)> = (0..n).map(|i| (i, delta_efficient(&c, &f, i))).collect();
    let a_bits = a.all_set_bits_hashset();

    let g_deltas: Vec<(usize, i64)> = (0..n).map(|i| (i, delta_efficient(&c, &g, i))).collect();
    let b_bits = b.all_set_bits_hashset();

    plot_points(&format!("graphs/f_plot_{}_{}.svg", n.to_string(), h.to_string()), n, f_deltas, a_bits);
    plot_points(&format!("graphs/g_plot_{}_{}.svg", n.to_string(), h.to_string()), n, g_deltas, b_bits);
    println!("Elapsed Time: {}s", start_time.elapsed().unwrap().as_secs());
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

fn plot_points(output_filename: &str, n: usize, deltas: Vec<(usize, i64)>, expected_point_indices: HashSet<usize>) {
    println!("Plotting Point Graph: {}", output_filename);

    let number_of_points = deltas.len();

    let min_hw = deltas.iter().fold(i64::MAX, |acc, (_, x)| acc.min(*x));
    let max_hw = deltas.iter().fold(i64::MIN, |acc, (_, x)| acc.max(*x));

    let expected_points: Vec<(f64, f64)> = deltas.iter().filter(|(i, x)| expected_point_indices.contains(i)).map(|(i, x)| (*i as f64, *x as f64)).collect();
    let unexpected_points: Vec<(f64, f64)> = deltas.iter().filter(|(i, x)| !expected_point_indices.contains(i)).map(|(i, x)| (*i as f64, *x as f64)).collect();

    // We create our scatter plot from the data
    let s1 = Scatter::from_vec(expected_points.as_slice())
        .style(scatter::Style::new()
            .marker(Marker::Square) // setting the marker to be a square
            .colour("#DD3355")); // and a custom colour

    let s2 = Scatter::from_vec(unexpected_points.as_slice())
        .style(scatter::Style::new() // uses the default marker
            .colour("#35C788")); // and a different colour

    // The 'view' describes what set of data is drawn
    let v = View::new()
        .add(&s1)
        .add(&s2)
        .x_range(0., number_of_points as f64)
        .y_range(min_hw as f64, max_hw as f64)
        .x_label("Index")
        .y_label("Hamming Weight Reduction");

    // A page with a single view is then saved to an SVG file
    Page::single(&v).save(output_filename);

    println!("Done");
}

fn generate_reductions(n: usize, h: usize) -> (Vec<i64>, i64, i64, i64) {
    let (f, g) = randomly_generate_message(n, h);

    let mut pub_key = f.clone();
    pub_key /= &g;

    let msg = randomly_generate_message(n, h);
    let (a,b) = msg.clone();

    let mut c = encrypt(msg, pub_key, h);
    c *= &g;

    let mut c = c.extend(1);
    c.make_sparse();
    c.set(n);

    // we just care about the values of a, since the results will be similar for b
    let deltas: Vec<(usize, i64)> = (0..n).map(|i| (i, delta_efficient(&c, &f, i))).collect();
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

    (expected_point_hamming_weight_reductions, unexpected_points_max_hamming_weight_reduction, expected_points_min_hamming_weight_reduction, expected_points_max_hamming_weight_reduction)
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
    let subtrahend = subtrahend.extend(1);
    minuend.hamming_weight_change_upon_subtraction(subtrahend)
}
