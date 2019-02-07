use mersennepkc::*;
use crate::bit_field::BitField;
use std::vec::Vec;
use std::iter::Iterator;
use std::collections::HashSet;
use std::i64;
extern crate plotlib;
use plotlib::scatter::Scatter;
use plotlib::scatter;
use plotlib::style::{Marker, Point};
use plotlib::view::View;
use plotlib::page::Page;

fn main() {
    let n = 19937;
    let h = 64;

    generate_and_plot(n, h);
}

fn generate_and_plot(n: usize, h: usize) {
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

    plot_graph(&format!("graphs/f_plot_{}_{}.svg", n.to_string(), h.to_string()), n, f_deltas, a_bits);
    plot_graph(&format!("graphs/g_plot_{}_{}.svg", n.to_string(), h.to_string()), n, g_deltas, b_bits);
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

fn plot_graph(output_filename: &str, n: usize, deltas: Vec<(usize, i64)>, expected_point_indices: HashSet<usize>) {
    println!("Plotting Graph: {}", output_filename);

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
