use mersennepkc::*;
use mersennepkc::mersenne_field::MersenneField;

fn main() {
    let n = 17;
    let h = 5;

    let (f, g) = randomly_generate_message(n, h);
    println!("F, G: {}, {}", f.to_string(), g.to_string());

    let mut pub_key = f.clone();
    pub_key /= &g;

    let pri_key = (f, g);

    let (a, b) = randomly_generate_message(n, h);
    println!("Original Plaintext: {}, {}", a.to_string(), b.to_string());

    let c = encrypt((a, b), pub_key, h);
    let (aa, bb) = decrypt(c, pri_key, h);
    println!("Original Plaintext: {}, {}", aa.to_string(), bb.to_string());
}
