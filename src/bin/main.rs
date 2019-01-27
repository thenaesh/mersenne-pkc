use mersennepkc::*;

fn main() {
    //let n = 4423;
    let n = 19937;
    let h = 64;

    let (f, g) = randomly_generate_message(n, h);
    println!("F, G: {}, {}", f.to_string(), g.to_string());

    let mut pub_key = f.clone();
    pub_key /= &g;

    let pri_key = (f, g);

    let msg = randomly_generate_message(n, h);
    let (a,b) = msg.clone();

    let c = encrypt(msg, pub_key, h);
    let (aa, bb) = decrypt(c, pri_key, h);

    println!("Original A Bits : {:?}", a.set_bits());
    println!("Decrypted A Bits: {:?}", aa.set_bits());
    println!("Original B Bits : {:?}", b.set_bits());
    println!("Decrypted B Bits: {:?}", bb.set_bits());
}
