use mersennepkc::*;

fn main() {
    let n = 86243;
    let h = 128;

    let (f, g) = randomly_generate_message(n, h);

    let mut pub_key = f.clone();
    pub_key /= &g;

    let pri_key = (f, g);

    let msg = randomly_generate_message(n, h);
    let (a,b) = msg.clone();

    let c = encrypt(msg, pub_key);
    let (aa, bb) = decrypt(c, pri_key, n, h);

    println!("Original A Bits : {:?}", a.all_set_bits());
    println!("Decrypted A Bits: {:?}", aa.all_set_bits());
    println!("Original B Bits : {:?}", b.all_set_bits());
    println!("Decrypted B Bits: {:?}", bb.all_set_bits());

    let alice_session_key = extract_128_bit_key(&(a,b));
    let bob_session_key = extract_128_bit_key(&(aa, bb));

    println!("Alice\'s Session Key : {}", alice_session_key);
    println!("Bob\'s Session Key   : {}", bob_session_key);
}
