# MersennePKC

MersennePKC is a post-quantum cryptosystem adapted from [this paper](https://eprint.iacr.org/2017/481.pdf). It is based on the hardness of distinguishing a quotient of two numbers with small Hamming weight in a finite field whose order is some Mersenne prime.

This repository contains the report detailing the construction of MersennePKC as well as an implementation of MersennePKC as a library. There are two programs: the first (in _main.rs_) is a sample program that does an encryption and decryption proof of concept, while the second (in _graph.rs_) plots graphs that were used to verify the correctness of MersennePKC.

## Usage

Compiling MersennePKC requires the Rust compiler (version >= 1.34) and an installation of Cargo. Rust and Cargo can be installed easily by using [Rustup](https://rustup.rs/).

* To compile a release build, perform `cargo build --release`. To compile a debug build, perform `cargo build`.
* To run the test suite, perform `cargo test`.
* To run the proof of concept sample program, perform `cargo run --release --bin main`.
* To run the graph plotting program, perform `cargo run --release --bin graph`.

## Directory Structure

| Directory | Contents |
| --------- | -------- |
| _report/_ | LaTeX sources and figures for the report |
| _src/_ | Source code |
| _src/bin/main.rs_ | Proof of concept program |
| _src/bin/graph.rs_ | Analysis and graph plotting program |
| __src/lib.rs_ | MersennePKC library functions |
