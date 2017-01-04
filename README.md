# PTS (Pure Type Systems)

[![Build Status](https://travis-ci.org/AndyShiue/pts.svg?branch=master)](https://travis-ci.org/AndyShiue/pts)

This is an implementation of *pure type systems* written in Rust.
It's basically a rewrite from the Haskell version, [Simpler, Easier!](http://augustss.blogspot.tw/2007/10/simpler-easier-in-recent-paper-simply.html)

---

Installation:

1. First make sure [Rust](https://www.rust-lang.org/en-US/) (and obviously also [`git`](https://git-scm.com)) has already been installed on your machine.

2. Clone this repository: `git clone https://github.com/AndyShiue/pts.git`

3. Navigate to the root of the project: `cd pts`

4. Run `cargo test` to run all the tests in the project. It might take some time.

---

Originally, lambda calculus is invented to be a Turing-complete model of computation.
Subsequent works add type systems on top of the lambda calculus, usually making it **not** Turing-complete, but stronger type systems lead to the ability to write mathematical proofs in it.
Pure type systems are a generalization of the lambda cube, which consists of the simply typed lambda calculus, system F, calculus of constructions, etc.
In this implementation, you can define your own pure type systems, consisting one or more, or even infinite sorts.
Currently, this project can only be used as a library, not an application, because I haven't dealt with parsing stuff.
See the tests at the end [of the source code](https://github.com/AndyShiue/pts/blob/master/src/lib.rs) and also the comments for thorough explanation of the algorithms.
