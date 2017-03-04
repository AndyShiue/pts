#[macro_use]
extern crate log;
extern crate env_logger;

#[macro_use]
extern crate pts;

use pts::system::Coc;
use pts::syntax::parse;

fn main() {
    env_logger::init().unwrap();
    println!("{:?}", parse::<Coc>(b"a b"))
}
