#[macro_use]
extern crate log;
extern crate env_logger;

#[macro_use]
extern crate pts;

use pts::*;

fn main() {
    env_logger::init().unwrap();
    let term1: Term<Coc> =
        pi!(
            "a", sort!(StarAndBox::Star),
            var!("a")
        );
    let term2 =
        pi!(
            "a", sort!(StarAndBox::Star),
            var!("a")
        );
    if let Term::Pi(ref bind1, ref left1, ref right1) = term1 {
        if let Term::Pi(ref bind2, ref left2, ref right2) = term2 {
            let left_cmp = left1.alpha_eq(left2);
            let right_cmp = right1.alpha_eq(&right2.clone().substitute(&bind2, &Term::Var(bind1.clone())));
            println!("{}", left_cmp);
            println!("{}", right_cmp);
            println!("{}", left_cmp && right_cmp);
        }
    }
    println!("{}", term1.alpha_eq(&term1.clone()));
}
