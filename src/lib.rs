// This is for debugging.
#[macro_use]
extern crate log;

use std::fmt::{self, Debug, Display};
use std::hash::Hash;
use std::collections::{HashSet, HashMap};

// A newtype wrapper representing a symbol.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Symbol(pub String);

impl Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// The type of terms generic over pure type systems.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term<System: PureTypeSystem> {
    Var(Symbol),
    App(Box<Term<System>>, Box<Term<System>>),
    Lam(Symbol, Box<Term<System>>, Box<Term<System>>),
    Pi(Symbol, Box<Term<System>>, Box<Term<System>>),
    Sort(System::Sort),
}

impl<System: PureTypeSystem> Display for Term<System> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Term::*;
        match *self {
            Var(Symbol(ref str)) => write!(f, "{}", str),
            App(ref left, ref right) => write!(f, "({} {})", left, right),
            Lam(ref bound, ref ty, ref inner) => write!(f, "(\\{}: {}. {})", bound, ty, inner),
            Pi(ref bound, ref left, ref right) => write!(f, "({}: {}) -> {}", bound, left, right),
            Sort(ref sort) => write!(f, "{}", sort),
        }
    }
}

// Below, I provide several macros for generating terms easily.
// (Explicitly writing out `Box`es is utterly cumbersome.)

#[macro_export]
macro_rules! var {
    ($str: expr) => { Term::Var(Symbol($str.into())) }
}

#[macro_export]
macro_rules! app {
    ($left: expr, $right: expr) => { Term::App(Box::new($left), Box::new($right)) }
}

#[macro_export]
macro_rules! lam {
    ($bound: expr, $ty: expr, $inner: expr) => {
        Term::Lam(Symbol($bound.into()), Box::new($ty), Box::new($inner))
    }
}

#[macro_export]
macro_rules! pi {
    ($bound: expr, $left: expr, $right: expr) => {
        Term::Pi(Symbol($bound.into()), Box::new($left), Box::new($right))
    }
}

// A degenerating case of the `Pi` constructor.
#[macro_export]
macro_rules! arrow {
    ($left: expr, $right: expr) => {
        pi!("x", $left, $right)
    }
}

#[macro_export]
macro_rules! sort {
    ($sort: expr) => {
        Term::Sort($sort)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum StarAndBox {
    Star,
    Box,
}

impl Display for StarAndBox {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::StarAndBox::*;
        match *self {
            Star => write!(f, "*"),
            Box => write!(f, "[]"),
        }
    }
}

// The trait classifying a pure type system.
// It consists of 3 things, respectively:
// 1. Its sort, this is represent as an associated type.
// 2. `axiom`, which is a function from any sort to its super-sort.
//    It returns an `Option` because some sort may not belong to any other sorts,
//    i.e. it's already the largest sort in the system.
// 3. `rule`, the purpose of this function is to specify the type of a function from the type of
//    its argument and its return type.
//    If a function has type T1 -> T2, the type of T1 is s1 and the type of T2 is s2,
//    then the type of the whole function is rule(s_1, s_2).
//    Again, `rule` returns an `Option` because the function type isn't always well-formed.
pub trait PureTypeSystem: Clone + Debug {
    type Sort: Copy + Clone + Debug + Display + Eq + Hash;
    fn axiom(sort: Self::Sort) -> Option<Self::Sort>;
    fn rule(s1: Self::Sort, s2: Self::Sort) -> Option<Self::Sort>;
}

// A private macro for generating pure type systems in the lambda cube.
macro_rules! lambda_cube {
    ($name: ident;
     $($rule_s1: pat, $rule_s2: pat => $rule_s3: expr),*) => {

        // The name of the pure type system.
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        pub struct $name;

        impl PureTypeSystem for $name {

            // In a system in the lambda cube, the only sorts available are always `Star` and `Box`
            type Sort = StarAndBox;

            // The type of `Star` is `Box`, and the `Box` is of no type.
            fn axiom(sort: StarAndBox) -> Option<StarAndBox> {
                use self::StarAndBox::*;
                match sort {
                    Star => Some(Box),
                    Box => None,
                }
            }

            // Everything the user of this macro needs to supply are the `rule`s.
            fn rule(s1: StarAndBox, s2: StarAndBox) -> Option<StarAndBox> {
                use self::StarAndBox::*;
                match (s1, s2) {
                    // The `if true` here is a small hack.
                    // Removing it makes `_` an unreachable pattern in `Coc`,
                    // making the program not to compile.
                    $(($rule_s1, $rule_s2) if true => Some($rule_s3),)*
                    _ => None,
                }
            }
        }

    }
}

// Below are the definitions of several systems in the lambda cube.

lambda_cube! {
    Stlc;
    Star, Star => Star
}

lambda_cube! {
    SystemF;
    Star, Star => Star,
    Box, Star => Star
}

lambda_cube! {
    SystemFOmega;
    Star, Star => Star,
    Box, Star => Star,
    Box, Box => Box
}

lambda_cube! {
    Coc;
    Star, Star => Star,
    Box, Star => Star,
    Box, Box => Box,
    Star, Box => Box
}

impl<System: PureTypeSystem> Term<System> {

    // The starting point of type checking.
    pub fn type_check(self) -> Result<Term<System>, String> {
        debug!("Start type checking.");
        self.type_check_with_context(HashMap::new())
    }

    // And the real implementation of the type checking.
    // We need to store typing information in a map called `context`.
    pub fn type_check_with_context(self, context: HashMap<Symbol, Term<System>>)
        -> Result<Term<System>, String> {
        use self::Term::*;
        match self {
            // Simply lookup the context if I hit a variable.
            Var(v) => {
                match context.get(&v) {
                    Some(ty) => Ok(ty.clone()),
                    None => Err(format!("Cannot find variable {}.", &v.0))
                }
            }
            // If I hit an application ...
            App(left, right) => {
                // First see if the left hand side type checks.
                let left_ty = try!(left.type_check_with_context(context.clone()));
                // If `left_ty` isn't a function in its `whnf` form, output an error.-------------+
                match left_ty.whnf() {                                                       //   |
                    Pi(bound, ty_in, ty_out) => {                                            //   |
                        // Let's then type check the right hand side.                             |
                        let right_ty = try!(right.clone()                                    //   |
                                                 .type_check_with_context(context.clone())); //   |
                        // If the type of the right hand side matches the type of the argument of |
                        // the `Pi` type, substitute the return type with the right hand side.    |
                        // The return type can have free occurences of the bound variable because |
                        // now we are working with dependent types.                               |
                        if right_ty.beta_eq(&ty_in) {                                        //   |
                            Ok(ty_out.substitute(&bound, &right))                            //   |
                        } else {                                                             //   |
                            // If the types doesn't match, return an error.                       |
                            Err(                                                             //   |
                                format!(                                                     //   |
                                    "Expected something of type {}, found that of type {}.", //   |
                                    ty_in, right_ty                                          //   |
                                )                                                            //   |
                            )                                                                //   |
                        }                                                                    //   |
                    }                                                                        //   |
                    left_ty =>                                                               //   |
                        Err(format!("Expected lambda, found value of type {}.", left_ty)) // <----+
                }
            }
            // If I hit a lambda ...
            Lam(bound, ty, inner) => {
                // Check if the type of the argument is well-formed, if it is, proceed ...
                try!(ty.clone().type_check_with_context(context.clone()));
                let mut new_context = context;
                // Insert the bound variable into the new context.
                new_context.insert(bound.clone(), *ty.clone());
                // And type check the right hand side of the lambda with the new context.
                let inner_type = try!(inner.type_check_with_context(new_context));
                Ok(Pi(bound, ty, Box::new(inner_type)))
            }
            // If I hit a `Pi` ...
            Pi(bound, left, right) => {
                // First, type check the type of the bound variable.
                // It must be a `Sort`, otherwise output an error.
                if let Sort(left_sort) = try!(left.clone()
                                                  .type_check_with_context(context.clone())
                                                  .map(Term::whnf)) {
                    // Create a new context, the same as what we did in the case of `Lam`.
                    let mut new_context = context;
                    // Insert the bound variable.
                    new_context.insert(bound, *left);
                    // type check the right hand side of the `Pi` with the new context.
                    let right_kind = try!(right.clone()
                                               .type_check_with_context(new_context)
                                               .map(Term::whnf));
                    // Again, check if the type of the return type is a `Sort`.
                    if let Sort(right_sort) = right_kind {
                        // Call `rule` to get the type of the whole function type.
                        let new_sort = System::rule(left_sort.clone(), right_sort.clone());
                        match new_sort {
                            Some(sort) => return Ok(Sort(sort.clone())),
                            // If such rule doesn't exist, output an error.
                            None => {
                                let error_message = format!("Rule ({}, {}, _) doesn't exist.",
                                                            left_sort, right_sort);
                                Err(error_message)
                            }
                        }
                    } else {
                        Err(format!("Type {} isn't inhabited.", right))
                    }
                } else {
                    Err(format!("Type {} isn't inhabited.", left))
                }
            }
            // Finally, type check the sorts. It's an easy case. We just need to call `axiom`.
            Sort(sort) => {
                match System::axiom(sort) {
                    Some(new_sort) => Ok(Sort(new_sort.clone())),
                    None => Err(format!("Sort {} doesn't have a super-sort.", sort)),
                }
            }
        }
    }

    // This function returns the set of free variables in a term and is used during substitution.
    pub fn free_vars(&self) -> HashSet<&Symbol> {
        use self::Term::*;
        let mut set;
        match *self {
            // If what we get is a variable ...
            Var(ref v) => {
                set = HashSet::new();
                // Then the only free variable is itself.
                set.insert(v);
            }
            // If it's an application, just merge the free variables in both sides of the term.
            App(ref left, ref right) => set = left.free_vars()
                                                  .union(&right.free_vars())
                                                  .cloned()
                                                  .collect(),
            // If it's a lambda ...
            Lam(ref bound, ref ty, ref inner) => {
                // Get the free variables from the right hand side.
                let mut tmp = inner.free_vars();
                // And remove the bound variable (because it is bound).
                tmp.remove(&bound);
                // The type of the bound variable could also contain free variables.
                set = tmp.union(&ty.free_vars()).cloned().collect();
            }
            // If it's a `Pi`, we do exactly the same as we did in a lambda!
            Pi(ref bound, ref left, ref right) => {
                let mut tmp = right.free_vars();
                tmp.remove(&bound);
                set = tmp.union(&left.free_vars()).cloned().collect();
            }
            // `Sort`s have no free variables.
            Sort(_) => { set = HashSet::new() }
        }
        debug!("{} has free variables {:?}.", self, set);
        set
    }

    // This function substitutes all occurences of the variable `from` into the term `to`.
    pub fn substitute(self, from: &Symbol, to: &Term<System>) -> Term<System> {
        use self::Term::*;
        match self {
            // If the term going to be substituted is a variable, there are 2 possibilities:
            // 1. `v == from`, then we just return `to`.
            // 2. `v != from`, then we return the variable untouched.
            Var(v) => if v == *from { to.clone() } else { Var(v) },
            // If we hit an application, recursively substitute both sides.
            App(left, right) => app!(left.substitute(from, to), right.substitute(from, to)),
            // If we hit a lambda, hmmmmm, it's a hard case.
            Lam(ref bound, ref ty, ref inner) => {
                // If the bound variable coincide with `from`, we can simply leave thing untouched.
                if bound == from {
                    self.clone()
                }
                // If it doesn't ...
                else {
                    // If the bound variable isn't occured in `to`, then we simply go on
                    // recursively.
                    if !to.free_vars().contains(bound) {
                        Lam(bound.clone(), Box::new(ty.clone().substitute(from, to)),
                            Box::new(inner.clone().substitute(from, to)))
                    }
                    // And now the hardest part about substitution.
                    else {
                        // We create a mutable variable which should eventually be unused in both
                        // the right hand side of the lambda and `to`
                        let mut should_be_unused: Symbol = bound.clone();
                        should_be_unused.0.push_str("'");
                        loop {
                            let used: HashSet<&Symbol> = inner.free_vars()
                                                              .union(&to.free_vars())
                                                              .cloned()
                                                              .collect();
                            // If `should_be_unused` actually is used, append the name of the
                            // variable with an apostrophe.
                            // Notice we're in a loop, so apostrophes will be appended indefinitely
                            if used.contains(&should_be_unused) {
                                should_be_unused.0.push_str("'")
                            }
                            // If `should_be_unused` literally aren't used ...
                            else {
                                // We change the symbols of the lambda from the clashed ones to the
                                // unused ones.
                                let renamed =
                                    Lam(should_be_unused.clone(),
                                        Box::new(ty.clone()
                                                   .substitute(bound,
                                                               &Var(should_be_unused.clone()))),
                                        Box::new(inner.clone()
                                                      .substitute(bound, &Var(should_be_unused))));
                                // And then we do the real substitution.
                                return renamed.substitute(from, to)
                            }
                        }
                    }
                }
            }
            // `Pi` types are dealt with very similar to lambdas are.
            // I copy-pasted the code for the sake of not overengineering.
            Pi(ref bound, ref left, ref right) => {
                if bound == from {
                    self.clone()
                } else {
                    if !to.free_vars().contains(bound) {
                        Pi(bound.clone(), Box::new(left.clone().substitute(from, to)),
                           Box::new(right.clone().substitute(from, to)))
                    } else {
                        let mut should_be_unused: Symbol = bound.clone();
                        should_be_unused.0.push_str("'");
                        loop {
                            let used: HashSet<&Symbol> = right.free_vars()
                                                              .union(&to.free_vars())
                                                              .cloned()
                                                              .collect();
                            if used.contains(&should_be_unused) {
                                should_be_unused.0.push_str("'")
                            } else {
                                let renamed =
                                    Pi(should_be_unused.clone(),
                                       Box::new(left.clone()
                                                    .substitute(bound,
                                                                &Var(should_be_unused.clone()))),
                                       Box::new(right.clone()
                                                     .substitute(bound, &Var(should_be_unused))));
                                return renamed.substitute(from, to)
                            }
                        }
                    }
                }
            }
            // If it's a sort, we don't need to do anything.
            this @ Sort(_) => this,
        }
    }

    // The purpose of this function is to get the *Weak Head Normal Form* of a term.
    pub fn whnf(self) -> Term<System> {
        use self::Term::*;
        // Basically, the **spine** of the syntax tree will be evaluated in this function.
        fn spine<S: PureTypeSystem>(leftmost: Term<S>, stack: &[Term<S>]) -> Term<S> {
            match (leftmost, stack) {
                // If we hit an application ...
                (App(left, right), _) => {
                    let mut new_stack: Vec<Term<S>> = stack.into();
                    // Push the right hand side onto the stack ...
                    new_stack.push(*right);
                    // And then recurse.
                    spine(*left, &new_stack)
                }
                // If we hit a lambda and the stack isn't empty ...
                (Lam(ref from, _, ref inner), ref stack) if !stack.is_empty() => {
                    let mut new_stack: Vec<Term<S>> = (*stack).into();
                    // Unwrapping here after popping is safe because `stack` isn't empty.
                    let right = new_stack.pop().unwrap();
                    // We just need to substitite and go forward.
                    spine(inner.clone().substitute(&from, &right), &new_stack)
                }
                // We simply build the term again if we encounter anything else.
                (leftmost, _) =>
                    stack.iter()
                         .fold(leftmost, |l, r| app!(l, r.clone())),
            }
        }
        spine(self, &[])
    }

    // In comparison with `whnf`, we evaluate every reducible expressions in the term.
    // The definition of the function `nf` is very similar to that of `whnf`,
    // but merging them into 1 function also seems like overengineering right now.
    pub fn nf(self) -> Term<System> {
        use self::Term::*;
        fn spine<S: PureTypeSystem>(leftmost: Term<S>, stack: &[Term<S>]) -> Term<S> {
            println!("{} | {:?}", leftmost, stack);
            match (leftmost, stack) {
                // The same as above.
                (App(left, right), _) => {
                    let mut new_stack: Vec<Term<S>> = stack.into();
                    new_stack.push(*right);
                    spine(*left, &new_stack)
                }
                // If the stack is empty, just recurse everywhere.
                (Lam(ref from, ref ty, ref inner), ref stack) if stack.is_empty() => {
                    Lam(from.clone(), Box::new(ty.clone().nf()), Box::new(inner.clone().nf()))
                }
                // If the stack isn't empty, we do the same as above.
                (Lam(ref from, _, ref inner), ref stack) => {
                    let mut new_stack: Vec<Term<S>> = (*stack).into();
                    // Unwrapping here after popping is safe because `stack` isn't empty.
                    let right = new_stack.pop().unwrap();
                    spine(inner.clone().substitute(&from, &right), &new_stack)
                }
                // If we hit a `Pi`, we recurse everywhere and build the term again.
                (Pi(ref bound, ref left, ref inner), ref stack) =>
                    stack.iter()
                         .fold(Pi(bound.clone(), Box::new(left.clone().nf()),
                                                Box::new(inner.clone().nf())),
                               |l, r| app!(l, r.clone().nf())),
                // We simply build the term again if we encounter anything else.
                // Oh, now we also recurse on the right hand side.
                (leftmost, _) =>
                    stack.iter()
                         .fold(leftmost, |l, r| app!(l, r.clone().nf())),
            }
        }
        spine(self, &[])
    }

    // Alpha equality between types.
    pub fn alpha_eq(&self, another: &Term<System>) -> bool {
        use self::Term::*;
        match (self, another) {
            (&Var(ref v1), &Var(ref v2)) => v1 == v2,
            (&App(ref left1, ref right1), &App(ref left2, ref right2)) =>
                left1.alpha_eq(&left2) && right1.alpha_eq(&right2),
            (&Lam(ref bound1, ref ty1, ref inner1), &Lam(ref bound2, ref ty2, ref inner2)) =>
                ty1.alpha_eq(ty2) &&
                inner1.alpha_eq(&inner2.clone().substitute(&bound2, &Var(bound1.clone()))),
            (&Pi(ref bound1, ref left1, ref right1), &Pi(ref bound2, ref left2, ref right2)) =>
                left1.alpha_eq(left2) &&
                right1.alpha_eq(&right2.clone().substitute(&bound2, &Var(bound1.clone()))),
            (&Sort(ref sort1), &Sort(ref sort2)) => sort1 == sort2,
            _ => false
        }
    }

    // Beta equality between types.
    // To know 2 terms are beta equal, all you have to do is to make sure their `nf`s are alpha
    // equal.
    pub fn beta_eq(&self, another: &Term<System>) -> bool {
        self.clone().nf().alpha_eq(&another.clone().nf())
    }

}

#[cfg(test)]
mod tests {

    use super::*;
    use super::StarAndBox::Star;

    // x == x
    #[test]
    fn alpha_eq_var() {
        let input: Term<Coc> = var!("x");
        assert!(input.alpha_eq(&var!("x")))
    }

    // x != y
    #[test]
    #[should_panic]
    fn alpha_neq_var() {
        let input: Term<Coc> = var!("x");
        assert!(input.alpha_eq(&var!("y")))
    }

    // \x: y. x == \a: y. a
    #[test]
    fn alpha_eq_lam() {
        let left: Term<Coc> = lam!("x", var!("y"), var!("x"));
        let right = lam!("a", var!("y"), var!("a"));
        assert!(left.alpha_eq(&right))
    }

    // (\x: y -> y. x)(\x: y. x) == (\a: y -> y. a)(\b: y. b)
    #[test]
    fn alpha_eq_app() {
        let left: Term<Coc> =
            app!(
                lam!(
                    "x", arrow!(var!("y"), var!("y")),
                    var!("x")
                ),
                lam!(
                    "x", var!("y"),
                    var!("x")
                )
            );
        let right =
            app!(
                lam!(
                    "a", arrow!(var!("y"), var!("y")),
                    var!("a")
                ),
                lam!(
                    "b", var!("y"),
                    var!("b")
                )
            );
        assert!(left.alpha_eq(&right))
    }

    // (a: *) -> a == (b: *) -> b
    #[test]
    fn alpha_eq_pi() {
        let left: Term<Coc> =
            pi!(
                "a", sort!(Star),
                var!("a")
            );
        let right =
            pi!(
                "b", sort!(Star),
                var!("b")
            );
        assert!(left.clone().alpha_eq(&right))
    }

    // id = \a: *. \x: a. x
    fn id() -> Term<Coc> {
        lam!(
            "a", sort!(Star),
            lam!(
                "x", var!("a"),
                var!("x")
            )
        )
    }

    // id: (a: *) -> a -> a
    #[test]
    fn id_type_checks() {
        let ty: Term<Coc> =
            pi!(
                "a", sort!(Star),
                arrow!(
                    var!("a"),
                    var!("a")
                )
            );
        assert_eq!(id().type_check().unwrap(), ty);
    }

    // This function turns a unsigned number into a Church numeral.
    fn church_nat(n: u32) -> Term<Coc> {
        let mut onion = var!("x");
        for _ in 0..n {
            onion = app!(var!("f"), onion)
        }
        lam!("t", sort!(Star),
            lam!(
                "f", arrow!(var!("t"), var!("t")),
                lam!(
                    "x", var!("t"),
                    onion
                )
            )
        )
    }

    // The type of church numerals.
    fn nat_type() -> Term<Coc> {
        pi!("t", sort!(Star),
            arrow!(
                arrow!(var!("t"), var!("t")),
                arrow!(var!("t"), var!("t"))
            )
        )
    }
    
    // `nat_type()` actually **is** the type of a church numeral
    #[test]
    fn church_nat_type_checks() {
        let meaning_of_life: Term<Coc> = church_nat(42).type_check().unwrap();
        assert!(meaning_of_life.beta_eq(&nat_type()));
    }

    // Summing up 2 church numerals.
    // plus(l, r) = \t: *. \f: t -> t. \x: t. l t f (r t f x)
    fn plus(l: Term<Coc>, r: Term<Coc>) -> Term<Coc> {
        lam!(
            "t", sort!(Star),
            lam!(
                "f", arrow!(var!("t"), var!("t")),
                lam!(
                    "x", var!("t"),
                    app!(
                        app!(
                            app!(
                                l,
                                var!("t")
                            ),
                            var!("f")
                        ),
                        app!(
                            app!(
                                app!(
                                    r,
                                    var!("t")
                                ),
                                var!("f")
                            ),
                            var!("x")
                        )
                    )
                )
            )
        )
    }

    // Check that plus(2, 3) equals 5.
    #[test]
    fn plus_check() {
        let two: Term<Coc> = church_nat(2);
        let three = church_nat(3);
        assert!(plus(two, three).beta_eq(&church_nat(5)));
    }

}
