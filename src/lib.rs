use std::collections::{HashMap, HashSet};
use std::fmt::{self, Debug, Display};
use std::hash::Hash;

use log::debug;

/// A newtype wrapper representing a symbol.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Symbol(pub String);

impl Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The type of terms generic over pure type systems.
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
        match self {
            Term::Var(Symbol(s)) => write!(f, "{}", s),
            Term::App(left, right) => write!(f, "({} {})", left, right),
            Term::Lam(bound, ty, inner) => write!(f, "(\\{}: {}. {})", bound, ty, inner),
            Term::Pi(bound, left, right) => write!(f, "({}: {}) -> {}", bound, left, right),
            Term::Sort(sort) => write!(f, "{}", sort),
        }
    }
}

// Macros for generating terms easily.
// (Explicitly writing out `Box`es is utterly cumbersome.)

#[macro_export]
macro_rules! var {
    ($str:expr) => {
        Term::Var(Symbol($str.into()))
    };
}

#[macro_export]
macro_rules! app {
    ($left:expr, $right:expr) => {
        Term::App(Box::new($left), Box::new($right))
    };
}

#[macro_export]
macro_rules! lam {
    ($bound:expr, $ty:expr, $inner:expr) => {
        Term::Lam(Symbol($bound.into()), Box::new($ty), Box::new($inner))
    };
}

#[macro_export]
macro_rules! pi {
    ($bound:expr, $left:expr, $right:expr) => {
        Term::Pi(Symbol($bound.into()), Box::new($left), Box::new($right))
    };
}

/// A degenerating case of the `Pi` constructor.
#[macro_export]
macro_rules! arrow {
    ($left:expr, $right:expr) => {
        pi!("x", $left, $right)
    };
}

#[macro_export]
macro_rules! sort {
    ($sort:expr) => {
        Term::Sort($sort)
    };
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum StarAndBox {
    Star,
    Box,
}

impl Display for StarAndBox {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            StarAndBox::Star => write!(f, "*"),
            StarAndBox::Box => write!(f, "[]"),
        }
    }
}

/// The trait classifying a pure type system.
///
/// It consists of 3 things, respectively:
/// 1. Its sort, represented as an associated type.
/// 2. `axiom`, a function from any sort to its super-sort.
///    Returns `None` if the sort has no super-sort (i.e. it's the largest sort).
/// 3. `rule`, which specifies the type of a function from the type of its argument and its return type.
///    If a function has type T1 -> T2, where T1 : s1 and T2 : s2,
///    then the type of the whole function type is `rule(s1, s2)`.
///    Returns `None` if the function type isn't well-formed.
pub trait PureTypeSystem: Clone + Debug {
    type Sort: Copy + Clone + Debug + Display + Eq + Hash;
    fn axiom(sort: Self::Sort) -> Option<Self::Sort>;
    fn rule(s1: Self::Sort, s2: Self::Sort) -> Option<Self::Sort>;
}

/// A private macro for generating pure type systems in the lambda cube.
macro_rules! lambda_cube {
    ($name:ident;
     $($rule_s1:pat, $rule_s2:pat => $rule_s3:expr),*) => {

        // The name of the pure type system.
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        pub struct $name;

        impl PureTypeSystem for $name {
            // In a system in the lambda cube, the only sorts available are always `Star` and `Box`.
            type Sort = StarAndBox;

            // The type of `Star` is `Box`, and the `Box` is of no type.
            fn axiom(sort: StarAndBox) -> Option<StarAndBox> {
                match sort {
                    StarAndBox::Star => Some(StarAndBox::Box),
                    StarAndBox::Box => None,
                }
            }

            // Everything the user of this macro needs to supply are the `rule`s.
            fn rule(s1: StarAndBox, s2: StarAndBox) -> Option<StarAndBox> {
                #[allow(unreachable_patterns)]
                match (s1, s2) {
                    $(($rule_s1, $rule_s2) => Some($rule_s3),)*
                    _ => None,
                }
            }
        }
    }
}

// Below are the definitions of several systems in the lambda cube.

lambda_cube! {
    Stlc;
    StarAndBox::Star, StarAndBox::Star => StarAndBox::Star
}

lambda_cube! {
    SystemF;
    StarAndBox::Star, StarAndBox::Star => StarAndBox::Star,
    StarAndBox::Box, StarAndBox::Star => StarAndBox::Star
}

lambda_cube! {
    SystemFOmega;
    StarAndBox::Star, StarAndBox::Star => StarAndBox::Star,
    StarAndBox::Box, StarAndBox::Star => StarAndBox::Star,
    StarAndBox::Box, StarAndBox::Box => StarAndBox::Box
}

lambda_cube! {
    Coc;
    StarAndBox::Star, StarAndBox::Star => StarAndBox::Star,
    StarAndBox::Box, StarAndBox::Star => StarAndBox::Star,
    StarAndBox::Box, StarAndBox::Box => StarAndBox::Box,
    StarAndBox::Star, StarAndBox::Box => StarAndBox::Box
}

impl<System: PureTypeSystem> Term<System> {
    /// The starting point of type checking.
    pub fn type_check(&self) -> Result<Term<System>, String> {
        debug!("Start type checking.");
        self.type_check_with_context(HashMap::new())
    }

    /// The real implementation of type checking.
    /// We need to store typing information in a map called `context`.
    pub fn type_check_with_context(
        &self,
        context: HashMap<Symbol, Term<System>>,
    ) -> Result<Term<System>, String> {
        match self {
            // Simply lookup the context if we hit a variable.
            Term::Var(v) => {
                let Some(ty) = context.get(v) else {
                    return Err(format!("Cannot find variable {}.", v.0));
                };
                Ok(ty.clone())
            }
            // If we hit an application ...
            Term::App(left, right) => {
                // First see if the left hand side type checks.
                let left_ty = left.type_check_with_context(context.clone())?;
                // If `left_ty` isn't a function in its `whnf` form, output an error.
                let Term::Pi(bound, ty_in, ty_out) = left_ty.whnf() else {
                    return Err(format!("Expected lambda, found value of type {}.", left_ty));
                };
                // Then type check the right hand side.
                let right_ty = right.type_check_with_context(context)?;
                // If the type of the right hand side matches the type of the argument of
                // the `Pi` type, substitute the return type with the right hand side.
                // The return type can have free occurences of the bound variable because
                // now we are working with dependent types.
                if right_ty.beta_eq(&ty_in) {
                    Ok(ty_out.substitute(&bound, right))
                } else {
                    Err(format!(
                        "Expected something of type {}, found that of type {}.",
                        ty_in, right_ty
                    ))
                }
            }
            // If we hit a lambda ...
            Term::Lam(bound, ty, inner) => {
                // Check if the type of the argument is well-formed.
                ty.type_check_with_context(context.clone())?;
                let mut new_context = context;
                // Insert the bound variable into the new context.
                new_context.insert(bound.clone(), *ty.clone());
                // And type check the right hand side of the lambda with the new context.
                let inner_type = inner.type_check_with_context(new_context)?;
                Ok(Term::Pi(bound.clone(), ty.clone(), Box::new(inner_type)))
            }
            // If we hit a `Pi` ...
            Term::Pi(bound, left, right) => {
                // First, type check the type of the bound variable. It must be a `Sort`.
                let Term::Sort(left_sort) = left
                    .type_check_with_context(context.clone())
                    .map(|t| t.whnf())?
                else {
                    return Err(format!("Type {} isn't inhabited.", left));
                };

                // Create a new context, the same as what we did in the case of `Lam`.
                let mut new_context = context;
                // Insert the bound variable.
                new_context.insert(bound.clone(), *left.clone());

                // type check the right hand side of the `Pi` with the new context.
                let Term::Sort(right_sort) = right
                    .type_check_with_context(new_context)
                    .map(|t| t.whnf())?
                else {
                    return Err(format!("Type {} isn't inhabited.", right));
                };

                let Some(sort) = System::rule(left_sort, right_sort) else {
                    return Err(format!(
                        "Rule ({}, {}, _) doesn't exist.",
                        left_sort, right_sort
                    ));
                };
                Ok(Term::Sort(sort))
            }
            // Finally, type check the sorts. It's an easy case. We just need to call `axiom`.
            Term::Sort(sort) => {
                let Some(new_sort) = System::axiom(*sort) else {
                    return Err(format!("Sort {} doesn't have a super-sort.", sort));
                };
                Ok(Term::Sort(new_sort))
            }
        }
    }

    /// Returns the set of free variables in a term. Used during substitution.
    pub fn free_vars(&self) -> HashSet<&Symbol> {
        match self {
            // If what we get is a variable ...
            Term::Var(v) => {
                let mut set = HashSet::new();
                // Then the only free variable is itself.
                set.insert(v);
                set
            }
            // If it's an application, just merge the free variables in both sides of the term.
            Term::App(left, right) => {
                let set: HashSet<_> = left
                    .free_vars()
                    .union(&right.free_vars())
                    .copied()
                    .collect();
                set
            }
            // If it's a lambda ...
            Term::Lam(bound, ty, inner) => {
                // Get the free variables from the right hand side.
                let mut tmp = inner.free_vars();
                // And remove the bound variable (because it is bound).
                tmp.remove(bound);
                // The type of the bound variable could also contain free variables.
                let set: HashSet<_> = tmp.union(&ty.free_vars()).copied().collect();
                set
            }
            // If it's a `Pi`, we do exactly the same as we did in a lambda!
            Term::Pi(bound, left, right) => {
                let mut tmp = right.free_vars();
                tmp.remove(bound);
                let set: HashSet<_> = tmp.union(&left.free_vars()).copied().collect();
                set
            }
            // `Sort`s have no free variables.
            Term::Sort(_) => HashSet::new(),
        }
    }

    /// Substitutes all occurrences of the variable `from` with the term `to`.
    pub fn substitute(&self, from: &Symbol, to: &Term<System>) -> Term<System> {
        match self {
            // If the term going to be substituted is a variable, there are 2 possibilities:
            // 1. `v == from`, then we just return `to`.
            // 2. `v != from`, then we return the variable untouched.
            Term::Var(v) => {
                if v == from {
                    to.clone()
                } else {
                    Term::Var(v.clone())
                }
            }
            // If we hit an application, recursively substitute both sides.
            Term::App(left, right) => {
                app!(left.substitute(from, to), right.substitute(from, to))
            }
            // If we hit a lambda, hmmmmm, it's a hard case.
            Term::Lam(bound, ty, inner) => {
                // If the bound variable coincide with `from`, we just need to substitite in its
                // type.
                if bound == from {
                    Term::Lam(
                        bound.clone(),
                        Box::new(ty.substitute(from, to)),
                        inner.clone(),
                    )
                }
                // If it doesn't ...
                else {
                    // If the bound variable doesn't occur in `to`, then we simply go on
                    // recursively.
                    if !to.free_vars().contains(bound) {
                        Term::Lam(
                            bound.clone(),
                            Box::new(ty.substitute(from, to)),
                            Box::new(inner.substitute(from, to)),
                        )
                    }
                    // And now the hardest part about substitution.
                    else {
                        // We create a mutable variable which should eventually be unused in both
                        // the right hand side of the lambda and `to`
                        let mut should_be_unused: Symbol = bound.clone();
                        should_be_unused.0.push('\'');
                        let used: HashSet<&Symbol> =
                            inner.free_vars().union(&to.free_vars()).copied().collect();
                        loop {
                            // If `should_be_unused` actually is used, append the name of the
                            // variable with an apostrophe.
                            // Notice we're in a loop, so apostrophes will be appended indefinitely.
                            if used.contains(&should_be_unused) {
                                should_be_unused.0.push('\'')
                            }
                            // If `should_be_unused` literally isn't used ...
                            else {
                                // We change the symbols of the lambda from the clashed ones to the
                                // unused ones.
                                let renamed = Term::Lam(
                                    should_be_unused.clone(),
                                    Box::new(
                                        ty.substitute(bound, &Term::Var(should_be_unused.clone())),
                                    ),
                                    Box::new(inner.substitute(bound, &Term::Var(should_be_unused))),
                                );
                                // And then we do the real substitution.
                                return renamed.substitute(from, to);
                            }
                        }
                    }
                }
            }
            // `Pi` types are dealt with very similar to lambdas are.
            // I copy-pasted the code for the sake of not overengineering.
            Term::Pi(bound, left, right) => {
                if bound == from {
                    Term::Pi(
                        bound.clone(),
                        Box::new(left.substitute(from, to)),
                        right.clone(),
                    )
                } else {
                    if !to.free_vars().contains(bound) {
                        Term::Pi(
                            bound.clone(),
                            Box::new(left.substitute(from, to)),
                            Box::new(right.substitute(from, to)),
                        )
                    } else {
                        let mut should_be_unused: Symbol = bound.clone();
                        should_be_unused.0.push('\'');
                        let used: HashSet<&Symbol> =
                            right.free_vars().union(&to.free_vars()).copied().collect();
                        loop {
                            if used.contains(&should_be_unused) {
                                should_be_unused.0.push('\'')
                            } else {
                                let renamed = Term::Pi(
                                    should_be_unused.clone(),
                                    Box::new(
                                        left.substitute(
                                            bound,
                                            &Term::Var(should_be_unused.clone()),
                                        ),
                                    ),
                                    Box::new(right.substitute(bound, &Term::Var(should_be_unused))),
                                );
                                return renamed.substitute(from, to);
                            }
                        }
                    }
                }
            }
            // If it's a sort, we don't need to do anything.
            Term::Sort(sort) => Term::Sort(*sort),
        }
    }

    /// Returns the *Weak Head Normal Form* of a term.
    pub fn whnf(&self) -> Term<System> {
        // The **spine** of the syntax tree is evaluated here.
        fn spine<S: PureTypeSystem>(leftmost: Term<S>, mut stack: Vec<Term<S>>) -> Term<S> {
            match leftmost {
                // If we hit an application ...
                Term::App(left, right) => {
                    // Push the right hand side onto the stack ...
                    stack.push(*right);
                    // And then recurse.
                    spine(*left, stack)
                }
                // If we hit a lambda and the stack isn't empty ...
                Term::Lam(ref from, _, ref inner) if !stack.is_empty() => {
                    // Safe: stack is non-empty.
                    let right = stack.pop().unwrap();
                    // We just need to substitite and go forward.
                    spine(inner.substitute(from, &right), stack)
                }
                // We simply build the term again if we encounter anything else.
                leftmost => stack.into_iter().rev().fold(leftmost, |l, r| app!(l, r)),
            }
        }
        spine(self.clone(), Vec::new())
    }

    /// In comparison with `whnf`, we evaluate every reducible expressions in the term.
    /// The definition of the function `nf` is very similar to that of `whnf`,
    /// but merging them into 1 function also seems like overengineering right now.
    pub fn nf(&self) -> Term<System> {
        fn spine<S: PureTypeSystem>(leftmost: Term<S>, mut stack: Vec<Term<S>>) -> Term<S> {
            match leftmost {
                // The same as above.
                Term::App(left, right) => {
                    stack.push(*right);
                    spine(*left, stack)
                }
                // If the stack is empty, just recurse everywhere.
                Term::Lam(ref from, ref ty, ref inner) if stack.is_empty() => {
                    Term::Lam(from.clone(), Box::new(ty.nf()), Box::new(inner.nf()))
                }
                // If the stack isn't empty, we do the same as above.
                Term::Lam(ref from, _, ref inner) => {
                    // Safe: stack is non-empty.
                    let right = stack.pop().unwrap();
                    spine(inner.substitute(from, &right), stack)
                }
                // If we hit a `Pi`, we recurse everywhere and build the term again.
                Term::Pi(ref bound, ref left, ref inner) => stack.into_iter().fold(
                    Term::Pi(bound.clone(), Box::new(left.nf()), Box::new(inner.nf())),
                    |l, r| app!(l, r.nf()),
                ),
                // We simply build the term again if we encounter anything else.
                // Oh, now we also recurse on the right hand side.
                leftmost => stack.into_iter().rev().fold(leftmost, |l, r| app!(l, r.nf())),
            }
        }
        spine(self.clone(), Vec::new())
    }

    /// Alpha equality between terms.
    pub fn alpha_eq(&self, another: &Term<System>) -> bool {
        match (self, another) {
            (Term::Var(v1), Term::Var(v2)) => v1 == v2,
            (Term::App(left1, right1), Term::App(left2, right2)) => {
                left1.alpha_eq(left2) && right1.alpha_eq(right2)
            }
            (Term::Lam(bound1, ty1, inner1), Term::Lam(bound2, ty2, inner2)) => {
                ty1.alpha_eq(ty2)
                    && inner1.alpha_eq(&inner2.substitute(bound2, &Term::Var(bound1.clone())))
            }
            (Term::Pi(bound1, left1, right1), Term::Pi(bound2, left2, right2)) => {
                left1.alpha_eq(left2)
                    && right1.alpha_eq(&right2.substitute(bound2, &Term::Var(bound1.clone())))
            }
            (Term::Sort(sort1), Term::Sort(sort2)) => sort1 == sort2,
            _ => false,
        }
    }

    /// Beta equality between terms.
    /// Two terms are beta-equal iff their normal forms are alpha-equal.
    pub fn beta_eq(&self, another: &Term<System>) -> bool {
        self.nf().alpha_eq(&another.nf())
    }
}

#[cfg(test)]
mod tests {

    use super::StarAndBox::Star;
    use super::*;

    // x == x
    #[test]
    fn alpha_eq_var() {
        let input: Term<Coc> = var!("x");
        assert!(input.alpha_eq(&var!("x")));
    }

    // x != y
    #[test]
    #[should_panic]
    fn alpha_neq_var() {
        let input: Term<Coc> = var!("x");
        assert!(input.alpha_eq(&var!("y")));
    }

    // \x: y. x == \a: y. a
    #[test]
    fn alpha_eq_lam() {
        let left: Term<Coc> = lam!("x", var!("y"), var!("x"));
        let right = lam!("a", var!("y"), var!("a"));
        assert!(left.alpha_eq(&right));
    }

    // (\x: y -> y. x)(\x: y. x) == (\a: y -> y. a)(\b: y. b)
    #[test]
    fn alpha_eq_app() {
        let left: Term<Coc> = app!(
            lam!("x", arrow!(var!("y"), var!("y")), var!("x")),
            lam!("x", var!("y"), var!("x"))
        );
        let right = app!(
            lam!("a", arrow!(var!("y"), var!("y")), var!("a")),
            lam!("b", var!("y"), var!("b"))
        );
        assert!(left.alpha_eq(&right));
    }

    // (a: *) -> a == (b: *) -> b
    #[test]
    fn alpha_eq_pi() {
        let left: Term<Coc> = pi!("a", sort!(Star), var!("a"));
        let right = pi!("b", sort!(Star), var!("b"));
        assert!(left.alpha_eq(&right));
    }

    #[test]
    fn substitute_type() {
        let left: Term<Coc> = app!(
            lam!("x", sort!(Star), lam!("x", var!("x"), var!("x"))),
            var!("y")
        );
        let right: Term<Coc> = lam!("x", var!("y"), var!("x"));
        assert!(left.beta_eq(&right));
    }

    // id = \a: *. \x: a. x
    fn id() -> Term<Coc> {
        lam!("a", sort!(Star), lam!("x", var!("a"), var!("x")))
    }

    // id: (a: *) -> a -> a
    #[test]
    fn id_type_checks() {
        let ty: Term<Coc> = pi!("a", sort!(Star), arrow!(var!("a"), var!("a")));
        assert_eq!(id().type_check().unwrap(), ty);
    }

    // Converts an unsigned number into a Church numeral.
    fn church_nat(n: u32) -> Term<Coc> {
        let mut onion = var!("x");
        for _ in 0..n {
            onion = app!(var!("f"), onion);
        }
        lam!(
            "t",
            sort!(Star),
            lam!(
                "f",
                arrow!(var!("t"), var!("t")),
                lam!("x", var!("t"), onion)
            )
        )
    }

    // The type of Church numerals.
    fn nat_type() -> Term<Coc> {
        pi!(
            "t",
            sort!(Star),
            arrow!(arrow!(var!("t"), var!("t")), arrow!(var!("t"), var!("t")))
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
            "t",
            sort!(Star),
            lam!(
                "f",
                arrow!(var!("t"), var!("t")),
                lam!(
                    "x",
                    var!("t"),
                    app!(
                        app!(app!(l, var!("t")), var!("f")),
                        app!(app!(app!(r, var!("t")), var!("f")), var!("x"))
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

    // (x a b) is already in normal form — nf should return it unchanged
    #[test]
    fn open_term_nf() {
        let term: Term<Coc> = app!(app!(var!("x"), var!("a")), var!("b"));
        assert!(term.nf().beta_eq(&term));
    }

    #[test]
    fn open_term_whnf() {
        let term: Term<Coc> = app!(app!(var!("x"), var!("a")), var!("b"));
        assert!(term.whnf().beta_eq(&term));
    }
}
