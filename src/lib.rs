#[macro_use]
extern crate log;

use std::fmt::{self, Debug, Display};
use std::hash::Hash;
use std::collections::HashSet;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Symbol(pub String);

impl Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

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
            App(ref left, ref right) => {
                match **right {
                    Var(_) | Sort(_) => write!(f, "{} {}", left, right),
                    _ => write!(f, "{} ({})", left, right),
                }
            }
            Lam(ref bind, ref ty, ref inner) => write!(f, "\\{}: {}. {}", bind, ty, inner),
            Pi(ref bind, ref left, ref right) => write!(f, "({}: {}) -> {}", bind, left, right),
            Sort(ref sort) => write!(f, "{}", sort),
        }
    }
}

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
    ($bind: expr, $ty: expr, $inner: expr) => {
        Term::Lam(Symbol($bind.into()), Box::new($ty), Box::new($inner))
    }
}

#[macro_export]
macro_rules! pi {
    ($bind: expr, $left: expr, $right: expr) => {
        Term::Pi(Symbol($bind.into()), Box::new($left), Box::new($right))
    }
}

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
            Star => write!(f, "{}", "*"),
            Box => write!(f, "{}", "[]"),
        }
    }
}

pub trait PureTypeSystem: Clone + Debug {
    type Sort: Clone + Debug + Display + Eq + Hash;
    fn axioms() -> HashMap<Self::Sort, Self::Sort>;
    fn rules() -> HashMap<(Self::Sort, Self::Sort), Self::Sort>;
}

macro_rules! lambda_cube {
    ($name: ident;
     $($rule_s1: expr, $rule_s2: expr => $rule_s3: expr),*) => {

        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        pub struct $name;

        impl PureTypeSystem for $name {
            type Sort = StarAndBox;
            fn axioms() -> HashMap<StarAndBox, StarAndBox> {
                use self::StarAndBox::*;
                let mut map = HashMap::new();
                map.insert(Star, Box);
                map
            }
            fn rules() -> HashMap<(StarAndBox, StarAndBox), StarAndBox> {
                use self::StarAndBox::*;
                let mut map = HashMap::new();
                $(map.insert(($rule_s1, $rule_s2), $rule_s3));
                *;
                map
            }
        }
    
    }
}

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

    pub fn type_check(&self) -> Result<Term<System>, String> {
        debug!("Start type checking.");
        self.type_check_with_context(HashMap::new())
    }
    
    pub fn type_check_with_context(&self, context: HashMap<Symbol, Term<System>>)
        -> Result<Term<System>, String> {
        use self::Term::*;
        match self.clone() {
            Var(v) => {
                match context.get(&v) {
                    Some(ty) => Ok(ty.clone()),
                    None => Err("Cannot find variable ".to_string() + &v.0)
                }
            }
            App(left, right) => {
                let left_ty = try!(left.type_check_with_context(context.clone()));
                match left_ty.whnf() {
                    Pi(bind, ty_in, ty_out) => {
                        let right_ty = try!(right.type_check_with_context(context.clone()));
                        if !right_ty.beta_eq(&*ty_in) {
                            Ok(ty_out.substitute(&bind, &*right))
                        } else {
                            Err(
                                format!(
                                    "Expected something of type {}, found that of type {}",
                                    ty_in, right_ty
                                )
                            )
                        }
                    }
                    left_ty => Err(format!("Expected lambda, found value of type {}", left_ty))
                }
            }
            Lam(bind, ty, inner) => {
                try!(ty.type_check_with_context(context.clone()));
                let mut new_context = context;
                new_context.insert(bind.clone(), *ty.clone());
                let inner_type = try!(inner.type_check_with_context(new_context));
                Ok(Pi(bind, ty, Box::new(inner_type)))
            }
            Pi(bind, left, right) => {
                if let Sort(left_sort) = try!(left.type_check_with_context(context.clone())
                                                  .map(Term::whnf)) {
                    let mut new_context = context;
                    new_context.insert(bind, *left);
                    let right_kind = try!(right.type_check_with_context(new_context)
                                               .map(Term::whnf));
                    if let Sort(right_sort) = right_kind {
                        let rules = System::rules();
                        let new_sort = rules.get(&(left_sort.clone(), right_sort.clone()));
                        match new_sort {
                            Some(sort) => return Ok(Sort(sort.clone())),
                            None =>  {
                                let error_message =
                                    format!("Rule ({}, {}, _) doesn't exist.",
                                            left_sort, right_sort);
                                return Err(error_message)
                            }
                        }
                    }
                    return Err(format!("Type {} isn't inhabited", right))
                }
                return Err(format!("Type {} isn't inhabited", left))
            }
            Sort(sort) => {
                match System::axioms().get(&sort) {
                    Some(new_sort) => Ok(Sort(new_sort.clone())),
                    None => Err(format!("Sort {} doesn't have a super-sort.", sort)),
                }
            }
        }
    }

    pub fn free_vars(&self) -> HashSet<&Symbol> {
        use self::Term::*;
        let mut set;
        match *self {
            Var(ref v) => {
                set = HashSet::new();
                set.insert(v);
            }
            App(ref left, ref right) => set = left.free_vars()
                                                  .union(&right.free_vars())
                                                  .cloned()
                                                  .collect(),
            Lam(ref bind, ref ty, ref inner) => {
                let mut tmp = inner.free_vars();
                tmp.remove(&bind);
                set = tmp.union(&ty.free_vars()).cloned().collect();
            }
            Pi(ref bind, ref left, ref right) => {
                let mut tmp = right.free_vars();
                tmp.remove(&bind);
                set = tmp.union(&left.free_vars()).cloned().collect();
            }
            Sort(_) => { set = HashSet::new() }
        }
        debug!("{} has free variables {:?}", self, set);
        set
    }
    
    pub fn substitute(self, from: &Symbol, to: &Term<System>) -> Term<System> {
        use self::Term::*;
        match self {
            Var(v) => if v == *from { to.clone() } else { Var(v) },
            App(left, right) => app!(left.substitute(from, to), right.substitute(from, to)),
            Lam(ref bind, ref ty, ref inner) => {
                if bind == from {
                    self.clone()
                } else {
                    if !to.free_vars().contains(bind) {
                        Lam(bind.clone(), Box::new(ty.clone().substitute(from, to)),
                            Box::new(inner.clone().substitute(from, to)))
                    } else {
                        let mut should_be_unused: Symbol = bind.clone();
                        should_be_unused.0.push_str("'");
                        loop {
                            let used: HashSet<&Symbol> = inner.free_vars()
                                                              .union(&to.free_vars())
                                                              .cloned()
                                                              .collect();
                            if used.contains(&should_be_unused) {
                                should_be_unused.0.push_str("'")
                            } else {
                                let renamed = 
                                    Lam(should_be_unused.clone(),
                                        Box::new(ty.clone()
                                                   .substitute(bind,
                                                               &Var(should_be_unused.clone()))),
                                        Box::new(inner.clone()
                                                      .substitute(bind, &Var(should_be_unused))));
                                return renamed.substitute(from, to)
                            }
                        }
                    }
                }
            }
            Pi(ref bind, ref left, ref right) => {
                if bind == from {
                    self.clone()
                } else {
                    if !to.free_vars().contains(bind) {
                        Pi(bind.clone(), Box::new(left.clone().substitute(from, to)),
                           Box::new(right.clone().substitute(from, to)))
                    } else {
                        let mut should_be_unused: Symbol = bind.clone();
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
                                                    .substitute(bind,
                                                                &Var(should_be_unused.clone()))),
                                       Box::new(right.clone()
                                                     .substitute(bind, &Var(should_be_unused))));
                                return renamed.substitute(from, to)
                            }
                        }
                    }
                }
            }
            this @ Sort(_) => this,
        }
    }
    
    pub fn whnf(self) -> Term<System> {
        use self::Term::*;
        fn spine<S2: PureTypeSystem>(leftmost: Term<S2>, stack: &[Term<S2>]) -> Term<S2> {
            match (leftmost, stack) {
                (App(left, right), _) => {
                    let mut new_stack: Vec<Term<S2>> = stack.into();
                    new_stack.push(*right);
                    spine(*left, &new_stack)
                }
                (Lam(ref from, _, ref inner), ref stack) if !stack.is_empty() => {
                    let mut new_stack: Vec<Term<S2>> = (*stack).into();
                    // Unwrapping here is safe because stack isn't empty.
                    let right = new_stack.pop().unwrap();
                    inner.clone().substitute(&from, &right)
                }
                (leftmost, _) =>
                    stack.iter()
                         .fold(leftmost, |l, r| app!(l, r.clone())),
            }
        }
        spine(self, &[])
    }
    
    // The function `nf` is very similar to that of `whnf`,
    // but merging them into 1 function seems like overengineering right now.
    pub fn nf(self) -> Term<System> {
        use self::Term::*;
        fn spine<S: PureTypeSystem>(leftmost: Term<S>, stack: &[Term<S>]) -> Term<S> {
            match (leftmost, stack) {
                (App(left, right), _) => {
                    let mut new_stack: Vec<Term<S>> = stack.into();
                    new_stack.push(*right);
                    spine(*left, &new_stack)
                }
                (Lam(ref from, ref ty, ref inner), ref stack) if stack.is_empty() => {
                    Lam(from.clone(), Box::new(ty.clone().nf()), Box::new(inner.clone().nf()))
                }
                (Lam(ref from, _, ref inner), ref stack) => {
                    let mut new_stack: Vec<Term<S>> = (*stack).into();
                    // Unwrapping here is safe because stack isn't empty.
                    let right = new_stack.pop().unwrap();
                    inner.clone().substitute(&from, &right)
                }
                (Pi(ref bind, ref left, ref inner), ref stack) =>
                    stack.iter()
                         .fold(Pi(bind.clone(), Box::new(left.clone().nf()),
                                                Box::new(inner.clone().nf())),
                               |l, r| app!(l, r.clone().nf())),
                (leftmost, _) =>
                    stack.iter()
                         .fold(leftmost, |l, r| app!(l, r.clone().nf())),
            }
        }
        spine(self, &[])
    }
    
    pub fn alpha_eq(&self, another: &Term<System>) -> bool {
        use self::Term::*;
        match (self, another) {
            (&Var(ref v1), &Var(ref v2)) => v1 == v2,
            (&App(ref left1, ref right1), &App(ref left2, ref right2)) =>
                left1.alpha_eq(&left2) && right1.alpha_eq(&right2),
            (&Lam(ref bind1, ref ty1, ref inner1), &Lam(ref bind2, ref ty2, ref inner2)) =>
                ty1.alpha_eq(ty2) &&
                inner1.alpha_eq(&inner2.clone().substitute(&bind2, &Var(bind1.clone()))),
            (&Pi(ref bind1, ref left1, ref right1), &Pi(ref bind2, ref left2, ref right2)) =>
                left1.alpha_eq(left2) &&
                right1.alpha_eq(&right2.clone().substitute(&bind2, &Var(bind1.clone()))),
            (&Sort(ref sort1), &Sort(ref sort2)) => sort1 == sort2,
            _ => false
        }
    }
    
    pub fn beta_eq(&self, another: &Term<System>) -> bool {
        self.clone().nf().alpha_eq(&another.clone().nf())
    }

}

#[cfg(test)]
mod tests {

    use super::*;
    use super::StarAndBox::Star;
    
    #[test]
    fn alpha_eq_var() {
        let input: Term<Coc> = var!("x");
        assert!(input.alpha_eq(&var!("x")))
    }
    
    #[test]
    #[should_panic]
    fn alpha_neq_var() {
        let input: Term<Coc> = var!("x");
        assert!(input.alpha_eq(&var!("y")))
    }
    
    #[test]
    fn alpha_eq_lam() {
        let left: Term<Coc> = lam!("x", var!("y"), var!("x"));
        let right = lam!("a", var!("y"), var!("a"));
        assert!(left.alpha_eq(&right))
    }
    
    #[test]
    fn alpha_eq_app() {
        let left: Term<Coc> =
            app!(
                lam!(
                    "x", var!("y"),
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
                    "a", var!("y"),
                    var!("a")
                ),
                lam!(
                    "b", var!("y"),
                    var!("b")
                )
            );
        assert!(left.alpha_eq(&right))
    }
    
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
    
    fn id() -> Term<Coc> {
        lam!(
            "a", sort!(Star),
            lam!(
                "x", var!("a"),
                var!("x")
            )
        )
    }
    
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
    
}