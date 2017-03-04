use std::usize::MAX;

use nom::IResult;

use system::*;

// I split the superficial syntax tree into another `enum`.
#[derive(Clone, Debug, PartialEq, Hash)]
pub enum Syntax<S: PureTypeSystem> {
    Var(String),
    App(Vec<Syntax<S>>),
    Lam(Vec<Args<S>>, Box<Syntax<S>>),
    Pi(Symbol, Box<Syntax<S>>, Box<Syntax<S>>),
    Sort(S::Sort),
    Parens(Box<Syntax<S>>),
}

use self::Syntax::*;
#[derive(Clone, Debug, PartialEq, Hash)]
pub struct Args<S: PureTypeSystem> {
    pub vars: Vec<Symbol>,
    pub ty: Box<Syntax<S>>,
}

pub trait IterSorts: PureTypeSystem {
    type Iter: Iterator<Item = Self::Sort>;
    fn sorts() -> Self::Iter;
}

macro_rules! lambda_cube_sorts {
    ($name: ident) => {
        impl IterSorts for $name {
            type Iter = StarAndBoxIter;
            fn sorts() -> StarAndBoxIter {
                StarAndBox::iter_variants()
            }
        }
    }
}

lambda_cube_sorts!(Stlc);
lambda_cube_sorts!(SystemF);
lambda_cube_sorts!(SystemFOmega);
lambda_cube_sorts!(Coc);

pub fn parse<S: IterSorts>(input: &[u8]) -> IResult<&[u8], Syntax<S>> {
    let lam =
        closure!(
            do_parse!(
                term: alt!(
                    apply!(parse_var, S::sorts())
                ) >>
                (term)
            )
        );
    lam(input)
}

fn parse_var<'a, S: IterSorts, I: Iterator<Item = S::Sort>>(input: &'a [u8], extra_idents: I)
                -> IResult<&'a [u8], Syntax<S>> {
    let idents = identifiers::<S, _>(" \t\r\n()", extra_idents);
    let lam =
        closure!(&'a [u8],
            do_parse!(
                many0!(one_of!(" \t\r\n")) >>
                var: call!(
                    |rest| parse_var_helper(&idents, rest).map(
                        |vec: Vec<char>| Var(vec.into_iter().collect::<String>())
                    )
                ) >>
                (var)
            )
        );
    lam(input)
}

fn identifiers<S: IterSorts, I: Iterator<Item = S::Sort>>(builtin: &str, extra: I) -> String {
    let mut string = String::from(builtin);
    for variant in extra {
        string.push_str(&variant.to_string())
    }
    string
}

fn parse_var_helper<'a>(idents: &str, input: &'a [u8]) -> IResult<&'a [u8], Vec<char>> {
    let lam = closure!(&'a [u8], many1!(none_of!(idents.as_bytes())));
    lam(input)
}

fn parse_app<'a, S: IterSorts>(input: &'a [u8]) -> IResult<&[u8], Syntax<S>> {
    let lam =
        closure!(&'a [u8],
            map!(
                many_m_n!(2, MAX, parse),
                |vec: Vec<Syntax<S>>| App(vec)
            )
        );
    lam(input)
}
