// This is for debugging.
#[macro_use] extern crate log;

// We use nom as the parsing library.
#[macro_use] extern crate nom;

// I want to iterate through variants of an `enum`.
#[macro_use] extern crate macro_attr;
#[macro_use] extern crate enum_derive;

pub mod system;
pub mod syntax;
