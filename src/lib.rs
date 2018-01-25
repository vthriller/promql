#[macro_use]
extern crate nom;
#[macro_use]
extern crate quick_error;

pub(crate) mod str;
pub(crate) mod vec;
pub(crate) mod expr;

pub use vec::*;
pub use expr::*;

use nom::types::CompleteByteSlice;

/**
Parse expression string into an AST.

This parser operates on byte sequence instead of `&str` because of the fact that PromQL, like Go, allows raw byte sequences to be included in the string literals (e.g. `{omg='∞'}` is equivalent to both `{omg='\u221e'}` and `{omg='\xe2\x88\x9e'}`).
*/
pub fn parse(e: &[u8]) -> Result<Node, nom::Err<CompleteByteSlice>> {
	match expression(CompleteByteSlice(e)) {
		Ok((CompleteByteSlice(b""), ast)) => Ok(ast),
		Ok(_) => unimplemented!("random gibberish at the end"),
		Err(e) => Err(e),
	}
}
