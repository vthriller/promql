#[macro_use]
extern crate nom;
#[macro_use]
extern crate quick_error;

pub(crate) mod str;
pub mod vec;
pub mod expr;

use nom::IResult;
use nom::types::CompleteByteSlice;

/**
Parse expression string into an AST.

This parser operates on byte sequence instead of `&str` because of the fact that PromQL, like Go, allows raw byte sequences to be included in the string literals (e.g. `{omg='∞'}` is equivalent to both `{omg='\u221e'}` and `{omg='\xe2\x88\x9e'}`).
*/
pub fn parse(e: &[u8]) -> IResult<CompleteByteSlice, expr::Node> {
	expr::expression(CompleteByteSlice(e))
}
