#[macro_use]
extern crate nom;
#[macro_use]
extern crate quick_error;

pub(crate) mod str;
pub(crate) mod vec;
pub(crate) mod expr;

pub use vec::*;
pub use expr::*;

use nom::{Err, ErrorKind};
use nom::types::CompleteByteSlice;

/**
Parse expression string into an AST.

This parser operates on byte sequence instead of `&str` because of the fact that PromQL, like Go, allows raw byte sequences to be included in the string literals (e.g. `{omg='∞'}` is equivalent to both `{omg='\u221e'}` and `{omg='\xe2\x88\x9e'}`).
*/
pub fn parse(e: &[u8]) -> Result<Node, nom::Err<CompleteByteSlice>> {
	match expression(CompleteByteSlice(e)) {
		Ok((CompleteByteSlice(b""), ast)) => Ok(ast),
		Ok((tail, _)) => Err(Err::Error(error_position!(tail, ErrorKind::Complete::<u32>))),
		Err(e) => Err(e),
	}
}

#[cfg(test)]
mod tests {
	use nom::{Err, ErrorKind, Context};
	use nom::types::CompleteByteSlice;

	#[test]
	fn completeness() {
		assert_eq!(
			super::parse(b"asdf hjkl"),
			Err(Err::Error(Context::Code(CompleteByteSlice(b"hjkl"), ErrorKind::Complete)))
		);
	}
}
