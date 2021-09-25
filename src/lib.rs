/*!
This crate allows one to parse PromQL query into some AST.

See [official documentation](https://prometheus.io/docs/prometheus/latest/querying/basics/) for query syntax description.

## Example

```
# extern crate nom;
# extern crate promql;
# fn main() {

use promql::*;

let ast = parse(b"
	sum(1 - something_used{env=\"production\"} / something_total) by (instance)
	and ignoring (instance)
	sum(rate(some_queries{instance=~\"localhost\\\\d+\"} [5m])) > 100
", false).unwrap(); // or show user that their query is invalid

// now we can look for all sorts of things

// AST can represent an operator
if let Node::Operator { x, op: Op::And(op_mod), y } = ast {
	// operators can have modifiers
	assert_eq!(op_mod, Some(OpMod {
		action: OpModAction::Ignore,
		labels: vec!["instance".to_string()],
		group: None,
	}));

	// aggregation functions like sum are represented as functions with optional modifiers (`by (label1, …)`/`without (…)`)
	if let Node::Function { ref name, ref aggregation, ref args } = *x {
		assert_eq!(*name, "sum".to_string());
		assert_eq!(*aggregation, Some(AggregationMod {
			action: AggregationAction::By,
			labels: vec!["instance".to_string()],
		}));

		// …
	}
} else {
	panic!("top operator is not an \"and\"");
}

# }
```
*/

#![cfg_attr(feature = "cargo-clippy", allow(clippy::tabs_in_doc_comments))]

#[macro_use]
extern crate nom;
#[macro_use]
extern crate quick_error;

pub(crate) mod expr;
pub(crate) mod str;
pub(crate) mod vec;
pub(crate) mod utils;

pub use expr::*;
pub use vec::*;

use nom::Err;
use nom::error::{Error, ErrorKind};

/**
Parse expression string into an AST.

This parser operates on byte sequence instead of `&str` because of the fact that PromQL, like Go, allows raw byte sequences to be included in the string literals (e.g. `{omg='∞'}` is equivalent to both `{omg='\u221e'}` and `{omg='\xe2\x88\x9e'}`).

Set `allow_periods` to `true` to allow vector names with periods (like `foo.bar`).
*/
pub fn parse(e: &[u8], allow_periods: bool) -> Result<Node, nom::Err<Error<&[u8]>>> {
	match expression(allow_periods)(e) {
		Ok((b"", ast)) => Ok(ast),
		Ok((tail, _)) => Err(Err::Error(error_position!(
			tail,
			ErrorKind::Complete
		))),
		Err(e) => Err(e),
	}
}

#[cfg(test)]
mod tests {
	use nom::error::ErrorKind;
	use crate::utils::tests::*;

	#[test]
	fn completeness() {
		assert_eq!(
			super::parse(b"asdf hjkl", false),
			err(
				&b"hjkl"[..],
				ErrorKind::Complete
			)
		);
	}

	// run this test with `cargo test stack_overflow -- --nocapture`
	#[test]
	fn stack_overflow() {
		let mut op = String::new();
		for _ in 1..128 {
			op.push('+');
			dbg!(op.len());

			use std::io::Write;
			std::io::stdout().flush().unwrap();

			let _ = super::parse(format!("a {} b", op).as_bytes(), Default::default());
		}
	}
}
