/*!
This crate allows one to parse PromQL query into some AST.

See [official documentation](https://prometheus.io/docs/prometheus/latest/querying/basics/) for query syntax description.

## Example

```
# extern crate nom;
# extern crate promql;
# fn main() {

use promql::*;

let opts = ParserOptions::default()
	.allow_periods(false);

let ast = parse(br#"
	sum(1 - something_used{env="production"} / something_total) by (instance)
	and ignoring (instance)
	sum(rate(some_queries{instance=~"localhost\\d+"} [5m])) > 100
"#, opts).unwrap(); // or show user that their query is invalid

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
	panic!("top operator is not an 'and'");
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

/// Options that allow or disallow certain query language features.
#[derive(Clone, Copy)]
pub struct ParserOptions {
	/**
	Allow periods in metric names (e.g. `threads.busy{instance="..."}`).

	This option is usually used in systems that have metrics carried over from other monitoring systems like Graphite.
	*/
	pub allow_periods: bool,
	/// Allow decimal fractions in intervals (e.g. `offset 0.5d`)
	pub fractional_intervals: bool,
	/// Allow compound interval literals (e.g. `offset 1h30m`)
	pub compound_intervals: bool,
}

impl Default for ParserOptions {
	fn default() -> Self {
		ParserOptions {
			allow_periods: false,
			fractional_intervals: false,
			compound_intervals: false,
		}
	}
}

impl ParserOptions {
	pub fn allow_periods(mut self, val: bool) -> Self {
		self.allow_periods = val;
		self
	}
	pub fn fractional_intervals(mut self, val: bool) -> Self {
		self.fractional_intervals = val;
		self
	}
	pub fn compound_intervals(mut self, val: bool) -> Self {
		self.compound_intervals = val;
		self
	}
}

/**
Parse expression string into an AST.

This parser operates on byte sequence instead of `&str` because of the fact that PromQL, like Go, allows raw byte sequences to be included in the string literals (e.g. `{omg='∞'}` is equivalent to both `{omg='\u221e'}` and `{omg='\xe2\x88\x9e'}`).

Set `allow_periods` to `true` to allow vector names with periods (like `foo.bar`).
*/
pub fn parse(e: &[u8], opts: ParserOptions) -> Result<Node, nom::Err<Error<&[u8]>>> {
	match expression(opts)(e) {
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
			super::parse(b"asdf hjkl", Default::default()),
			err(
				&b"hjkl"[..],
				ErrorKind::Complete
			)
		);
	}
}
