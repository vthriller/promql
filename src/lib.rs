/*!
This crate allows one to parse PromQL query into some AST.

See [official documentation](https://prometheus.io/docs/prometheus/latest/querying/basics/) for query syntax description.

## Example

```
# extern crate nom;
# extern crate promql;
# fn main() {

use promql::*;

let opts = ParserOptions::new()
	.allow_periods(false)
	.build();

// query can also be `&str`
let query: &[u8] = br#"
	sum(1 - something_used{env="production"} / something_total) by (instance)
	and ignoring (instance)
	sum(rate(some_queries{instance=~"localhost\\d+"} [5m])) > 100
"#;
let ast = parse(query, opts).unwrap(); // or show user that their query is invalid

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

## Types

This parser emits `Vec<u8>` for most string literals because PromQL, like Go, allows raw byte sequences to be included in the string literals (e.g. `{omg='∞'}` is equivalent to both `{omg='\u221e'}` and `{omg='\xe2\x88\x9e'}`).
*/

#![cfg_attr(feature = "cargo-clippy", allow(clippy::tabs_in_doc_comments))]

#[macro_use]
extern crate nom;
#[macro_use]
extern crate quick_error;

/* Nota bene

Some functions parse input directly instead of returning Fn()-parsers.
This sucks ergonomically (need to write `foo(|i| atom(i, opts))` instead of `foo(atom(opts))`),
but closure-returning parsers suck more:

- they allocate a lot of copies of the same closure on the stack
  (since some of them are parts of a larger recursive expression),
  and because some of them use a lot of nom-produced closures
  (and, thus, use quite a lot of memory even if instantiated once),
  they tend to overflow the stack pretty quickly;

- some parser generators also need to create temporary closures
  just to avoid recursive `impl Fn()` return type (see `rustc --explain E0720`),
  making situation worse;

- we cannot reuse single closure because nom parsers don't accept refs to Fn().
*/

pub(crate) mod expr;
pub(crate) mod str;
pub(crate) mod vec;
pub(crate) mod utils;

pub use expr::*;
pub use vec::*;

use nom::Err;
use nom::error::{VerboseError, ErrorKind};

extern crate builder_pattern;
use builder_pattern::Builder;

/// Options that allow or disallow certain query language features.
#[derive(Clone, Copy, Builder)]
pub struct ParserOptions {
	/**
	Allow periods in metric names (e.g. `threads.busy{instance="..."}`).

	This option is usually used in systems that have metrics carried over from other monitoring systems like Graphite.
	*/
	#[default(false)]
	allow_periods: bool,

	/// Allow decimal fractions in intervals (e.g. `offset 0.5d`)
	#[default(false)]
	fractional_intervals: bool,

	/// Allow compound interval literals (e.g. `offset 1h30m`)
	#[default(false)]
	compound_intervals: bool,

	/// Allow negative offsets
	#[default(false)]
	negative_offsets: bool,

	/// Allow `ms` as an interval suffix
	#[default(false)]
	ms_duration: bool,

	/// Allow `#`-prefixed comments
	#[default(true)]
	comments: bool,

	/// How many `Node`-producing expressions and unary operators can be nested into each other
	// affects expr::{expression, atom}
	#[default(64)]
	recursion_limit: usize,
}

impl Default for ParserOptions {
	fn default() -> Self {
		ParserOptions::new().build()
	}
}

/// Parse expression string into an AST.
pub fn parse<I, C>(e: I, opts: ParserOptions) -> Result<Node, nom::Err<VerboseError<I>>>
where
	I: Clone + Copy
		+ nom::AsBytes
		+ nom::Compare<&'static str>
		+ for<'a> nom::Compare<&'a [u8]>
		+ nom::InputIter<Item = C>
		+ nom::InputLength
		+ nom::InputTake
		+ nom::InputTakeAtPosition<Item = C>
		+ nom::Offset
		+ nom::Slice<std::ops::Range<usize>>
		+ nom::Slice<std::ops::RangeFrom<usize>>
		+ nom::Slice<std::ops::RangeTo<usize>>
		+ nom::ParseTo<f32>
		,
	C: nom::AsChar + Clone + Copy,
	&'static str: nom::FindToken<C>,
	<I as nom::InputIter>::IterElem: Clone,
{
	match nom::combinator::all_consuming(|i| expression(0, i, opts))(e) {
		Ok((_, ast)) => Ok(ast),
		Err(e) => Err(e),
	}
}

#[cfg(test)]
mod tests {
	use nom::error::{
		ErrorKind,
		VerboseErrorKind,
	};
	use crate::utils::tests::*;

	#[test]
	fn completeness() {
		assert_eq!(
			super::parse(&b"asdf hjkl"[..], Default::default()),
			err(vec![
				(&b"hjkl"[..], VerboseErrorKind::Nom(ErrorKind::Eof)),
			])
		);
	}
}
