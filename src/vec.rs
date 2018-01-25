use nom::{alpha, alphanumeric, digit};
use nom::types::CompleteByteSlice;
use str::string;

/// Label filter operators.
#[derive(Debug, PartialEq)]
pub enum LabelMatchOp {
	/** `=`  */ Eq,
	/** `!=` */ Ne,
	/** `=~` */ REq,
	/** `!~` */ RNe,
}

/// Single label filter.
#[derive(Debug, PartialEq)]
pub struct LabelMatch {
	pub name: String,
	pub op: LabelMatchOp,
	pub value: String,
}

named!(label_set <CompleteByteSlice, Vec<LabelMatch>>, delimited!(
	char!('{'),
	ws!(separated_list!(char!(','), do_parse!(
		name: label_name >>
		op: label_op >>
		value: string >>
		(LabelMatch { name, op, value })
	))),
	char!('}')
));

/**
This struct represents both instant and range vectors.

Note that there's no field for metric name: not only it is optional (as in `{instance="localhost", job="foo"}`), metric names can actually be matched using special label called `__name__` (e.g. `{__name__=~"megaexporter_.+"}`), so it only makes sense to parse label names into the corresponding label filter, like so:

```
# extern crate nom;
# extern crate promql;
# fn main() {
use promql::*;
use promql::LabelMatchOp::*; // Eq
use nom::types::CompleteByteSlice;
use nom::IResult;

assert_eq!(
	vector(CompleteByteSlice("foo{bar='baz'}".as_bytes())),
	Ok((CompleteByteSlice(b""), Vector {
		labels: vec![
			// this is the filter for the metric name 'foo'
			LabelMatch { name: "__name__".to_string(), op: Eq, value: "foo".to_string(), },
			// here go all the other filters
			LabelMatch { name: "bar".to_string(),      op: Eq, value: "baz".to_string(), },
		],
		range: None, offset: None,
	}))
);
# }
```
*/
#[derive(Debug, PartialEq)]
pub struct Vector {
	/// Set of label filters
	pub labels: Vec<LabelMatch>,
	/// Range for range vectors, in seconds, e.g. `Some(300)` for `[5m]`
	pub range: Option<usize>,
	/// Offset in seconds, e.g. `Some(3600)` for `offset 1h`
	pub offset: Option<usize>,
}

named!(instant_vec <CompleteByteSlice, Vec<LabelMatch>>, map_res!(ws!(do_parse!(
	name: opt!(metric_name) >>
	labels: opt!(label_set) >>
	({
		let mut ret = match name {
			Some(name) => vec![ LabelMatch{
				name: "__name__".to_string(),
				op: LabelMatchOp::Eq,
				value: name,
			} ],
			None => vec![],
		};
		if let Some(labels) = labels {
			ret.extend(labels)
		}

		if ret.is_empty() {
			Err("vector selector must contain label matchers or metric name")
		} else { Ok(ret) }
	})
)), |x| x));

named!(range_literal <CompleteByteSlice, usize>, do_parse!(
	num: map!(
		digit,
		// from_utf8_unchecked() on [0-9]+ is actually totally safe
		// FIXME unwrap? FIXME copy-pasted from expr.rs
		|n| unsafe { String::from_utf8_unchecked(n.0.to_vec()) }.parse::<usize>().unwrap()
	) >>
	suffix: alt!(
		  char!('s') => { |_| 1 }
		| char!('m') => { |_| 60 }
		| char!('h') => { |_| 60 * 60 }
		| char!('d') => { |_| 60 * 60 * 24 }
		| char!('w') => { |_| 60 * 60 * 24 * 7 }
		| char!('y') => { |_| 60 * 60 * 24 * 365 } // XXX leap years?
	) >>
	(num * suffix)
));

// XXX nom does not allow pub(crate) here
named_attr!(#[doc(hidden)], pub vector <CompleteByteSlice, Vector>, ws!(do_parse!(
	labels: instant_vec >>
	range: opt!(
		delimited!(char!('['), range_literal, char!(']'))
	) >>
	offset: opt!(
		ws!(preceded!(tag!("offset"), range_literal))
	) >>
	(Vector {labels, range, offset})
)));

// > The metric name … must match the regex [a-zA-Z_:][a-zA-Z0-9_:]*.
// > Label names … must match the regex [a-zA-Z_][a-zA-Z0-9_]*. Label names beginning with __ are reserved for internal use.

named!(metric_name <CompleteByteSlice, String>, flat_map!(
	recognize!(tuple!(
		alt!(call!(alpha) | is_a!("_:")),
		many0!(alt!(call!(alphanumeric) | is_a!("_:")))
	)),
	parse_to!(String)
));

// XXX nom does not allow pub(crate) here
named_attr!(#[doc(hidden)], pub label_name <CompleteByteSlice, String>, flat_map!(
	recognize!(tuple!(
		alt!(call!(alpha) | is_a!("_")),
		many0!(alt!(call!(alphanumeric) | is_a!("_")))
	)),
	parse_to!(String)
));

named!(label_op <CompleteByteSlice, LabelMatchOp>, alt!(
	  tag!("=~") => { |_| LabelMatchOp::REq }
	| tag!("!~") => { |_| LabelMatchOp::RNe }
	| tag!("=")  => { |_| LabelMatchOp::Eq  } // should come after =~
	| tag!("!=") => { |_| LabelMatchOp::Ne  }
));

#[allow(unused_imports)]
#[cfg(test)]
mod tests {
	use super::*;
	use nom::{Err, ErrorKind, Context};

	fn cbs(s: &str) -> CompleteByteSlice {
		CompleteByteSlice(s.as_bytes())
	}

	#[test]
	fn instant_vectors() {
		assert_eq!(vector(cbs("foo")), Ok((cbs(""), Vector{
			labels: vec![
				LabelMatch{
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: "foo".to_string(),
				},
			],
			range: None,
			offset: None
		})));

		assert_eq!(vector(cbs("foo { }")), Ok((cbs(""), Vector{
			labels: vec![
				LabelMatch{
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: "foo".to_string(),
				},
			],
			range: None,
			offset: None
		})));

		assert_eq!(vector(cbs("foo { bar = 'baz', quux !~ 'xyzzy', lorem = `ipsum \\n dolor \"sit amet\"` }")), Ok((cbs(""), Vector{
			labels: vec![
				LabelMatch{
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: "foo".to_string(),
				},
				LabelMatch{
					name: "bar".to_string(),
					op: LabelMatchOp::Eq,
					value: "baz".to_string(),
				},
				LabelMatch{
					name: "quux".to_string(),
					op: LabelMatchOp::RNe,
					value: "xyzzy".to_string(),
				},
				LabelMatch{
					name: "lorem".to_string(),
					op: LabelMatchOp::Eq,
					value: "ipsum \\n dolor \"sit amet\"".to_string(),
				},
			],
			range: None,
			offset: None
		})));

		assert_eq!(vector(cbs("{lorem=~\"ipsum\"}")), Ok((cbs(""), Vector{
			labels: vec![
				LabelMatch{
					name: "lorem".to_string(),
					op: LabelMatchOp::REq,
					value: "ipsum".to_string(),
				},
			],
			range: None,
			offset: None
		})));

		assert_eq!(vector(cbs("{}")), Err(Err::Error(Context::Code(cbs("{}"), ErrorKind::MapRes))));
	}

	#[test]
	fn modified_vectors() {
		modified_vectors_for_instant("foo", || vec![
			LabelMatch{
				name: "__name__".to_string(),
				op: LabelMatchOp::Eq,
				value: "foo".to_string(),
			},
		]);

		modified_vectors_for_instant("foo {bar!~\"baz\"}", || vec![
			LabelMatch{
				name: "__name__".to_string(),
				op: LabelMatchOp::Eq,
				value: "foo".to_string(),
			},
			LabelMatch{
				name: "bar".to_string(),
				op: LabelMatchOp::RNe,
				value: "baz".to_string(),
			},
		]);

		modified_vectors_for_instant("{instance!=`localhost`}", || vec![
			LabelMatch{
				name: "instance".to_string(),
				op: LabelMatchOp::Ne,
				value: "localhost".to_string(),
			},
		]);
	}

	fn modified_vectors_for_instant(instant: &str, labels: fn() -> Vec<LabelMatch>) {
		assert_eq!(vector(cbs(&format!("{} [1m]", instant))), Ok((cbs(""), Vector{
			labels: labels(),
			range: Some(60),
			offset: None,
		})));

		assert_eq!(vector(cbs(&format!("{} offset 5m", instant))), Ok((cbs(""), Vector{
			labels: labels(),
			range: None,
			offset: Some(300),
		})));

		assert_eq!(vector(cbs(&format!("{} [1m] offset 5m", instant))), Ok((cbs(""), Vector{
			labels: labels(),
			range: Some(60),
			offset: Some(300),
		})));

		// FIXME should be Error()?
		assert_eq!(vector(cbs(&format!("{} offset 5m [1m]", instant))), Ok((cbs("[1m]"), Vector{
			labels: labels(),
			range: None,
			offset: Some(300),
		})));
	}
}
