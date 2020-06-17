use nom::{
	alpha,
	alphanumeric,
	digit,
	IResult,
};
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
	parse("foo{bar='baz'}".as_bytes(), false),
	Ok(Node::Vector(Vector {
		labels: vec![
			// this is the filter for the metric name 'foo'
			LabelMatch { name: "__name__".to_string(), op: Eq, value: "foo".to_string(), },
			// here go all the other filters
			LabelMatch { name: "bar".to_string(),      op: Eq, value: "baz".to_string(), },
		],
		range: None, resolution: None, offset: None,
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
        /// Resolution for subqueries, defaults to the global evaluation_interval (1m). Same
        /// time-semantics as range or offset.
        pub resolution: Option<usize>,
	/// Offset in seconds, e.g. `Some(3600)` for `offset 1h`
	pub offset: Option<usize>,
}

fn instant_vec(input: CompleteByteSlice, allow_periods: bool) -> IResult<CompleteByteSlice, Vec<LabelMatch>> {
	map_res!(
		input,
		ws!(do_parse!(
			name: opt!(call!(metric_name, allow_periods)) >>
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
		)),
		|x| x
	)
}

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

type ResolvedRange = (usize, Option<usize>);

fn delimited_range(input: CompleteByteSlice) -> IResult<CompleteByteSlice, Option<ResolvedRange>> {
    ws!(input,
        opt!(
            delimited!(
                char!('['),
                do_parse!(
                    range: range_literal >>
                    opt!(tag!(":")) >>
                    resolution: opt!(range_literal) >>
                    (range, resolution)
                ),
                char!(']')
            )
        )
    )
}

pub(crate) fn vector(input: CompleteByteSlice, allow_periods: bool) -> IResult<CompleteByteSlice, Vector> {
	ws!(
		input,
		do_parse!(
			labels: call!(instant_vec, allow_periods) >>
			range: call!(delimited_range) >>
                        offset: opt!(
				ws!(preceded!(tag!("offset"), range_literal))
			) >>
			(
                            match range {
                                Some(t) => {
                                    Vector{ labels, range: Some(t.0), resolution: t.1, offset }
                                }
                                None => {
                                    Vector{ labels, range: None, resolution: None, offset }
                                }
                            }
			)
		)
	)
}

// > The metric name … must match the regex [a-zA-Z_:][a-zA-Z0-9_:]*.
// > Label names … must match the regex [a-zA-Z_][a-zA-Z0-9_]*. Label names beginning with __ are reserved for internal use.

fn metric_name(input: CompleteByteSlice, allow_periods: bool) -> IResult<CompleteByteSlice, String> {
	flat_map!(
		input,
		recognize!(tuple!(
			alt!(call!(alpha) | is_a!("_:")),
			many0!(alt!(call!(alphanumeric) | is_a!(if allow_periods { "_:." } else { "_:" })))
		)),
		parse_to!(String)
	)
}

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
	fn instant_vectors_period() {
		instant_vectors(true);

		// matches foo.bar{} entirely
		assert_eq!(vector(cbs("foo.bar{}"), true), Ok((cbs(""), Vector{
			labels: vec![
				LabelMatch{
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: "foo.bar".to_string(),
				},
			],
			range: None,
			resolution: None,
			offset: None
		})));
	}

	#[test]
	fn instant_vectors_no_period() {
		instant_vectors(false);

		// matches foo, leaves .bar{}
		assert_eq!(vector(cbs("foo.bar{}"), false), Ok((cbs(".bar{}"), Vector{
			labels: vec![
				LabelMatch{
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: "foo".to_string(),
				},
			],
			range: None,
			resolution: None,
			offset: None
		})));
	}

	fn instant_vectors(allow_periods: bool) {
		assert_eq!(vector(cbs("foo"), allow_periods), Ok((cbs(""), Vector{
			labels: vec![
				LabelMatch{
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: "foo".to_string(),
				},
			],
			range: None,
			resolution: None,
			offset: None
		})));

		assert_eq!(vector(cbs("foo { }"), allow_periods), Ok((cbs(""), Vector{
			labels: vec![
				LabelMatch{
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: "foo".to_string(),
				},
			],
			range: None,
			resolution: None,
			offset: None
		})));

		assert_eq!(vector(cbs("foo { bar = 'baz', quux !~ 'xyzzy', lorem = `ipsum \\n dolor \"sit amet\"` }"), allow_periods), Ok((cbs(""), Vector{
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
			resolution: None,
			offset: None
		})));

		assert_eq!(vector(cbs("{lorem=~\"ipsum\"}"), allow_periods), Ok((cbs(""), Vector{
			labels: vec![
				LabelMatch{
					name: "lorem".to_string(),
					op: LabelMatchOp::REq,
					value: "ipsum".to_string(),
				},
			],
			range: None,
			resolution: None,
			offset: None
		})));

		assert_eq!(vector(cbs("{}"), allow_periods), Err(Err::Error(Context::Code(cbs("{}"), ErrorKind::MapRes))));
	}


	#[test]
	fn modified_vectors_period() {
		modified_vectors(true)
	}

	#[test]
	fn modified_vectors_no_period() {
		modified_vectors(false)
	}

	fn modified_vectors(allow_periods: bool) {
		modified_vectors_for_instant("foo", || vec![
			LabelMatch{
				name: "__name__".to_string(),
				op: LabelMatchOp::Eq,
				value: "foo".to_string(),
			},
		], allow_periods);

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
		], allow_periods);

		modified_vectors_for_instant("{instance!=`localhost`}", || vec![
			LabelMatch{
				name: "instance".to_string(),
				op: LabelMatchOp::Ne,
				value: "localhost".to_string(),
			},
		], allow_periods);
	}

	fn modified_vectors_for_instant(instant: &str, labels: fn() -> Vec<LabelMatch>, allow_periods: bool) {
		assert_eq!(vector(cbs(&format!("{} [1m]", instant)), allow_periods), Ok((cbs(""), Vector{
			labels: labels(),
			range: Some(60),
			resolution: None,
			offset: None,
		})));

		assert_eq!(vector(cbs(&format!("{} [1m:]", instant)), allow_periods), Ok((cbs(""), Vector{
			labels: labels(),
			range: Some(60),
			resolution: None,
			offset: None,
		})));

		assert_eq!(vector(cbs(&format!("{} [1m:10m]", instant)), allow_periods), Ok((cbs(""), Vector{
			labels: labels(),
			range: Some(60),
			resolution: Some(600),
			offset: None,
		})));

		assert_eq!(vector(cbs(&format!("{} offset 5m", instant)), allow_periods), Ok((cbs(""), Vector{
			labels: labels(),
			range: None,
			resolution: None,
			offset: Some(300),
		})));

		assert_eq!(vector(cbs(&format!("{} [1m] offset 5m", instant)), allow_periods), Ok((cbs(""), Vector{
			labels: labels(),
			range: Some(60),
			resolution: None,
			offset: Some(300),
		})));

		assert_eq!(vector(cbs(&format!("{} [1m:] offset 5m", instant)), allow_periods), Ok((cbs(""), Vector{
			labels: labels(),
			range: Some(60),
			resolution: None,
			offset: Some(300),
		})));

		assert_eq!(vector(cbs(&format!("{} [1m:5m] offset 5m", instant)), allow_periods), Ok((cbs(""), Vector{
			labels: labels(),
			range: Some(60),
			resolution: Some(300),
			offset: Some(300),
		})));

		// FIXME should be Error()?
		assert_eq!(vector(cbs(&format!("{} offset 5m [1m]", instant)), allow_periods), Ok((cbs("[1m]"), Vector{
			labels: labels(),
			range: None,
			resolution: None,
			offset: Some(300),
		})));
	}
}
