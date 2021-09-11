use nom::IResult;
use nom::bytes::complete::{
	is_a,
	tag,
};
use nom::character::complete::{
	alpha1,
	alphanumeric1,
	digit1,
	char,
	multispace0,
};
use nom::combinator::opt;
use nom::multi::separated_list;
use nom::sequence::{
	delimited,
	preceded,
	tuple,
};
use str::string;
use crate::{
	tuple_ws,
	tuple_separated,
};

/// Label filter operators.
#[derive(Debug, PartialEq)]
pub enum LabelMatchOp {
	/** `=`  */
	Eq,
	/** `!=` */
	Ne,
	/** `=~` */
	REq,
	/** `!~` */
	RNe,
}

/// Single label filter.
#[derive(Debug, PartialEq)]
pub struct LabelMatch {
	pub name: String,
	pub op: LabelMatchOp,
	pub value: String,
}

fn label_set(input: &[u8]) -> IResult<&[u8], Vec<LabelMatch>> {
	delimited(
		char('{'),
		delimited(
			multispace0,
			separated_list(
				delimited(multispace0, char(','), multispace0),
				|input: &[u8]| {
					let (input, (name, op, value))  = tuple_ws!((
						label_name,
						label_op,
						string,
					))(input)?;
					Ok((input, LabelMatch { name, op, value }))
				}
			),
			multispace0,
		),
		char('}')
	)(input)
}

/**
This struct represents both instant and range vectors.

Note that there's no field for metric name: not only it is optional (as in `{instance="localhost", job="foo"}`), metric names can actually be matched using special label called `__name__` (e.g. `{__name__=~"megaexporter_.+"}`), so it only makes sense to parse label names into the corresponding label filter, like so:

```
# extern crate nom;
# extern crate promql;
# fn main() {
use promql::*;
use promql::LabelMatchOp::*; // Eq
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

fn instant_vec(
	input: &[u8],
	allow_periods: bool,
) -> IResult<&[u8], Vec<LabelMatch>> {
	let orig = input;
	let (input, (name, labels))  = tuple_ws!((
		opt(|input| metric_name(input, allow_periods)),
		opt(label_set),
	))(input)?;

	let mut ret = match name {
		Some(name) => vec![LabelMatch {
			name: "__name__".to_string(),
			op: LabelMatchOp::Eq,
			value: name,
		}],
		None => vec![],
	};
	if let Some(labels) = labels {
		ret.extend(labels)
	}

	if ret.is_empty() {
		Err(nom::Err::Error((
			orig,
			// XXX FIXME
			// "vector selector must contain label matchers or metric name",
			nom::error::ErrorKind::MapRes,
		)))
	} else {
		Ok((input, ret))
	}
}

fn range_literal(input: &[u8]) -> IResult<&[u8], usize> {
	do_parse!(input,
		num: map!(
			digit1,
			// from_utf8_unchecked() on [0-9]+ is actually totally safe
			// FIXME unwrap? FIXME copy-pasted from expr.rs
			|n| unsafe { String::from_utf8_unchecked(n.to_vec()) }.parse::<usize>().unwrap()
		) >>
		suffix: alt!(
			  call!(char('s')) => { |_| 1 }
			| call!(char('m')) => { |_| 60 }
			| call!(char('h')) => { |_| 60 * 60 }
			| call!(char('d')) => { |_| 60 * 60 * 24 }
			| call!(char('w')) => { |_| 60 * 60 * 24 * 7 }
			| call!(char('y')) => { |_| 60 * 60 * 24 * 365 } // XXX leap years?
		) >>
		(num * suffix)
	)
}

pub(crate) fn vector<'a>(
	input: &'a [u8],
	allow_periods: bool,
) -> IResult<&[u8], Vector> {
	// labels and offset parsers already handle whitespace, no need to use ws!() here
	let (input, (labels, range, offset, _)) = tuple((
		|input: &'a [u8]| instant_vec(input, allow_periods),
		opt(delimited(char('['), range_literal, char(']'))),
		opt(preceded(
			delimited(multispace0, tag("offset"), multispace0),
			range_literal
		)),
		multispace0,
	))(input)?;
	Ok((input, Vector {
		labels,
		range,
		offset
	}))
}

// > The metric name … must match the regex [a-zA-Z_:][a-zA-Z0-9_:]*.
// > Label names … must match the regex [a-zA-Z_][a-zA-Z0-9_]*. Label names beginning with __ are reserved for internal use.

fn metric_name(
	input: &[u8],
	allow_periods: bool,
) -> IResult<&[u8], String> {
	flat_map!(
		input,
		recognize!(tuple!(
			alt!(call!(alpha1) | call!(is_a("_:"))),
			many0!(alt!(
				call!(alphanumeric1) | call!(is_a(if allow_periods { "_:." } else { "_:" }))
			))
		)),
		parse_to!(String)
	)
}

// XXX nom does not allow pub(crate) here
named_attr!(#[doc(hidden)], pub label_name <&[u8], String>, flat_map!(
	recognize!(tuple!(
		alt!(call!(alpha1) | call!(is_a("_"))),
		many0!(alt!(call!(alphanumeric1) | call!(is_a("_"))))
	)),
	parse_to!(String)
));

fn label_op(input: &[u8]) -> IResult<&[u8], LabelMatchOp> {
	alt!(input,
		  call!(tag("=~")) => { |_| LabelMatchOp::REq }
		| call!(tag("!~")) => { |_| LabelMatchOp::RNe }
		| call!(tag("="))  => { |_| LabelMatchOp::Eq  } // should come after =~
		| call!(tag("!=")) => { |_| LabelMatchOp::Ne  }
	)
}

#[allow(unused_imports)]
#[cfg(test)]
mod tests {
	use super::*;
	use nom::Err;
	use nom::error::ErrorKind;

	fn cbs(s: &str) -> &[u8] {
		s.as_bytes()
	}

	#[test]
	fn instant_vectors_period() {
		instant_vectors(true);

		// matches foo.bar{} entirely
		assert_eq!(
			vector(cbs("foo.bar{}"), true),
			Ok((
				cbs(""),
				Vector {
					labels: vec![LabelMatch {
						name: "__name__".to_string(),
						op: LabelMatchOp::Eq,
						value: "foo.bar".to_string(),
					},],
					range: None,
					offset: None
				}
			))
		);
	}

	#[test]
	fn instant_vectors_no_period() {
		instant_vectors(false);

		// matches foo, leaves .bar{}
		assert_eq!(
			vector(cbs("foo.bar{}"), false),
			Ok((
				cbs(".bar{}"),
				Vector {
					labels: vec![LabelMatch {
						name: "__name__".to_string(),
						op: LabelMatchOp::Eq,
						value: "foo".to_string(),
					},],
					range: None,
					offset: None
				}
			))
		);
	}

	fn instant_vectors(allow_periods: bool) {
		assert_eq!(
			vector(cbs("foo"), allow_periods),
			Ok((
				cbs(""),
				Vector {
					labels: vec![LabelMatch {
						name: "__name__".to_string(),
						op: LabelMatchOp::Eq,
						value: "foo".to_string(),
					},],
					range: None,
					offset: None
				}
			))
		);

		assert_eq!(
			vector(cbs("foo { }"), allow_periods),
			Ok((
				cbs(""),
				Vector {
					labels: vec![LabelMatch {
						name: "__name__".to_string(),
						op: LabelMatchOp::Eq,
						value: "foo".to_string(),
					},],
					range: None,
					offset: None
				}
			))
		);

		assert_eq!(
			vector(
				cbs("foo { bar = 'baz', quux !~ 'xyzzy', lorem = `ipsum \\n dolor \"sit amet\"` }"),
				allow_periods
			),
			Ok((
				cbs(""),
				Vector {
					labels: vec![
						LabelMatch {
							name: "__name__".to_string(),
							op: LabelMatchOp::Eq,
							value: "foo".to_string(),
						},
						LabelMatch {
							name: "bar".to_string(),
							op: LabelMatchOp::Eq,
							value: "baz".to_string(),
						},
						LabelMatch {
							name: "quux".to_string(),
							op: LabelMatchOp::RNe,
							value: "xyzzy".to_string(),
						},
						LabelMatch {
							name: "lorem".to_string(),
							op: LabelMatchOp::Eq,
							value: "ipsum \\n dolor \"sit amet\"".to_string(),
						},
					],
					range: None,
					offset: None
				}
			))
		);

		assert_eq!(
			vector(
				// testing whitespace
				cbs("foo{a='b',c ='d' , e = 'f' }"),
				allow_periods
			),
			Ok((
				cbs(""),
				Vector {
					labels: vec![
						LabelMatch {
							name: "__name__".to_string(),
							op: LabelMatchOp::Eq,
							value: "foo".to_string(),
						},
						LabelMatch {
							name: "a".to_string(),
							op: LabelMatchOp::Eq,
							value: "b".to_string(),
						},
						LabelMatch {
							name: "c".to_string(),
							op: LabelMatchOp::Eq,
							value: "d".to_string(),
						},
						LabelMatch {
							name: "e".to_string(),
							op: LabelMatchOp::Eq,
							value: "f".to_string(),
						},
					],
					range: None,
					offset: None
				}
			))
		);

		assert_eq!(
			vector(cbs("{lorem=~\"ipsum\"}"), allow_periods),
			Ok((
				cbs(""),
				Vector {
					labels: vec![LabelMatch {
						name: "lorem".to_string(),
						op: LabelMatchOp::REq,
						value: "ipsum".to_string(),
					},],
					range: None,
					offset: None
				}
			))
		);

		assert_eq!(
			vector(cbs("{}"), allow_periods),
			Err(Err::Error((cbs("{}"), ErrorKind::MapRes)))
		);
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
		modified_vectors_for_instant(
			"foo",
			|| {
				vec![LabelMatch {
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: "foo".to_string(),
				}]
			},
			allow_periods,
		);

		modified_vectors_for_instant(
			"foo {bar!~\"baz\"}",
			|| {
				vec![
					LabelMatch {
						name: "__name__".to_string(),
						op: LabelMatchOp::Eq,
						value: "foo".to_string(),
					},
					LabelMatch {
						name: "bar".to_string(),
						op: LabelMatchOp::RNe,
						value: "baz".to_string(),
					},
				]
			},
			allow_periods,
		);

		modified_vectors_for_instant(
			"{instance!=`localhost`}",
			|| {
				vec![LabelMatch {
					name: "instance".to_string(),
					op: LabelMatchOp::Ne,
					value: "localhost".to_string(),
				}]
			},
			allow_periods,
		);
	}

	fn modified_vectors_for_instant(
		instant: &str,
		labels: fn() -> Vec<LabelMatch>,
		allow_periods: bool,
	) {
		assert_eq!(
			vector(cbs(&format!("{} [1m]", instant)), allow_periods),
			Ok((
				cbs(""),
				Vector {
					labels: labels(),
					range: Some(60),
					offset: None,
				}
			))
		);

		assert_eq!(
			vector(cbs(&format!("{} offset 5m", instant)), allow_periods),
			Ok((
				cbs(""),
				Vector {
					labels: labels(),
					range: None,
					offset: Some(300),
				}
			))
		);

		assert_eq!(
			vector(cbs(&format!("{} [1m] offset 5m", instant)), allow_periods),
			Ok((
				cbs(""),
				Vector {
					labels: labels(),
					range: Some(60),
					offset: Some(300),
				}
			))
		);

		// FIXME should be Error()?
		assert_eq!(
			vector(cbs(&format!("{} offset 5m [1m]", instant)), allow_periods),
			Ok((
				cbs("[1m]"),
				Vector {
					labels: labels(),
					range: None,
					offset: Some(300),
				}
			))
		);
	}
}
