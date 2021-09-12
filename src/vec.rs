use nom::IResult;
use nom::branch::alt;
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
use nom::combinator::{
	map,
	opt,
};
use nom::multi::{
	many0,
	separated_list0,
};
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
use crate::utils::surrounded_ws;

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

fn label_set<'a>(input: &'a [u8]) -> IResult<&[u8], Vec<LabelMatch>> {
	delimited(
		char('{'),
		surrounded_ws(
			separated_list0(
				surrounded_ws(char(',')),
				|input: &'a [u8]| {
					let (input, (name, op, value))  = tuple_ws!((
						label_name,
						label_op,
						string,
					))(input)?;
					Ok((input, LabelMatch { name, op, value }))
				}
			),
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
	allow_periods: bool,
) -> impl Fn(&[u8]) -> IResult<&[u8], Vec<LabelMatch>> {
	move |input| {
		let orig = input;
		let (input, (name, labels))  = tuple_ws!((
			opt(metric_name(allow_periods)),
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
			Err(nom::Err::Error(nom::error::Error::new(
				orig,
				// XXX FIXME
				// "vector selector must contain label matchers or metric name",
				nom::error::ErrorKind::MapRes,
			)))
		} else {
			Ok((input, ret))
		}
	}
}

fn range_literal(input: &[u8]) -> IResult<&[u8], usize> {
	map(
		tuple((
			map(
				digit1,
				// from_utf8_unchecked() on [0-9]+ is actually totally safe
				// FIXME unwrap? FIXME copy-pasted from expr.rs
				|n: &[u8]| unsafe { String::from_utf8_unchecked(n.to_vec()) }.parse::<usize>().unwrap()
			),
			alt((
				map(char('s'), |_| 1),
				map(char('m'), |_| 60),
				map(char('h'), |_| 60 * 60),
				map(char('d'), |_| 60 * 60 * 24),
				map(char('w'), |_| 60 * 60 * 24 * 7),
				map(char('y'), |_| 60 * 60 * 24 * 365), // XXX leap years?
			)),
		)),
		|(num, suffix)| (num * suffix)
	)(input)
}

pub(crate) fn vector(
	allow_periods: bool,
) -> impl Fn(&[u8]) -> IResult<&[u8], Vector> {
	move |input: &[u8]| {
		// labels and offset parsers already handle whitespace, no need to use ws!() here
		let (input, (labels, range, offset, _)) = tuple((
			instant_vec(allow_periods),
			opt(delimited(char('['), range_literal, char(']'))),
			opt(preceded(
				surrounded_ws(tag("offset")),
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
}

// > The metric name … must match the regex [a-zA-Z_:][a-zA-Z0-9_:]*.
// > Label names … must match the regex [a-zA-Z_][a-zA-Z0-9_]*. Label names beginning with __ are reserved for internal use.

fn metric_name(
	allow_periods: bool,
) -> impl Fn(&[u8]) -> IResult<&[u8], String> {
	move |input| flat_map!(
		input,
		recognize!(tuple((
			alt((alpha1, is_a("_:"))),
			many0(alt((
				alphanumeric1, is_a(if allow_periods { "_:." } else { "_:" }),
			))),
		))),
		parse_to!(String)
	)
}

// XXX nom does not allow pub(crate) here
named_attr!(#[doc(hidden)], pub label_name <&[u8], String>, flat_map!(
	recognize!(tuple!(
		call!(alt((alpha1, is_a("_")))),
		call!(many0(alt((alphanumeric1, is_a("_")))))
	)),
	parse_to!(String)
));

fn label_op(input: &[u8]) -> IResult<&[u8], LabelMatchOp> {
	alt((
		map(tag("=~"), |_| LabelMatchOp::REq),
		map(tag("!~"), |_| LabelMatchOp::RNe),
		map(tag("="),  |_| LabelMatchOp::Eq), // should come after =~
		map(tag("!="), |_| LabelMatchOp::Ne),
	))(input)
}

#[allow(unused_imports)]
#[cfg(test)]
mod tests {
	use super::*;
	use crate::utils::tests::*;
	use nom::error::ErrorKind;

	fn cbs(s: &str) -> &[u8] {
		s.as_bytes()
	}

	#[test]
	fn instant_vectors_period() {
		instant_vectors(true);

		// matches foo.bar{} entirely
		assert_eq!(
			vector(true)(cbs("foo.bar{}")),
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
			vector(false)(cbs("foo.bar{}")),
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
			vector(allow_periods)(cbs("foo")),
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
			vector(allow_periods)(cbs("foo { }")),
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
			vector(allow_periods)(
				cbs("foo { bar = 'baz', quux !~ 'xyzzy', lorem = `ipsum \\n dolor \"sit amet\"` }"),
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
			vector(allow_periods)(
				// testing whitespace
				cbs("foo{a='b',c ='d' , e = 'f' }"),
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
			vector(allow_periods)(cbs("{lorem=~\"ipsum\"}")),
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
			vector(allow_periods)(cbs("{}")),
			err(cbs("{}"), ErrorKind::MapRes)
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
			vector(allow_periods)(cbs(&format!("{} [1m]", instant))),
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
			vector(allow_periods)(cbs(&format!("{} offset 5m", instant))),
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
			vector(allow_periods)(cbs(&format!("{} [1m] offset 5m", instant))),
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
			vector(allow_periods)(cbs(&format!("{} offset 5m [1m]", instant))),
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
