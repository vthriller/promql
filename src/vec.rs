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
	map_res,
	opt,
	recognize,
};
use nom::multi::{
	many0,
	many1,
	separated_list0,
};
use nom::sequence::{
	delimited,
	preceded,
	tuple,
};
use str::string;
use crate::{
	ParserOptions,
	tuple_ws,
	tuple_separated,
};
use crate::utils::{
	surrounded_ws,
	value,
};

/// Label filter operators.
#[derive(Debug, PartialEq, Clone)]
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
				map(
					tuple_ws!((
						label_name,
						label_op,
						string,
					)),
					|(name, op, value)|
						LabelMatch { name, op, value }
				)
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
	parse("foo{bar='baz'}".as_bytes(), Default::default()),
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
	/// Range for range vectors, in seconds, e.g. `Some(300.)` for `[5m]`
	pub range: Option<f32>,
	/// Offset in seconds, e.g. `Some(3600.)` for `offset 1h`
	pub offset: Option<f32>,
}

fn instant_vec<'a>(opts: ParserOptions) -> impl FnMut(&'a [u8]) -> IResult<&[u8], Vec<LabelMatch>> {
	map_res(
		tuple_ws!((
			opt(metric_name(opts)),
			opt(label_set),
		)),
		|(name, labels)| {
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
				Err(
					// FIXME how end-user can actually access this message?
					"vector selector must contain label matchers or metric name",
				)
			} else {
				Ok(ret)
			}
		}
	)
}

fn range_literal_part<'a>(opts: ParserOptions) -> impl FnMut(&'a [u8]) -> IResult<&[u8], f32> {
	map(
		tuple((
			map(
				move |input| if opts.fractional_intervals {
					// not using nom's `float` here as it allows literals like `1e3`, which is not what we want
					// TODO should `.5d`/`5.d` (without leading/trailing digits) be allowed?
					recognize(tuple((
						digit1,
						opt(tuple((
							char('.'),
							digit1,
						))),
					)))(input)
				} else {
					digit1(input)
				},
				// from_utf8_unchecked() on [0-9.]+ is actually totally safe
				// FIXME unwrap? FIXME copy-pasted from expr.rs
				|n: &[u8]| unsafe { String::from_utf8_unchecked(n.to_vec()) }.parse::<f32>().unwrap()
			),
			alt((
				value(char('s'), 1.),
				value(char('m'), 60.),
				value(char('h'), 60. * 60.),
				value(char('d'), 60. * 60. * 24.),
				value(char('w'), 60. * 60. * 24. * 7.),
				value(char('y'), 60. * 60. * 24. * 7. * 365.), // XXX leap years?
			)),
		)),
		|(num, suffix)| (num * suffix)
	)
}

fn range_literal<'a>(opts: ParserOptions) -> impl FnMut(&'a [u8]) -> IResult<&[u8], f32> {
	move |input| if opts.compound_intervals {
		map(
			many1(range_literal_part(opts)),
			|intervals| intervals.into_iter().sum()
		)(input)
	} else {
		range_literal_part(opts)(input)
	}
}

pub(crate) fn vector<'a>(opts: ParserOptions) -> impl FnMut(&'a [u8]) -> IResult<&[u8], Vector> {
	map(
		// labels and offset parsers already handle whitespace, no need to use ws!() here
		tuple((
			instant_vec(opts),
			opt(delimited(char('['), range_literal(opts), char(']'))),
			opt(preceded(
				surrounded_ws(tag("offset")),
				tuple((
					move |input| if opts.negative_offsets {
						opt(char('-'))(input)
					} else {
						// match empty string (let next parser fail),
						// mark offset interval as positive
						Ok((input, None))
					},
					range_literal(opts),
				)),
			)),
			multispace0,
		)),
		|(labels, range, offset, _)|
		Vector {
			labels,
			range,
			offset: offset.map(|(sign, value)| {
				let sign = sign.map(|_| -1.).unwrap_or(1.);
				sign * value
			})
		}
	)
}

// > The metric name … must match the regex [a-zA-Z_:][a-zA-Z0-9_:]*.
// > Label names … must match the regex [a-zA-Z_][a-zA-Z0-9_]*. Label names beginning with __ are reserved for internal use.

fn metric_name<'a>(opts: ParserOptions) -> impl FnMut(&'a [u8]) -> IResult<&[u8], String> {
	map_res(
		recognize(tuple((
			alt((alpha1, is_a("_:"))),
			many0(alt((
				alphanumeric1, is_a(if opts.allow_periods { "_:." } else { "_:" }),
			))),
		))),
		|s: &'a [u8]| String::from_utf8(s.to_vec())
	)
}

pub(crate) fn label_name(input: &[u8]) -> IResult<&[u8], String> {
map_res(
	recognize(tuple((
		alt((alpha1, is_a("_"))),
		many0(alt((alphanumeric1, is_a("_")))),
	))),
	|s: &[u8]| String::from_utf8(s.to_vec())
)(input)
}

fn label_op(input: &[u8]) -> IResult<&[u8], LabelMatchOp> {
	alt((
		value(tag("=~"), LabelMatchOp::REq),
		value(tag("!~"), LabelMatchOp::RNe),
		value(tag("="),  LabelMatchOp::Eq), // should come after =~
		value(tag("!="), LabelMatchOp::Ne),
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
			vector(ParserOptions::new()
				.allow_periods(true)
				.build(),
			)(cbs("foo.bar{}")),
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
			vector(ParserOptions::new()
				.allow_periods(false)
				.build()
			)(cbs("foo.bar{}")),
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
		let opts = ParserOptions::new()
			.allow_periods(allow_periods)
			.build();

		assert_eq!(
			vector(opts)(cbs("foo")),
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
			vector(opts)(cbs("foo { }")),
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
			vector(opts)(
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
			vector(opts)(
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
			vector(opts)(cbs("{lorem=~\"ipsum\"}")),
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
			vector(opts)(cbs("{}")),
			err(cbs("{}"), ErrorKind::MapRes)
		);
	}

	#[test]
	fn modified_vectors_permutations() {
		for &allow_periods in &[true, false] {
		for &fractional_intervals in &[true, false] {
		for &compound_intervals in &[true, false] {
		for &negative_offsets in &[true, false] {
			let opts = ParserOptions::new()
				.allow_periods(allow_periods)
				.fractional_intervals(fractional_intervals)
				.compound_intervals(compound_intervals)
				.negative_offsets(negative_offsets)
				.build();

			modified_vectors(opts)
		}
		}
		}
		}
	}

	fn modified_vectors(opts: ParserOptions) {
		modified_vectors_for_instant(
			"foo",
			|| {
				vec![LabelMatch {
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: "foo".to_string(),
				}]
			},
			opts,
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
			opts,
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
			opts,
		);
	}

	fn modified_vectors_for_instant(
		instant: &str,
		labels: fn() -> Vec<LabelMatch>,
		opts: ParserOptions,
	) {
		let v = |tail, range, offset| Ok((
			cbs(tail),
			Vector {
				labels: labels(),
				range, offset,
			},
		));

		// regular

		let q = format!("{} [1m]", instant);
		assert_eq!(
			vector(opts)(cbs(&q)),
			v("", Some(60.), None),
		);

		let q = format!("{} offset 5m", instant);
		assert_eq!(
			vector(opts)(cbs(&q)),
			v("", None, Some(300.)),
		);

		let q = format!("{} [1m] offset 5m", instant);
		assert_eq!(
			vector(opts)(cbs(&q)),
			v("", Some(60.), Some(300.)),
		);

		let q = format!("{} offset 5m [1m]", instant);
		// FIXME should be Error()?
		assert_eq!(
			vector(opts)(cbs(&q)),
			v("[1m]", None, Some(300.)),
		);

		// fractional_intervals

		let q = format!("{} [1.5m]", instant);
		assert_eq!(
			vector(opts)(cbs(&q)),
			if opts.fractional_intervals {
				v("", Some(90.), None)
			} else {
				v("[1.5m]", None, None)
			}
		);

		let q = format!("{} offset 0.5d", instant);
		assert_eq!(
			vector(opts)(cbs(&q)),
			if opts.fractional_intervals {
				v("", None, Some(60. * 60. * 12.))
			} else {
				v("offset 0.5d", None, None)
			}
		);

		let q = format!("{} [1.5m] offset 0.5d", instant);
		assert_eq!(
			vector(opts)(cbs(&q)),
			if opts.fractional_intervals {
				v("", Some(90.), Some(60. * 60. * 12.))
			} else {
				v("[1.5m] offset 0.5d", None, None)
			}
		);

		let q = format!("{} offset 0.5d [1.5m]", instant);
		// FIXME should be Error()?
		assert_eq!(
			vector(opts)(cbs(&q)),
			if opts.fractional_intervals {
				v("[1.5m]", None, Some(60. * 60. * 12.))
			} else {
				v("offset 0.5d [1.5m]", None, None)
			}
		);

		// compound_intervals

		let q = format!("{} [1m45s]", instant);
		assert_eq!(
			vector(opts)(cbs(&q)),
			if opts.compound_intervals {
				v("", Some(105.), None)
			} else {
				v("[1m45s]", None, None)
			}
		);

		let q = format!("{} offset 1h30m", instant);
		assert_eq!(
			vector(opts)(cbs(&q)),
			if opts.compound_intervals {
				v("", None, Some(90. * 60.))
			} else {
				// `offset 1h` is partially pared
				v("30m", None, Some(60. * 60.))
			}
		);

		let q = format!("{} [1m45s] offset 1h30m", instant);
		assert_eq!(
			vector(opts)(cbs(&q)),
			if opts.compound_intervals {
				v("", Some(105.), Some(90. * 60.))
			} else {
				v("[1m45s] offset 1h30m", None, None)
			}
		);

		let q = format!("{} offset 1h30m [1m45s]", instant);
		// FIXME should be Error()?
		assert_eq!(
			vector(opts)(cbs(&q)),
			if opts.compound_intervals {
				v("[1m45s]", None, Some(90. * 60.))
			} else {
				// `offset 1h` is partially pared
				v("30m [1m45s]", None, Some(60. * 60.))
			}
		);

		// negative_offsets

		let q = format!("{} offset -5m", instant);
		assert_eq!(
			vector(opts)(cbs(&q)),
			if opts.negative_offsets {
				v("", None, Some(-300.))
			} else {
				v("offset -5m", None, None)
			}
		);
	}
}
