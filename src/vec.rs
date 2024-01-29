use nom::{
	AsBytes,
	Compare,
	InputIter,
	InputLength,
	InputTake,
	InputTakeAtPosition,
	Offset,
	Slice,
	FindToken,
	AsChar,
};
use std::ops::{
	Range,
	RangeFrom,
	RangeTo,
};
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
	cond,
	map,
	map_opt,
	map_res,
	opt,
	recognize,
};
use nom::multi::{
	many0,
	separated_list0,
};
use nom::sequence::{
	delimited,
	tuple,
};
use crate::{
	ParserOptions,
	tuple_separated,
};
use crate::str::string;
use crate::whitespace::ws_or_comment;
use crate::utils::{
	IResult,
	delimited_ws,
	surrounded_ws,
	value,
};

/// Label filter operators.
#[derive(Debug, PartialEq, Clone)]
#[cfg_attr(feature = "serializable", derive(serde_derive::Serialize))]
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
#[cfg_attr(feature = "serializable", derive(serde_derive::Serialize))]
pub struct LabelMatch {
	pub name: String,
	pub op: LabelMatchOp,
	pub value: Vec<u8>,
}

fn label_set<I, C>(input: I, opts: &ParserOptions) -> IResult<I, Vec<LabelMatch>>
where
	I: Clone
		+ AsBytes
		+ Compare<&'static str>
		+ InputIter<Item = C>
		+ InputLength
		+ InputTake
		+ InputTakeAtPosition<Item = C>
		+ Offset
		+ Slice<Range<usize>>
		+ Slice<RangeFrom<usize>>
		+ Slice<RangeTo<usize>>
		,
	C: AsChar + Clone,
	&'static str: FindToken<C>,
{
	delimited(
		char('{'),
		surrounded_ws(
			separated_list0(
				surrounded_ws(char(',')),
				map(
					tuple_separated!(ws_or_comment(opts), (
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
	parse("foo{bar='baz'}".as_bytes(), &Default::default()),
	Ok(Node::Vector(Vector {
		labels: vec![
			// this is the filter for the metric name 'foo'
			LabelMatch { name: "__name__".to_string(), op: Eq, value: b"foo".to_vec(), },
			// here go all the other filters
			LabelMatch { name: "bar".to_string(),      op: Eq, value: b"baz".to_vec(), },
		],
		range: None, offset: None,
	}))
);
# }
```
*/
#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "serializable", derive(serde_derive::Serialize))]
pub struct Vector {
	/// Set of label filters
	pub labels: Vec<LabelMatch>,
	/// Range for range vectors, in seconds, e.g. `Some(300.)` for `[5m]`
	pub range: Option<f32>,
	/// Offset in seconds, e.g. `Some(3600.)` for `offset 1h`
	pub offset: Option<f32>,
}

fn instant_vec<I, C>(input: I, opts: &ParserOptions) -> IResult<I, Vec<LabelMatch>>
where
	I: Clone + Copy
		+ AsBytes
		+ Compare<&'static str>
		+ InputIter<Item = C>
		+ InputLength
		+ InputTake
		+ InputTakeAtPosition<Item = C>
		+ Offset
		+ Slice<Range<usize>>
		+ Slice<RangeFrom<usize>>
		+ Slice<RangeTo<usize>>
		,
	C: AsChar + Clone,
	&'static str: FindToken<C>,
{
	let orig_input = input;
	let (input, (name, labels)) =
		tuple_separated!(ws_or_comment(opts), (
			opt(move |i| metric_name(i, opts)),
			opt(|i| label_set(i, opts)),
		))(input)?;

	let mut ret = match name {
		Some(name) => vec![LabelMatch {
			name: "__name__".to_string(),
			op: LabelMatchOp::Eq,
			value: name.into_bytes(),
		}],
		None => vec![],
	};
	if let Some(labels) = labels {
		ret.extend(labels)
	}

	if ret.is_empty() {
		Err(nom::Err::Error(nom::error::VerboseError {
			errors: vec![
				(orig_input, nom::error::VerboseErrorKind::Context("vector selector must contain label matchers or metric name")),
			],
		}))
	} else {
		Ok((input, ret))
	}
}

// `max_duration` limits set of available suffixes, allowing us to forbid intervals like `30s5m`
// not using vecs/slices to limit set of acceptable suffixes: they're expensive,
// and we cannot build an alt() from them anyway (even recursive one, like alt(alt(), ...))
fn range_literal_part<I, C>(input: I, opts: &ParserOptions, max_duration: Option<f32>) -> IResult<I, (f32, f32)>
where
	I: Clone
		+ AsBytes
		+ Compare<&'static str>
		+ InputIter<Item = C>
		+ InputLength
		+ InputTake
		+ InputTakeAtPosition<Item = C>
		+ Offset
		+ Slice<RangeFrom<usize>>
		+ Slice<RangeTo<usize>>
		,
	C: AsChar,
{
	map_opt(
		tuple((
			map(
				move |input: I| if opts.fractional_intervals {
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
				|n| unsafe { String::from_utf8_unchecked(n.as_bytes().to_vec()) }.parse::<f32>().unwrap()
			),
			alt((
				// 'ms' should come before 'm'
				map_opt(
					cond(opts.ms_duration, tag("ms")),
					|option| option.map(|_| 1e-3),
				),
				value(char('s'), 1.),
				value(char('m'), 60.),
				value(char('h'), 60. * 60.),
				value(char('d'), 60. * 60. * 24.),
				value(char('w'), 60. * 60. * 24. * 7.),
				value(char('y'), 60. * 60. * 24. * 7. * 365.), // XXX leap years?
			)),
		)),
		move |(num, suffix)| match max_duration {
			None => Some((num, suffix)),
			Some(max) => if suffix < max {
				Some((num, suffix))
			} else {
				None
			},
		}
	)(input)
}

fn range_compound_literal<I, C>(input: I, opts: &ParserOptions, max_duration: Option<f32>) -> IResult<I, f32>
where
	I: Clone + Copy
		+ AsBytes
		+ Compare<&'static str>
		+ InputIter<Item = C>
		+ InputLength
		+ InputTake
		+ InputTakeAtPosition<Item = C>
		+ Offset
		+ Slice<RangeFrom<usize>>
		+ Slice<RangeTo<usize>>
		,
	C: AsChar,
{
		let (input, (amount, duration)) = range_literal_part(input, opts, max_duration)?;
		// use matched duration as a new cap so we don't match the same durations or longer
		let (input, rest) = match range_compound_literal(input, opts, Some(duration)) {
			Ok((input, rest)) => (input, rest),
			Err(_) => (input, 0.), // the rest doesn't look like compound literal
		};
		Ok((input, amount * duration + rest))
}

fn range_literal<I, C>(input: I, opts: &ParserOptions) -> IResult<I, f32>
where
	I: Clone + Copy
		+ AsBytes
		+ Compare<&'static str>
		+ InputIter<Item = C>
		+ InputLength
		+ InputTake
		+ InputTakeAtPosition<Item = C>
		+ Offset
		+ Slice<RangeFrom<usize>>
		+ Slice<RangeTo<usize>>
		,
	C: AsChar,
{
	if opts.compound_intervals {
		range_compound_literal(input, opts, None)
	} else {
		map(
			|i| range_literal_part(i, opts, None),
			|(amount, duration)| amount * duration
		)(input)
	}
}

pub(crate) fn vector<I, C>(input: I, opts: &ParserOptions) -> IResult<I, Vector>
where
	I: Clone + Copy
		+ AsBytes
		+ Compare<&'static str>
		+ InputIter<Item = C>
		+ InputLength
		+ InputTake
		+ InputTakeAtPosition<Item = C>
		+ Offset
		+ Slice<Range<usize>>
		+ Slice<RangeFrom<usize>>
		+ Slice<RangeTo<usize>>
		,
	C: AsChar + Clone,
	&'static str: FindToken<C>,
{
	map(
		// labels and offset parsers already handle whitespace, no need to use ws!() here
		tuple_separated!(ws_or_comment(opts), (
			|i| instant_vec(i, opts),
			opt(delimited_ws(char('['), |i| range_literal(i, opts), char(']'))),
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
					|i| range_literal(i, opts),
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
	)(input)
}

// > The metric name … must match the regex [a-zA-Z_:][a-zA-Z0-9_:]*.
// > Label names … must match the regex [a-zA-Z_][a-zA-Z0-9_]*. Label names beginning with __ are reserved for internal use.

fn metric_name<I, C>(input: I, opts: &ParserOptions) -> IResult<I, String>
where
	I: Clone
		+ AsBytes
		+ InputIter<Item = C>
		+ InputLength
		+ InputTake
		+ InputTakeAtPosition<Item = C>
		+ Offset
		+ Slice<RangeTo<usize>>
		,
	C: AsChar,
	&'static str: FindToken<C>
{
	map_res(
		recognize(tuple((
			alt((alpha1, is_a("_:"))),
			many0(alt((
				alphanumeric1, is_a(if opts.allow_dots { "_:." } else { "_:" }),
			))),
		))),
		|s: I| String::from_utf8(s.as_bytes().to_vec())
	)(input)
}

pub(crate) fn label_name<I, C>(input: I) -> IResult<I, String>
where
	I: Clone
		+ AsBytes
		+ InputIter<Item = C>
		+ InputLength
		+ InputTake
		+ InputTakeAtPosition<Item = C>
		+ Offset
		+ Slice<RangeTo<usize>>
		,
	C: AsChar,
	&'static str: FindToken<C>
{
map_res(
	recognize(tuple((
		alt((alpha1, is_a("_"))),
		many0(alt((alphanumeric1, is_a("_")))),
	))),
	|s: I| String::from_utf8(s.as_bytes().to_vec())
)(input)
}

fn label_op<I>(input: I) -> IResult<I, LabelMatchOp>
where
	I: Clone
		+ Compare<&'static str>
		+ InputTake
{
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
	use nom::error::{
		ErrorKind,
		VerboseErrorKind,
	};

	#[test]
	fn instant_vectors_period() {
		instant_vectors(true);

		// matches foo.bar{} entirely
		for q in [
			"foo.bar{}",
			"foo.bar { }",
		] {
			assert_eq!(
				vector(
					q,
					&ParserOptions::new()
						.allow_dots(true)
						.build(),
				),
				Ok((
					"",
					Vector {
						labels: vec![LabelMatch {
							name: "__name__".to_string(),
							op: LabelMatchOp::Eq,
							value: b"foo.bar".to_vec(),
						},],
						range: None,
						offset: None
					}
				))
			);
		}
	}

	#[test]
	fn instant_vectors_no_period() {
		instant_vectors(false);

		// matches foo, leaves .bar{}
		for (q, tail) in [
			("foo.bar{}",   ".bar{}"),
			("foo.bar { }", ".bar { }"),
		] {
			assert_eq!(
				vector(
					q,
					&ParserOptions::new()
						.allow_dots(false)
						.build(),
				),
				Ok((
					tail,
					Vector {
						labels: vec![LabelMatch {
							name: "__name__".to_string(),
							op: LabelMatchOp::Eq,
							value: b"foo".to_vec(),
						},],
						range: None,
						offset: None
					}
				))
			);
		}
	}

	fn instant_vectors(allow_dots: bool) {
		let opts = ParserOptions::new()
			.allow_dots(allow_dots)
			.comments(true)
			.build();

		assert_eq!(
			vector("foo", &opts),
			Ok((
				"",
				Vector {
					labels: vec![LabelMatch {
						name: "__name__".to_string(),
						op: LabelMatchOp::Eq,
						value: b"foo".to_vec(),
					},],
					range: None,
					offset: None
				}
			))
		);

		for q in [
			"foo{}",
			"foo { }",
		] {
			assert_eq!(
				vector(q, &opts),
				Ok((
					"",
					Vector {
						labels: vec![LabelMatch {
							name: "__name__".to_string(),
							op: LabelMatchOp::Eq,
							value: b"foo".to_vec(),
						},],
						range: None,
						offset: None
					}
				))
			);
		}

		for q in [
			"foo{bar='baz',quux!~'xyzzy',lorem=`ipsum \\n dolor \"sit amet\"`}",
			"foo { bar = 'baz' , quux !~ 'xyzzy' , lorem = `ipsum \\n dolor \"sit amet\"` }",
		] {
			assert_eq!(
				vector(
					q,
					&opts,
				),
				Ok((
					"",
					Vector {
						labels: vec![
							LabelMatch {
								name: "__name__".to_string(),
								op: LabelMatchOp::Eq,
								value: b"foo".to_vec(),
							},
							LabelMatch {
								name: "bar".to_string(),
								op: LabelMatchOp::Eq,
								value: b"baz".to_vec(),
							},
							LabelMatch {
								name: "quux".to_string(),
								op: LabelMatchOp::RNe,
								value: b"xyzzy".to_vec(),
							},
							LabelMatch {
								name: "lorem".to_string(),
								op: LabelMatchOp::Eq,
								value: b"ipsum \\n dolor \"sit amet\"".to_vec(),
							},
						],
						range: None,
						offset: None
					}
				))
			);
		}

		for q in [
			"{lorem=~\"ipsum\"}",
			"{ lorem =~ \"ipsum\" }",
		] {
			assert_eq!(
				vector(q, &opts),
				Ok((
					"",
					Vector {
						labels: vec![LabelMatch {
							name: "lorem".to_string(),
							op: LabelMatchOp::REq,
							value: b"ipsum".to_vec(),
						},],
						range: None,
						offset: None
					}
				))
			);
		}

		for q in [
			"{}",
			"{ }",
		] {
			assert_eq!(
				vector(q, &opts),
				err(vec![
					(q, VerboseErrorKind::Context("vector selector must contain label matchers or metric name")),
				]),
			);
		}
	}

	#[test]
	fn modified_vectors_permutations() {
		for &allow_dots in &[true, false] {
		for &negative_offsets in &[true, false] {
			let opts = ParserOptions::new()
				.allow_dots(allow_dots)
				.negative_offsets(negative_offsets)
				.build();

			modified_vectors(&opts)
		}
		}
	}

	fn modified_vectors(opts: &ParserOptions) {
		modified_vectors_for_instant(
			"foo",
			|| {
				vec![LabelMatch {
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: b"foo".to_vec(),
				}]
			},
			opts,
		);
		modified_vectors_for_instant_concat_offset(
			"foo",
			|| {
				vec![LabelMatch {
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: b"foooffset".to_vec(), // N.B. different label
				}]
			},
			opts,
			false, // should_parse_offset
		);

		for q in [
			"foo{bar!~'baz'}",
			"foo { bar !~ 'baz' }",
		] {
			for f in [
				|instant, labels, opts| modified_vectors_for_instant(instant, labels, opts),
				|instant, labels, opts| modified_vectors_for_instant_concat_offset(instant, labels, opts, true),
			] {
			f(
				q,
				|| {
					vec![
						LabelMatch {
							name: "__name__".to_string(),
							op: LabelMatchOp::Eq,
							value: b"foo".to_vec(),
						},
						LabelMatch {
							name: "bar".to_string(),
							op: LabelMatchOp::RNe,
							value: b"baz".to_vec(),
						},
					]
				},
				opts,
			);
			}
		}

		for q in [
			"{instance!=`localhost`}",
			"{ instance != `localhost` }",
		] {
			for f in [
				|instant, labels, opts| modified_vectors_for_instant(instant, labels, opts),
				|instant, labels, opts| modified_vectors_for_instant_concat_offset(instant, labels, opts, true),
			] {
			f(
				q,
				|| {
					vec![LabelMatch {
						name: "instance".to_string(),
						op: LabelMatchOp::Ne,
						value: b"localhost".to_vec(),
					}]
				},
				opts,
			);
			}
		}
	}

	fn modified_vectors_for_instant(
		instant: &str,
		labels: fn() -> Vec<LabelMatch>,
		opts: &ParserOptions,
	) {
		let v = |tail, range, offset| Ok((
			tail,
			Vector {
				labels: labels(),
				range, offset,
			},
		));

		// regular

		for q in [
			format!("{}[1m]", instant),
			format!("{} [ 1m ]", instant),
		] {
			assert_eq!(
				vector(q.as_str(), opts),
				v("", Some(60.), None),
			);
		}

		// TODO failing "offset5m"
		let q = format!("{} offset 5m", instant);
		assert_eq!(
			vector(q.as_str(), opts),
			v("", None, Some(300.)),
		);
		// for "{}offset" without space see `modified_vectors_for_instant_concat_offset`

		// TODO failing "offset5m"
		for q in [
			format!("{}[1m]offset 5m", instant),
			format!("{} [ 1m ] offset 5m", instant),
		] {
			assert_eq!(
				vector(q.as_str(), opts),
				v("", Some(60.), Some(300.)),
			);
		}
		// for "{}offset" without space see `modified_vectors_for_instant_concat_offset`

		// TODO failing "offset5m"
		// not testing "5m[1m]" since this order of tokens doesn't parse regardless of whitespace
		let q = format!("{} offset 5m [1m]", instant);
		// FIXME should be Error()?
		assert_eq!(
			vector(q.as_str(), opts),
			v("[1m]", None, Some(300.)),
		);

		// negative_offsets

		// TODO *passing* "offset-5m"
		let q = format!("{} offset -5m", instant);
		// "{}offset -5m" (no space before "offset") should be already covered by the case above
		assert_eq!(
			vector(q.as_str(), opts),
			if opts.negative_offsets {
				v("", None, Some(-300.))
			} else {
				v("offset -5m", None, None)
			}
		);
	}

	// similar to `modified_vectors_for_instant` except it has no space between vector and "offset"
	fn modified_vectors_for_instant_concat_offset(
		instant: &str,
		labels: fn() -> Vec<LabelMatch>,
		opts: &ParserOptions,
		should_parse_offset: bool,
	) {
		let v = |tail, range, offset| Ok((
			tail,
			Vector {
				labels: labels(),
				range, offset,
			},
		));

		let q = format!("{}offset 5m", instant);
		assert_eq!(
			vector(q.as_str(), opts),
			if should_parse_offset {
				v("", None, Some(300.))
			} else {
				v("5m", None, None)
			},
		);

		let q = format!("{}offset 5m [1m]", instant);
		assert_eq!(
			vector(q.as_str(), opts),
			if should_parse_offset {
				v("[1m]", None, Some(300.))
			} else {
				v("5m [1m]", None, None)
			}
		);
	}

	#[test]
	fn ranges() {
		for (
			// None: test both true/false
			// Some(bool): test specific option only
			fractional_intervals,
			compound_intervals,
			// input
			src,
			// whether parser returns "" as the remainder
			expect_complete,
			// Some(123) for Ok((..., 123)), None for any Err()
			value,
		) in [
			(None,        None,        "1m",    true,  Some(60.)),
			(Some(true),  None,        "1.5m",  true,  Some(90.)),
			(Some(false), None,        "1.5m",  false, None),
			(None,        Some(true),  "1m30s", true,  Some(90.)),
			(None,        Some(false), "1m30s", false, Some(60.)),
			// should not parse completely if in wrong order
			(None,        Some(true),  "30s1m", false, Some(30.)),
			// should not parse completely if some suffixes repeat
			(None,        Some(true),  "30s5s", false, Some(30.)),
			// should parse if some suffixes are skipped
			(None,        Some(true),  "1d5m",  true,  Some(60. * 60. * 24. + 60. * 5.)),
			// TODO? `1.5h 30s`
		] {
			for fractional_intervals in fractional_intervals.map(|i| vec![i]).unwrap_or_else(|| vec![true, false]) {
			for compound_intervals   in compound_intervals  .map(|i| vec![i]).unwrap_or_else(|| vec![true, false]) {
				let opts = ParserOptions::new()
					.fractional_intervals(fractional_intervals)
					.compound_intervals(compound_intervals)
					.build();

				let output = range_literal(src, &opts);
				if let Some(value) = value {
					let (tail, output) = output.unwrap(); // panics if not Ok()
					assert_eq!(output, value,
						"\n fractional_intervals = {} \n compound_intervals = {} \n src = {}",
						fractional_intervals,
						compound_intervals,
						src,
					);
					assert_eq!(tail.is_empty(), expect_complete);
				} else {
					assert!(output.is_err());
				}
			}
			}
		}

		let opts = ParserOptions::new()
			.ms_duration(true)
			.build();
		assert_eq!(
			range_literal("500ms", &opts),
			Ok(("", 0.5))
		);

		let opts = ParserOptions::new()
			.ms_duration(false)
			.build();
		assert_eq!(
			range_literal("500ms", &opts),
			Ok(("s", 500. * 60.))
		);
	}
}
