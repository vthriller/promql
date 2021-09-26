use nom::{
	AsBytes,
	AsChar,
	Compare,
	FindToken,
	InputIter,
	InputLength,
	InputTake,
	InputTakeAtPosition,
	Offset,
	Slice,
};
use std::ops::{
	Range,
	RangeFrom,
	RangeTo,
};
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::char;
use nom::combinator::{
	map,
	opt,
};
use nom::multi::separated_list0;
use nom::sequence::tuple;
use vec::label_name;
use crate::{
	ParserOptions,
	tuple_separated,
};
use crate::str::string;
use crate::expr::{
	Node,
	expression,
	label_list,
};
use crate::whitespace::{
	ws_or_comment,
	surrounded_ws_or_comment,
};
use crate::utils::{
	IResult,
	delimited_ws,
	value,
};

#[derive(Debug, PartialEq, Clone)]
pub enum AggregationAction {
	Without,
	By,
}
#[derive(Debug, PartialEq)]
pub struct AggregationMod {
	// Action applied to a list of vectors; whether `by (…)` or `without (…)` is used.
	pub action: AggregationAction,
	pub labels: Vec<String>,
}

fn function_aggregation<I, C>(input: I, opts: ParserOptions) -> IResult<I, AggregationMod>
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
	surrounded_ws_or_comment(opts, map(
		tuple_separated!(ws_or_comment(opts), (
			alt((
				value(tag("by"), AggregationAction::By),
				value(tag("without"), AggregationAction::Without),
			)),
			|i| label_list(i, opts),
		)),
		|(action, labels)| (AggregationMod { action, labels })
	))(input)
}

// it's up to the library user to decide whether argument list is valid or not
fn function_args<I, C>(recursion_level: usize, opts: ParserOptions) -> impl FnMut(I) -> IResult<I, Vec<Node>>
where
	I: Clone + Copy
		+ AsBytes
		+ Compare<&'static str>
		+ for<'a> Compare<&'a [u8]>
		+ InputIter<Item = C>
		+ InputLength
		+ InputTake
		+ InputTakeAtPosition<Item = C>
		+ Offset
		+ Slice<Range<usize>>
		+ Slice<RangeFrom<usize>>
		+ Slice<RangeTo<usize>>
		,
	C: AsChar + Clone + Copy,
	&'static str: FindToken<C>,
	<I as InputIter>::IterElem: Clone,
{
	delimited_ws(
		char('('),
		separated_list0(
			surrounded_ws_or_comment(opts, char(',')),
			alt((
				move |i| expression(recursion_level, i, opts),
				map(string, Node::String),
			))
		),
		char(')')
	)
}

macro_rules! pair_permutations {
	($p1:expr, $p2:expr $(,)?) => {
	alt((
		tuple(($p1, $p2)),
		map(
			tuple(($p2, $p1)),
			|(o2, o1)| (o1, o2),
		),
	))
	};
}

pub(crate) fn function<I, C>(recursion_level: usize, input: I, opts: ParserOptions) -> IResult<I, Node>
where
	I: Clone + Copy
		+ AsBytes
		+ Compare<&'static str>
		+ for<'a> Compare<&'a [u8]>
		+ InputIter<Item = C>
		+ InputLength
		+ InputTake
		+ InputTakeAtPosition<Item = C>
		+ Offset
		+ Slice<Range<usize>>
		+ Slice<RangeFrom<usize>>
		+ Slice<RangeTo<usize>>
		,
	C: AsChar + Clone + Copy,
	&'static str: FindToken<C>,
	<I as InputIter>::IterElem: Clone,
{
	map(
		tuple((
			// I have no idea what counts as a function name but label_name fits well for what's built into the prometheus so let's use that
			label_name,
			// both 'sum by (label, label) (foo)' and 'sum(foo) by (label, label)' are valid
			pair_permutations!(
				function_args(recursion_level, opts),
				opt(|i| function_aggregation(i, opts)),
			),
		)),
		|(name, (args, agg))|
			Node::Function {
				name,
				args,
				aggregation: agg,
			}
	)(input)
}

#[allow(unused_imports)]
#[cfg(test)]
mod tests {
	use super::*;
	use crate::vec;

	use crate::expr::Node::{Function, Scalar};
	use crate::expr::Op::{self, *};

	use nom::error::{
		VerboseError,
		VerboseErrorKind,
	};

	// cannot 'use self::Node::operator' for some reason
	#[allow(non_upper_case_globals)]
	const operator: fn(Node, Op, Node) -> Node = Node::operator;

	// vector parsing is already tested in `mod vec`, so use that parser instead of crafting lengthy structs all over the test functions
	fn vector(expr: &str) -> Node {
		match vec::vector(expr, ParserOptions::default()) {
			Ok(("", x)) => Node::Vector(x),
			_ => panic!("failed to parse label correctly"),
		}
	}

	#[test]
	fn functions() {
		assert_eq!(
			function(0,
				"foo(bar, baz)",
				Default::default(),
			),
			Ok((
				"",
				Function {
					name: "foo".to_string(),
					args: vec![vector("bar"), vector("baz"),],
					aggregation: None,
				},
			))
		);

		assert_eq!(
			function(0,
				"round(rate(whatever [5m]) > 0, 0.2)",
				Default::default(),
			),
			Ok((
				"",
				Function {
					name: "round".to_string(),
					args: vec![
						operator(
							Function {
								name: "rate".to_string(),
								args: vec![vector("whatever [5m]")],
								aggregation: None,
							},
							Gt(false, None),
							Scalar(0.),
						),
						Scalar(0.2)
					],
					aggregation: None,
				}
			))
		);

		assert_eq!(
			function(0,
				"label_replace(up, 'instance', '', 'instance', '.*')",
				Default::default(),
			),
			Ok((
				"",
				Function {
					name: "label_replace".to_string(),
					args: vec![
						vector("up"),
						Node::String(b"instance".to_vec()),
						Node::String(b"".to_vec()),
						Node::String(b"instance".to_vec()),
						Node::String(b".*".to_vec()),
					],
					aggregation: None,
				}
			))
		);
	}

	#[test]
	fn agg_functions() {
		assert_eq!(
			function(0,
				"sum(foo) by (bar)",
				Default::default(),
			),
			Ok((
				"",
				Function {
					name: "sum".to_string(),
					args: vec![vector("foo")],
					aggregation: Some(AggregationMod {
						action: AggregationAction::By,
						labels: vec!["bar".to_string()]
					}),
				},
			))
		);

		assert_eq!(
			expression(0,
				"count without (bar) (foo)",
				Default::default(),
			),
			Ok((
				"",
				Function {
					name: "count".to_string(),
					args: vec![vector("foo")],
					aggregation: Some(AggregationMod {
						action: AggregationAction::Without,
						labels: vec!["bar".to_string()]
					}),
				},
			))
		);
	}
}
