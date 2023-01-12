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
	ParseTo
};
use std::ops::{
	Range,
	RangeFrom,
	RangeTo,
};
use nom::branch::alt;
use nom::bytes::complete::{
	tag,
	tag_no_case,
};
use nom::character::complete::{
	char,
	multispace1,
	not_line_ending,
};
use nom::combinator::{
	fail,
	map,
	opt,
	recognize,
};
use nom::multi::{
	many0,
	separated_list0,
};
use nom::number::complete::float;
use nom::sequence::{
	delimited,
	preceded,
	tuple,
};
use str::string;
use vec::{label_name, vector, Vector};
use crate::{
	ParserOptions,
	tuple_separated,
};
use crate::utils::{
	IResult,
	delimited_ws,
	value,
};

/// PromQL operators
#[derive(Debug, PartialEq)]
pub enum Op {
	/** `^` */
	Pow(Option<OpMod>),

	/** `*` */
	Mul(Option<OpMod>),
	/** `/` */
	Div(Option<OpMod>),
	/** `%` */
	Mod(Option<OpMod>),

	/** `+` */
	Plus(Option<OpMod>),
	/** `-` */
	Minus(Option<OpMod>),

	/// `==`, with optional `bool` modifier in addition to regular operator modifiers
	Eq(bool, Option<OpMod>),
	/// `!=`, with optional `bool` modifier in addition to regular operator modifiers
	Ne(bool, Option<OpMod>),
	/// `<`, with optional `bool` modifier in addition to regular operator modifiers
	Lt(bool, Option<OpMod>),
	/// `>`, with optional `bool` modifier in addition to regular operator modifiers
	Gt(bool, Option<OpMod>),
	/// `<=`, with optional `bool` modifier in addition to regular operator modifiers
	Le(bool, Option<OpMod>),
	/// `>=`, with optional `bool` modifier in addition to regular operator modifiers
	Ge(bool, Option<OpMod>),

	/** `and` */
	And(Option<OpMod>),
	/** `unless` */
	Unless(Option<OpMod>),

	/** `or` */
	Or(Option<OpMod>),
}

#[derive(Debug, PartialEq, Clone)]
pub enum OpModAction {
	RestrictTo,
	Ignore,
}
/// Vector matching operator modifier (`on (…)`/`ignoring (…)`).
#[derive(Debug, PartialEq)]
pub struct OpMod {
	/// Action applied to a list of vectors; whether `on (…)` or `ignored(…)` is used after the operator.
	pub action: OpModAction,
	/// Set of labels to apply `action` to.
	pub labels: Vec<String>,
	/// Additional grouping modifier, if any.
	pub group: Option<OpGroupMod>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum OpGroupSide {
	Left,
	Right,
}
/// Vector grouping operator modifier (`group_left(…)`/`group_right(…)`).
#[derive(Debug, PartialEq)]
pub struct OpGroupMod {
	pub side: OpGroupSide,
	pub labels: Vec<String>,
}

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

/// AST node.
#[derive(Debug, PartialEq)]
pub enum Node {
	/// Operator: `a + ignoring (foo) b`
	Operator {
		/// First operand.
		x: Box<Node>,
		/// Operator itself.
		op: Op,
		/// Second operand.
		y: Box<Node>,
	},
	/// Time series vector.
	Vector(Vector),
	/// Floating point number.
	Scalar(f32),
	/// String literal.
	String(Vec<u8>),
	/// Function call or aggregation operator.
	Function {
		// Function name.
		name: String,
		// Function arguments.
		args: Vec<Node>,
		// Aggregation operator modifiers (`by(…)`/`without(…)`).
		aggregation: Option<AggregationMod>,
	},
	/// Unary negation, e.g. `-b` in `a + -b`
	Negation(Box<Node>),
}
impl Node {
	// these functions are here primarily to avoid explicit mention of `Box::new()` in the code

	fn operator(x: Node, op: Op, y: Node) -> Node {
		Node::Operator {
			x: Box::new(x),
			op,
			y: Box::new(y),
		}
	}
	fn negation(x: Node) -> Node {
		Node::Negation(Box::new(x))
	}
}

fn ws_or_comment<I, C>(opts: ParserOptions) -> impl FnMut(I) -> IResult<I, ()>
where
	I: Clone
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
{
	value(
		many0(alt((
			move |input| if opts.comments {
				recognize(
					tuple((
						char('#'),
						not_line_ending,
					))
				)(input)
			} else {
				fail(input)
			},
			recognize(multispace1),
		))),
		(),
	)
}

fn surrounded_ws_or_comment<I, C, O, P>(opts: ParserOptions, parser: P) -> impl FnMut(I) -> IResult<I, O>
where
	P: FnMut(I) -> IResult<I, O>,
	I: Clone
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
{
	delimited(
		ws_or_comment(opts),
		parser,
		ws_or_comment(opts),
	)
}

fn label_list<I, C>(input: I, opts: ParserOptions) -> IResult<I, Vec<String>>
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
	delimited_ws(
		char('('),
		separated_list0(surrounded_ws_or_comment(opts, char(',')), label_name),
		char(')')
	)(input)
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
		tuple((
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
		+ ParseTo<f32>
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

fn function<I, C>(recursion_level: usize, input: I, opts: ParserOptions) -> IResult<I, Node>
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
		+ ParseTo<f32>
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

fn atom<I, C>(recursion_level: usize, input: I, opts: ParserOptions) -> IResult<I, Node>
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
		+ ParseTo<f32>
		,
	C: AsChar + Clone + Copy,
	&'static str: FindToken<C>,
	<I as InputIter>::IterElem: Clone,
{
	if recursion_level > opts.recursion_limit {
		return Err(
			nom::Err::Failure(
				nom::error::VerboseError {
					errors: vec![
						(input, nom::error::VerboseErrorKind::Context("reached recursion limit")),
					]
				}
			)
		);
	}

	surrounded_ws_or_comment(opts,
		alt((
			map(
				tag_no_case("NaN"),
				|_| Node::Scalar(::std::f32::NAN)
			) // XXX define Node::NaN instead?
			,
			map(
				float,
				Node::Scalar
			)
			,
			// unary + does nothing
			preceded(
				char('+'),
				|i| atom(recursion_level+1, i, opts)
			)
			,
			// unary -, well, negates whatever is following it
			map(
				preceded(
					char('-'),
					|i| atom(recursion_level+1, i, opts)
				),
				Node::negation
			)
			,
			// function call is parsed before vector: the latter can actually consume function name as a vector, effectively rendering the rest of the expression invalid
			|i| function(recursion_level, i, opts)
			,
			// FIXME? things like 'and' and 'group_left' are not supposed to parse as a vector: prometheus lexes them unambiguously
			map(
				|i| vector(i, opts),
				Node::Vector
			)
			,
			delimited(
				char('('),
				|i| expression(recursion_level, i, opts),
				char(')')
			)
		))
	)(input)
}

fn with_modifier<I, C>(opts: ParserOptions, literal: &'static str, op: fn(Option<OpMod>) -> Op) -> impl FnMut(I) -> IResult<I, Op>
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
	map(
		preceded(
			tag(literal),
			opt(move |i| op_modifier(i, opts)),
		),
		op,
	)
}

fn with_bool_modifier<'a, I, C, O: Fn(bool, Option<OpMod>) -> Op>(opts: ParserOptions, literal: &'static str, op: O) -> impl FnMut(I) -> IResult<I, Op>
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
	map(
		tuple_separated!(ws_or_comment(opts), (
			tag(literal),
			opt(tag("bool")),
			opt(move |i| op_modifier(i, opts)),
		)),
		move |(_, boolness, op_mod)|
			op(boolness.is_some(), op_mod)
	)
}

fn op_modifier<I, C>(input: I, opts: ParserOptions) -> IResult<I, OpMod>
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
		tuple((
			// action
			alt((
				value(tag("on"), OpModAction::RestrictTo),
				value(tag("ignoring"), OpModAction::Ignore),
			)),
			// labels
			|i| label_list(i, opts),
			// group
			// TODO > Grouping modifiers can only be used for comparison and arithmetic. Operations as and, unless and or operations match with all possible entries in the right vector by default.
			opt(map(
				tuple((
					alt((
						value(tag("group_left"), OpGroupSide::Left),
						value(tag("group_right"), OpGroupSide::Right),
					)),
					map(
						opt(|i| label_list(i, opts)),
						|labels| labels.unwrap_or_default()
					),
				)),
				|(side, labels)|
					(OpGroupMod { side, labels })
			)),
		)),
		|(action, labels, group)|
			(OpMod { action, labels, group })
	))(input)
}

// ^ is right-associative, so we can actually keep it simple and recursive
fn power<I, C>(recursion_level: usize, input: I, opts: ParserOptions) -> IResult<I, Node>
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
        + ParseTo<f32>
		,
	C: AsChar + Clone + Copy,
	&'static str: FindToken<C>,
	<I as InputIter>::IterElem: Clone,
{
	surrounded_ws_or_comment(opts, map(
		tuple((
			|i| atom(recursion_level, i, opts),
			opt(tuple((
				with_modifier(opts, "^", Op::Pow),
				|i| power(recursion_level, i, opts)
			)))
		)),
		|(x, y)|
			match y {
				None => x,
				Some((op, y)) => Node::operator(x, op, y),
			}
	))(input)
}

// foo op bar op baz → Node[Node[foo op bar] op baz]
macro_rules! left_op {
	// $next is the parser for operator that takes precenence, or any other kind of non-operator token sequence
	($name:ident, $next:ident, $op:expr) => (
		fn $name<I, C>(recursion_level: usize, input: I, opts: ParserOptions) -> IResult<I, Node>
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
				+ ParseTo<f32>
				,
			C: AsChar + Clone + Copy,
			&'static str: FindToken<C>,
			<I as InputIter>::IterElem: Clone,
		{
			surrounded_ws_or_comment(opts,
				map(tuple((
					|i| $next(recursion_level, i, opts),
					many0(tuple((
						$op(opts),
						|i| $next(recursion_level, i, opts)
					))),
				)), |(x, ops)|
					({
						let mut x = x;
						for (op, y) in ops {
							x = Node::operator(x, op, y);
						}
						x
					})
				)
			)(input)
		}
	);
}

left_op!(
	mul_div_mod,
	power,
	|opts|
	alt((
		with_modifier(opts, "*", Op::Mul),
		with_modifier(opts, "/", Op::Div),
		with_modifier(opts, "%", Op::Mod),
	))
);

left_op!(
	plus_minus,
	mul_div_mod,
	|opts|
	alt((
		with_modifier(opts, "+", Op::Plus),
		with_modifier(opts, "-", Op::Minus),
	))
);

// if you thing this kind of operator chaining makes little to no sense, think again: it actually matches 'foo' that is both '> bar' and '!= baz'.
// or, speaking another way: comparison operators are really just filters for values in a vector, and this is a chain of filters.
left_op!(
	comparison,
	plus_minus,
	|opts|
	alt((
		with_bool_modifier(opts, "==", Op::Eq),
		with_bool_modifier(opts, "!=", Op::Ne),
		with_bool_modifier(opts, "<=", Op::Le),
		with_bool_modifier(opts, ">=", Op::Ge),
		with_bool_modifier(opts, "<", Op::Lt),
		with_bool_modifier(opts, ">", Op::Gt),
	))
);

left_op!(
	and_unless,
	comparison,
	|opts|
	alt((
		with_modifier(opts, "and", Op::And),
		with_modifier(opts, "unless", Op::Unless),
	))
);

left_op!(or_op, and_unless, |opts| with_modifier(opts, "or", Op::Or));

pub(crate) fn expression<I, C>(recursion_level: usize, input: I, opts: ParserOptions) -> IResult<I, Node>
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
		+ ParseTo<f32>
		,
	C: AsChar + Clone + Copy,
	&'static str: FindToken<C>,
	<I as InputIter>::IterElem: Clone,
{
	if recursion_level > opts.recursion_limit {
		return Err(
			nom::Err::Failure(
				nom::error::VerboseError {
					errors: vec![
						(input, nom::error::VerboseErrorKind::Context("reached recursion limit")),
					]
				}
			)
		);
	}

	or_op(recursion_level+1, input, opts)
}

#[allow(unused_imports)]
#[cfg(test)]
mod tests {
	use super::*;
	use vec;

	use self::Node::{Function, Scalar};
	use self::Op::*;

	use nom::error::{
		VerboseError,
		VerboseErrorKind,
	};

	// cannot 'use self::Node::operator' for some reason
	#[allow(non_upper_case_globals)]
	const operator: fn(Node, Op, Node) -> Node = Node::operator;
	#[allow(non_upper_case_globals)]
	const negation: fn(Node) -> Node = Node::negation;

	// vector parsing is already tested in `mod vec`, so use that parser instead of crafting lengthy structs all over the test functions
	fn vector(expr: &str) -> Node {
		match vec::vector(cbs(expr), ParserOptions::default()) {
			Ok((b"", x)) => Node::Vector(x),
			_ => panic!("failed to parse label correctly"),
		}
	}

	fn cbs(s: &str) -> &[u8] {
		s.as_bytes()
	}

	#[test]
	fn scalar() {
		scalar_single("123", 123.);
		scalar_single("-123", -123.);

		scalar_single("123.", 123.);
		scalar_single("-123.", -123.);

		scalar_single("123.45", 123.45);
		scalar_single("-123.45", -123.45);

		scalar_single(".123", 0.123);
		scalar_single("-.123", -0.123);

		scalar_single("123e5", 123e5);
		scalar_single("-123e5", -123e5);

		scalar_single("1.23e5", 1.23e5);
		scalar_single("-1.23e5", -1.23e5);

		scalar_single("1.23e-5", 1.23e-5);
		scalar_single("-1.23e-5", -1.23e-5);
	}

	fn scalar_single(input: &str, output: f32) {
		assert_eq!(expression(0, cbs(input), Default::default()), Ok((cbs(""), Scalar(output))));
	}

	#[test]
	fn ops() {
		assert_eq!(
			expression(0,
				cbs("foo > bar != 0 and 15.5 < xyzzy"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					operator(
						operator(vector("foo"), Gt(false, None), vector("bar")),
						Ne(false, None),
						Scalar(0.)
					),
					And(None),
					operator(Scalar(15.5), Lt(false, None), vector("xyzzy")),
				)
			))
		);

		assert_eq!(
			expression(0,
				cbs("foo + bar - baz <= quux + xyzzy"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					operator(
						operator(vector("foo"), Plus(None), vector("bar")),
						Minus(None),
						vector("baz"),
					),
					Le(false, None),
					operator(vector("quux"), Plus(None), vector("xyzzy")),
				)
			))
		);

		assert_eq!(
			expression(0,
				cbs("foo + bar % baz"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					vector("foo"),
					Plus(None),
					operator(vector("bar"), Mod(None), vector("baz")),
				)
			))
		);

		assert_eq!(
			expression(0,
				cbs("x^y^z"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					vector("x"),
					Pow(None),
					operator(vector("y"), Pow(None), vector("z")),
				)
			))
		);

		assert_eq!(
			expression(0,
				cbs("(a+b)*c"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					operator(vector("a"), Plus(None), vector("b")),
					Mul(None),
					vector("c"),
				)
			))
		);
	}

	#[test]
	fn op_mods() {
		assert_eq!(
			expression(0,
				cbs("foo + ignoring (instance) bar / on (cluster) baz"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					vector("foo"),
					Plus(Some(OpMod {
						action: OpModAction::Ignore,
						labels: vec!["instance".to_string()],
						group: None,
					})),
					operator(
						vector("bar"),
						Div(Some(OpMod {
							action: OpModAction::RestrictTo,
							labels: vec!["cluster".to_string()],
							group: None,
						})),
						vector("baz"),
					)
				)
			))
		);

		assert_eq!(
			expression(0,
				cbs("foo + ignoring (instance) group_right bar / on (cluster, shmuster) group_left (job) baz"),
				Default::default(),
			),
			Ok((cbs(""), operator(
				vector("foo"),
				Plus(Some(OpMod {
					action: OpModAction::Ignore,
					labels: vec!["instance".to_string()],
					group: Some(OpGroupMod { side: OpGroupSide::Right, labels: vec![] }),
				})),
				operator(
					vector("bar"),
					Div(Some(OpMod {
						action: OpModAction::RestrictTo,
						labels: vec!["cluster".to_string(), "shmuster".to_string()],
						group: Some(OpGroupMod { side: OpGroupSide::Left, labels: vec!["job".to_string()] }),
					})),
					vector("baz"),
				)
			)))
		);

		assert_eq!(
			expression(0,
				cbs("node_cpu{cpu='cpu0'} > bool ignoring (cpu) node_cpu{cpu='cpu1'}"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					vector("node_cpu{cpu='cpu0'}"),
					Gt(
						true,
						Some(OpMod {
							action: OpModAction::Ignore,
							labels: vec!["cpu".to_string()],
							group: None,
						})
					),
					vector("node_cpu{cpu='cpu1'}"),
				)
			))
		);
	}

	#[test]
	fn unary() {
		assert_eq!(
			expression(0,
				cbs("a + -b"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(vector("a"), Plus(None), negation(vector("b")),)
			))
		);

		assert_eq!(
			expression(0,
				cbs("a ^ - 1 - b"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					operator(vector("a"), Pow(None), negation(Scalar(1.)),),
					Minus(None),
					vector("b"),
				)
			))
		);

		assert_eq!(
			expression(0,
				cbs("a ^ - (1 - b)"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					vector("a"),
					Pow(None),
					negation(operator(Scalar(1.), Minus(None), vector("b"),)),
				)
			))
		);

		// yes, these are also valid

		assert_eq!(
			expression(0,
				cbs("a +++++++ b"),
				Default::default(),
			),
			Ok((cbs(""), operator(vector("a"), Plus(None), vector("b"),)))
		);

		assert_eq!(
			expression(0,
				cbs("a * --+-b"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					vector("a"),
					Mul(None),
					negation(negation(negation(vector("b")))),
				)
			))
		);
	}

	#[test]
	fn functions() {
		assert_eq!(
			expression(0,
				cbs("foo() + bar(baz) + quux(xyzzy, plough)"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					operator(
						Function {
							name: "foo".to_string(),
							args: vec![],
							aggregation: None,
						},
						Plus(None),
						Function {
							name: "bar".to_string(),
							args: vec![vector("baz")],
							aggregation: None,
						},
					),
					Plus(None),
					Function {
						name: "quux".to_string(),
						args: vec![vector("xyzzy"), vector("plough"),],
						aggregation: None,
					},
				)
			))
		);

		assert_eq!(
			expression(0,
				cbs("round(rate(whatever [5m]) > 0, 0.2)"),
				Default::default(),
			),
			Ok((
				cbs(""),
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
			expression(0,
				cbs("label_replace(up, 'instance', '', 'instance', '.*')"),
				Default::default(),
			),
			Ok((
				cbs(""),
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
			expression(0,
				cbs("sum(foo) by (bar) * count(foo) without (bar)"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					Function {
						name: "sum".to_string(),
						args: vec![vector("foo")],
						aggregation: Some(AggregationMod {
							action: AggregationAction::By,
							labels: vec!["bar".to_string()]
						}),
					},
					Mul(None),
					Function {
						name: "count".to_string(),
						args: vec![vector("foo")],
						aggregation: Some(AggregationMod {
							action: AggregationAction::Without,
							labels: vec!["bar".to_string()]
						}),
					},
				)
			))
		);

		assert_eq!(
			expression(0,
				cbs("sum by (bar) (foo) * count without (bar) (foo)"),
				Default::default(),
			),
			Ok((
				cbs(""),
				operator(
					Function {
						name: "sum".to_string(),
						args: vec![vector("foo")],
						aggregation: Some(AggregationMod {
							action: AggregationAction::By,
							labels: vec!["bar".to_string()]
						}),
					},
					Mul(None),
					Function {
						name: "count".to_string(),
						args: vec![vector("foo")],
						aggregation: Some(AggregationMod {
							action: AggregationAction::Without,
							labels: vec!["bar".to_string()]
						}),
					},
				)
			))
		);
	}

	#[test]
	fn comments() {
		let opts = ParserOptions::new()
			.comments(true)
			.build();

		assert_eq!(
			ws_or_comment(opts)("# sfdjvdkfjvbh\n"),
			Ok(("", ())),
		);

		assert_eq!(
			expression(0, cbs("foo # / bar\n/ baz"), opts),
			Ok((
				cbs(""),
				operator(vector("foo"), Div(None), vector("baz"))
			))
		);

		assert_eq!(
			expression(0, cbs("sum(foo) # by (bar)\nby (baz)"), opts),
			Ok((
				cbs(""),
				Function {
					name: "sum".to_string(),
					args: vec![vector("foo")],
					aggregation: Some(AggregationMod {
						action: AggregationAction::By,
						labels: vec!["baz".to_string()]
					}),
				},
			))
		);
	}

	#[test]
	fn recursion_limit() {
		let opts = super::ParserOptions::new()
			.recursion_limit(8)
			.build();

		let mut op = String::new();
		for _ in 1..=9 {
			op.push('+');
		}

		assert_eq!(
			expression(0, format!("a {} b", op).as_str(), opts),
			Err(nom::Err::Failure(VerboseError {
				errors: vec![
					(&" b"[..], VerboseErrorKind::Context("reached recursion limit")),
				],
			})),
		);

		op.push('+');

		assert_eq!(
			expression(0, format!("a {} b", op).as_str(), opts),
			Err(nom::Err::Failure(VerboseError {
				errors: vec![
					(&"+ b"[..], VerboseErrorKind::Context("reached recursion limit")),
				],
			})),
		);
	}

	// run this test with `cargo test stack_overflow -- --nocapture`
	#[test]
	fn stack_overflow() {
		let opts = super::ParserOptions::new()
			.recursion_limit(1024)
			.build();

		let mut op = String::new();
		for _ in 1..256 {
			op.push('+');
			dbg!(op.len());

			use std::io::Write;
			std::io::stdout().flush().unwrap();

			let _ = expression(0, format!("a {} b", op).as_str(), opts);
		}
	}
}
