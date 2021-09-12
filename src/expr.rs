use nom::IResult;
use nom::branch::alt;
use nom::bytes::complete::{
	tag,
	tag_no_case,
};
use nom::character::complete::char;
use nom::combinator::{
	map,
	opt,
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
use crate::tuple_ws;
use crate::utils::{
	surrounded_ws,
	delimited_ws,
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

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
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
	String(String),
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

fn label_list(input: &[u8]) -> IResult<&[u8], Vec<String>> {
	delimited_ws(
		char('('),
		separated_list0(surrounded_ws(char(',')), label_name),
		char(')')
	)(input)
}

fn function_aggregation(input: &[u8]) -> IResult<&[u8], AggregationMod> {
	surrounded_ws(map(
		tuple((
			alt((
				map(tag("by"), |_| AggregationAction::By),
				map(tag("without"), |_| AggregationAction::Without),
			)),
			label_list,
		)),
		|(action, labels)| (AggregationMod { action, labels })
	))(input)
}

// it's up to the library user to decide whether argument list is valid or not
fn function_args(allow_periods: bool) -> impl Fn(&[u8]) -> IResult<&[u8], Vec<Node>> {
	move |input| delimited_ws(
		char('('),
		separated_list0(
			surrounded_ws(char(',')),
			alt((
				expression(allow_periods),
				map(string, Node::String),
			))
		),
		char(')')
	)(input)
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

fn function(allow_periods: bool) -> impl Fn(&[u8]) -> IResult<&[u8], Node> {
	move |input| map(
		tuple((
			// I have no idea what counts as a function name but label_name fits well for what's built into the prometheus so let's use that
			label_name,
			// both 'sum by (label, label) (foo)' and 'sum(foo) by (label, label)' are valid
			pair_permutations!(
				function_args(allow_periods),
				opt(function_aggregation),
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

fn atom(allow_periods: bool) -> impl Fn(&[u8]) -> IResult<&[u8], Node> {
	move |input| surrounded_ws(
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
				atom(allow_periods)
			)
			,
			// unary -, well, negates whatever is following it
			map(
				preceded(
					char('-'),
					atom(allow_periods)
				),
				Node::negation
			)
			,
			// function call is parsed before vector: the latter can actually consume function name as a vector, effectively rendering the rest of the expression invalid
			function(allow_periods)
			,
			// FIXME? things like 'and' and 'group_left' are not supposed to parse as a vector: prometheus lexes them unambiguously
			map(
				vector(allow_periods),
				Node::Vector
			)
			,
			delimited(
				char('('),
				expression(allow_periods),
				char(')')
			)
		))
	)(input)
}

macro_rules! with_modifier {
	($literal:expr, $op:expr) => {
		map(preceded(tag($literal), opt(op_modifier)), |op_mod| {
			$op(op_mod)
			})
	};
}

fn with_bool_modifier<'a, O: Fn(bool, Option<OpMod>) -> Op>(literal: &'a str, op: O) -> impl FnMut(&'a [u8]) -> IResult<&[u8], Op> {
	map(
		tuple_ws!((
			tag(literal),
			opt(tag("bool")),
			opt(op_modifier),
		)),
		move |(_, boolness, op_mod)|
			op(boolness.is_some(), op_mod)
	)
}

fn op_modifier(input: &[u8]) -> IResult<&[u8], OpMod> {
	surrounded_ws(map(
		tuple((
			// action
			alt((
				map(tag("on"), |_| OpModAction::RestrictTo),
				map(tag("ignoring"), |_| OpModAction::Ignore),
			)),
			// labels
			label_list,
			// group
			// TODO > Grouping modifiers can only be used for comparison and arithmetic. Operations as and, unless and or operations match with all possible entries in the right vector by default.
			opt(map(
				tuple((
					alt((
						map(tag("group_left"), |_| OpGroupSide::Left),
						map(tag("group_right"), |_| OpGroupSide::Right),
					)),
					map(
						opt(label_list),
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
fn power(allow_periods: bool) -> impl Fn(&[u8]) -> IResult<&[u8], Node> {
	move |input|
	surrounded_ws(map(
		tuple((
			atom(allow_periods),
			opt(tuple((
				with_modifier!("^", Op::Pow),
				power(allow_periods)
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
		fn $name<'a>(allow_periods: bool) -> impl Fn(&'a [u8]) -> IResult<&'a [u8], Node> {
			move |input| surrounded_ws(
				map(tuple((
					$next(allow_periods),
					many0(tuple((
						$op,
						$next(allow_periods)
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
	alt((
		with_modifier!("*", Op::Mul),
		with_modifier!("/", Op::Div),
		with_modifier!("%", Op::Mod),
	))
);

left_op!(
	plus_minus,
	mul_div_mod,
	alt((with_modifier!("+", Op::Plus), with_modifier!("-", Op::Minus)))
);

// if you thing this kind of operator chaining makes little to no sense, think again: it actually matches 'foo' that is both '> bar' and '!= baz'.
// or, speaking another way: comparison operators are really just filters for values in a vector, and this is a chain of filters.
left_op!(
	comparison,
	plus_minus,
	alt((
		with_bool_modifier("==", Op::Eq),
		with_bool_modifier("!=", Op::Ne),
		with_bool_modifier("<=", Op::Le),
		with_bool_modifier(">=", Op::Ge),
		with_bool_modifier("<", Op::Lt),
		with_bool_modifier(">", Op::Gt),
	))
);

left_op!(
	and_unless,
	comparison,
	alt((with_modifier!("and", Op::And), with_modifier!("unless", Op::Unless)))
);

left_op!(or_op, and_unless, with_modifier!("or", Op::Or));

pub(crate) fn expression<'a>(
	allow_periods: bool,
) -> impl Fn(&'a [u8]) -> IResult<&'a [u8], Node> {
	or_op(allow_periods)
}

#[allow(unused_imports)]
#[cfg(test)]
mod tests {
	use super::*;
	use vec;

	use self::Node::{Function, Scalar};
	use self::Op::*;

	// cannot 'use self::Node::operator' for some reason
	#[allow(non_upper_case_globals)]
	const operator: fn(Node, Op, Node) -> Node = Node::operator;
	#[allow(non_upper_case_globals)]
	const negation: fn(Node) -> Node = Node::negation;

	// vector parsing is already tested in `mod vec`, so use that parser instead of crafting lengthy structs all over the test functions
	fn vector(expr: &str) -> Node {
		match vec::vector(false)(cbs(expr)) {
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
		assert_eq!(expression(false)(cbs(input)), Ok((cbs(""), Scalar(output))));
	}

	#[test]
	fn ops() {
		assert_eq!(
			expression(false)(cbs("foo > bar != 0 and 15.5 < xyzzy")),
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
			expression(false)(cbs("foo + bar - baz <= quux + xyzzy")),
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
			expression(false)(cbs("foo + bar % baz")),
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
			expression(false)(cbs("x^y^z")),
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
			expression(false)(cbs("(a+b)*c")),
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
			expression(false)(
				cbs("foo + ignoring (instance) bar / on (cluster) baz"),
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
			expression(false)(cbs("foo + ignoring (instance) group_right bar / on (cluster, shmuster) group_left (job) baz")),
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
			expression(false)(
				cbs("node_cpu{cpu='cpu0'} > bool ignoring (cpu) node_cpu{cpu='cpu1'}"),
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
			expression(false)(cbs("a + -b")),
			Ok((
				cbs(""),
				operator(vector("a"), Plus(None), negation(vector("b")),)
			))
		);

		assert_eq!(
			expression(false)(cbs("a ^ - 1 - b")),
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
			expression(false)(cbs("a ^ - (1 - b)")),
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
			expression(false)(cbs("a +++++++ b")),
			Ok((cbs(""), operator(vector("a"), Plus(None), vector("b"),)))
		);

		assert_eq!(
			expression(false)(cbs("a * --+-b")),
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
			expression(false)(cbs("foo() + bar(baz) + quux(xyzzy, plough)")),
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
			expression(false)(cbs("round(rate(whatever [5m]) > 0, 0.2)")),
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
			expression(false)(
				cbs("label_replace(up, 'instance', '', 'instance', '.*')"),
			),
			Ok((
				cbs(""),
				Function {
					name: "label_replace".to_string(),
					args: vec![
						vector("up"),
						Node::String("instance".to_string()),
						Node::String("".to_string()),
						Node::String("instance".to_string()),
						Node::String(".*".to_string()),
					],
					aggregation: None,
				}
			))
		);
	}

	#[test]
	fn agg_functions() {
		assert_eq!(
			expression(false)(cbs("sum(foo) by (bar) * count(foo) without (bar)")),
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
			expression(false)(cbs("sum by (bar) (foo) * count without (bar) (foo)")),
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
}
