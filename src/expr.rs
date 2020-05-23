use vec::{vector, label_name, Vector};
use str::string;
use nom::{
	recognize_float,
	IResult,
};
use nom::types::CompleteByteSlice;

/// PromQL operators
#[derive(Debug, PartialEq)]
pub enum Op {
	/** `^` */ Pow(Option<OpMod>),

	/** `*` */ Mul(Option<OpMod>),
	/** `/` */ Div(Option<OpMod>),
	/** `%` */ Mod(Option<OpMod>),

	/** `+` */ Plus(Option<OpMod>),
	/** `-` */ Minus(Option<OpMod>),

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

	/** `and` */ And(Option<OpMod>),
	/** `unless` */ Unless(Option<OpMod>),

	/** `or` */ Or(Option<OpMod>),
}

#[derive(Debug, PartialEq)]
pub enum OpModAction { RestrictTo, Ignore }
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
pub enum OpGroupSide { Left, Right }
/// Vector grouping operator modifier (`group_left(…)`/`group_right(…)`).
#[derive(Debug, PartialEq)]
pub struct OpGroupMod {
	pub side: OpGroupSide,
	pub labels: Vec<String>,
}

#[derive(Debug, PartialEq)]
pub enum AggregationAction { Without, By }
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
		y: Box<Node>
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
			y: Box::new(y)
		}
	}
	fn negation(x: Node) -> Node {
		Node::Negation(Box::new(x))
	}
}

named!(label_list <CompleteByteSlice, Vec<String>>, ws!(delimited!(
	char!('('),
	separated_list!(char!(','), label_name),
	char!(')')
)));

named!(function_aggregation <CompleteByteSlice, AggregationMod>, ws!(do_parse!(
	action: alt!(
		  tag!("by") => { |_| AggregationAction::By }
		| tag!("without") => { |_| AggregationAction::Without }
	) >>
	labels: label_list >>
	(AggregationMod { action, labels })
)));

// it's up to the library user to decide whether argument list is valid or not
named!(function_args <CompleteByteSlice, Vec<Node>>, ws!(delimited!(
	char!('('),
	separated_list!(char!(','), alt!(
		  expression => { |e| e }
		| string => { |s| Node::String(s) }
	)),
	char!(')')
)));

fn function(input: CompleteByteSlice) -> IResult<CompleteByteSlice, Node> {
	ws!(
		input,
		do_parse!(
			// I have no idea what counts as a function name but label_name fits well for what's built into the prometheus so let's use that
			name: label_name >>
			args_agg: alt!(
				// both 'sum by (label, label) (foo)' and 'sum(foo) by (label, label)' are valid
				do_parse!(
					args: function_args >>
					aggregation: opt!(function_aggregation) >>
					((args, aggregation))
				)
				|
				do_parse!(
					aggregation: opt!(function_aggregation) >>
					args: function_args >>
					((args, aggregation))
				)
			) >>
			({
				let (args, aggregation) = args_agg;
				Node::Function { name, args, aggregation }
			})
		)
	)
}

fn atom(input: CompleteByteSlice) -> IResult<CompleteByteSlice, Node> {
	ws!(
		input,
		alt!(
			map!(tag_no_case!("NaN"), |_| Node::Scalar(::std::f32::NAN)) // XXX define Node::NaN instead?
			|
			map!(
				flat_map!(call!(recognize_float), parse_to!(f32)),
				Node::Scalar
			)
			|
			// unary + does nothing
			preceded!(char!('+'), atom)
			|
			// unary -, well, negates whatever is following it
			map!(preceded!(char!('-'), atom), |a| Node::negation(a))
			|
			// function call is parsed before vector: the latter can actually consume function name as a vector, effectively rendering the rest of the expression invalid
			function
			|
			// FIXME? things like 'and' and 'group_left' are not supposed to parse as a vector: prometheus lexes them unambiguously
			map!(call!(vector, false), Node::Vector)
			|
			delimited!(char!('('), expression, char!(')'))
		)
	)
}

macro_rules! with_modifier {
	// this macro mimicks another parser macros, hence implicit input argument, $i
	// for comparison, see nom's call!()
	($i:expr, $literal:expr, $op:expr) => (
		map!(
			$i,
			preceded!(tag!($literal), opt!(op_modifier)),
			|op_mod| $op(op_mod)
		)
	)
}

macro_rules! with_bool_modifier {
	($i:expr, $literal:expr, $op:expr) => (
		ws!($i, do_parse!(
			tag!($literal) >>
			boolness: opt!(tag!("bool")) >>
			op_mod: opt!(op_modifier) >>
			($op(boolness.is_some(), op_mod))
		))
	)
}

named!(op_modifier <CompleteByteSlice, OpMod>, ws!(do_parse!(
	action: alt!(
		  tag!("on") => { |_| OpModAction::RestrictTo }
		| tag!("ignoring") => { |_| OpModAction::Ignore }
	) >>
	labels: label_list >>
	// TODO > Grouping modifiers can only be used for comparison and arithmetic. Operations as and, unless and or operations match with all possible entries in the right vector by default.
	group: opt!(ws!(do_parse!(
		side: alt!(
			  tag!("group_left") => { |_| OpGroupSide::Left }
			| tag!("group_right") => { |_| OpGroupSide::Right }
		) >>
		labels: map!(
			opt!(label_list),
			|labels| labels.unwrap_or(vec![])
		) >>
		(OpGroupMod { side, labels })
	))) >>
	(OpMod { action, labels, group })
)));

// ^ is right-associative, so we can actually keep it simple and recursive
fn power(input: CompleteByteSlice) -> IResult<CompleteByteSlice, Node> {
ws!(
input,
do_parse!(
	x: atom >>
	y: opt!(tuple!(
		with_modifier!("^", Op::Pow),
		power
	)) >>
	( match y {
		None => x,
		Some((op, y)) => Node::operator(x, op, y),
	} )
)
)
}

// foo op bar op baz → Node[Node[foo op bar] op baz]
macro_rules! left_op {
	// $next is the parser for operator that takes precenence, or any other kind of non-operator token sequence
	($name:ident, $next:ident!($($next_args:tt)*), $op:ident!($($op_args:tt)*)) => (
		named!($name <CompleteByteSlice, Node>, ws!(do_parse!(
			x: $next!($($next_args)*) >>
			ops: many0!(tuple!(
				$op!($($op_args)*),
				$next!($($next_args)*)
			)) >>
			({
				let mut x = x;
				for (op, y) in ops {
					x = Node::operator(x, op, y);
				}
				x
			})
		)));
	);
	($name:ident, $next:ident, $op:ident!($($op_args:tt)*)) => ( left_op!(
		$name,
		call!($next),
		$op!($($op_args)*)
	); );
	($name:ident, $next:ident!($($next_args:tt)*), $op:ident) => ( left_op!(
		$name,
		$next!($($next_args)*),
		call!($op)
	); );
	($name:ident, $next:ident, $op:ident) => ( left_op!(
		$name,
		call!($next),
		call!($op)
	); );
}

left_op!(mul_div_mod, power, alt!(
	  with_modifier!("*", Op::Mul)
	| with_modifier!("/", Op::Div)
	| with_modifier!("%", Op::Mod)
));

left_op!(plus_minus, mul_div_mod, alt!(
	  with_modifier!("+", Op::Plus)
	| with_modifier!("-", Op::Minus)
));

// if you thing this kind of operator chaining makes little to no sense, think again: it actually matches 'foo' that is both '> bar' and '!= baz'.
// or, speaking another way: comparison operators are really just filters for values in a vector, and this is a chain of filters.
left_op!(comparison, plus_minus, alt!(
	  with_bool_modifier!("==", Op::Eq)
	| with_bool_modifier!("!=", Op::Ne)
	| with_bool_modifier!("<=", Op::Le)
	| with_bool_modifier!(">=", Op::Ge)
	| with_bool_modifier!("<",  Op::Lt)
	| with_bool_modifier!(">",  Op::Gt)
));

left_op!(and_unless, comparison, alt!(
	  with_modifier!("and", Op::And)
	| with_modifier!("unless", Op::Unless)
));

left_op!(or_op, and_unless, with_modifier!("or", Op::Or));

// XXX nom does not allow pub(crate) here
named_attr!(#[doc(hidden)], pub expression <CompleteByteSlice, Node>, call!(or_op));

#[allow(unused_imports)]
#[cfg(test)]
mod tests {
	use super::*;
	use vec;
	use nom::ErrorKind;

	use self::Node::{Scalar, Function};
	use self::Op::*;

	// cannot 'use self::Node::operator' for some reason
	#[allow(non_upper_case_globals)]
	const operator: fn(Node, Op, Node) -> Node = Node::operator;
	#[allow(non_upper_case_globals)]
	const negation: fn(Node) -> Node = Node::negation;

	// vector parsing is already tested in `mod vec`, so use that parser instead of crafting lengthy structs all over the test functions
	fn vector(expr: &str) -> Node {
		match vec::vector(cbs(expr), false) {
			Ok((CompleteByteSlice(b""), x)) => Node::Vector(x),
			_ => panic!("failed to parse label correctly")
		}
	}

	fn cbs(s: &str) -> CompleteByteSlice {
		CompleteByteSlice(s.as_bytes())
	}

	#[test]
	fn scalar() {
		scalar_single("123",       123.);
		scalar_single("-123",     -123.);

		scalar_single("123.",      123.);
		scalar_single("-123.",    -123.);

		scalar_single("123.45",    123.45);
		scalar_single("-123.45",  -123.45);

		scalar_single(".123",      0.123);
		scalar_single("-.123",    -0.123);

		scalar_single("123e5",     123e5);
		scalar_single("-123e5",   -123e5);

		scalar_single("1.23e5",    1.23e5);
		scalar_single("-1.23e5",  -1.23e5);

		scalar_single("1.23e-5",   1.23e-5);
		scalar_single("-1.23e-5", -1.23e-5);
	}

	fn scalar_single(input: &str, output: f32) {
		assert_eq!(expression(cbs(input)), Ok((cbs(""), Scalar(output))));
	}

	#[test]
	fn ops() {
		assert_eq!(
			expression(cbs("foo > bar != 0 and 15.5 < xyzzy")),
			Ok((cbs(""), operator(
				operator(
					operator(vector("foo"), Gt(false, None), vector("bar")),
					Ne(false, None),
					Scalar(0.)
				),
				And(None),
				operator(Scalar(15.5), Lt(false, None), vector("xyzzy")),
			)))
		);

		assert_eq!(
			expression(cbs("foo + bar - baz <= quux + xyzzy")),
			Ok((cbs(""), operator(
				operator(
					operator(vector("foo"), Plus(None), vector("bar")),
					Minus(None),
					vector("baz"),
				),
				Le(false, None),
				operator(vector("quux"), Plus(None), vector("xyzzy")),
			)))
		);

		assert_eq!(
			expression(cbs("foo + bar % baz")),
			Ok((cbs(""), operator(
				vector("foo"),
				Plus(None),
				operator(vector("bar"), Mod(None), vector("baz")),
			)))
		);

		assert_eq!(
			expression(cbs("x^y^z")),
			Ok((cbs(""), operator(
				vector("x"),
				Pow(None),
				operator(vector("y"), Pow(None), vector("z")),
			)))
		);

		assert_eq!(
			expression(cbs("(a+b)*c")),
			Ok((cbs(""), operator(
				operator(vector("a"), Plus(None), vector("b")),
				Mul(None),
				vector("c"),
			)))
		);
	}

	#[test]
	fn op_mods() {
		assert_eq!(
			expression(cbs("foo + ignoring (instance) bar / on (cluster) baz")),
			Ok((cbs(""), operator(
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
			)))
		);

		assert_eq!(
			expression(cbs("foo + ignoring (instance) group_right bar / on (cluster, shmuster) group_left (job) baz")),
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
			expression(cbs("node_cpu{cpu='cpu0'} > bool ignoring (cpu) node_cpu{cpu='cpu1'}")),
			Ok((cbs(""), operator(
				vector("node_cpu{cpu='cpu0'}"),
				Gt(true, Some(OpMod {
					action: OpModAction::Ignore,
					labels: vec!["cpu".to_string()],
					group: None,
				})),
				vector("node_cpu{cpu='cpu1'}"),
			)))
		);
	}

	#[test]
	fn unary() {
		assert_eq!(
			expression(cbs("a + -b")),
			Ok((cbs(""), operator(
				vector("a"),
				Plus(None),
				negation(vector("b")),
			)))
		);

		assert_eq!(
			expression(cbs("a ^ - 1 - b")),
			Ok((cbs(""), operator(
				operator(
					vector("a"),
					Pow(None),
					negation(Scalar(1.)),
				),
				Minus(None),
				vector("b"),
			)))
		);

		assert_eq!(
			expression(cbs("a ^ - (1 - b)")),
			Ok((cbs(""), operator(
				vector("a"),
				Pow(None),
				negation(operator(
					Scalar(1.),
					Minus(None),
					vector("b"),
				)),
			)))
		);

		// yes, these are also valid

		assert_eq!(
			expression(cbs("a +++++++ b")),
			Ok((cbs(""), operator(
				vector("a"),
				Plus(None),
				vector("b"),
			)))
		);

		assert_eq!(
			expression(cbs("a * --+-b")),
			Ok((cbs(""), operator(
				vector("a"),
				Mul(None),
				negation(negation(negation(vector("b")))),
			)))
		);
	}

	#[test]
	fn functions() {
		assert_eq!(
			expression(cbs("foo() + bar(baz) + quux(xyzzy, plough)")),
			Ok((cbs(""), operator(
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
					args: vec![
						vector("xyzzy"),
						vector("plough"),
					],
					aggregation: None,
				},
			)))
		);

		assert_eq!(
			expression(cbs("round(rate(whatever [5m]) > 0, 0.2)")),
			Ok((cbs(""),
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
			expression(cbs("label_replace(up, 'instance', '', 'instance', '.*')")),
			Ok((cbs(""), Function {
				name: "label_replace".to_string(),
				args: vec![
					vector("up"),
					Node::String("instance".to_string()),
					Node::String("".to_string()),
					Node::String("instance".to_string()),
					Node::String(".*".to_string()),
				],
				aggregation: None,
			}))
		);
	}

	#[test]
	fn agg_functions() {
		assert_eq!(
			expression(cbs("sum(foo) by (bar) * count(foo) without (bar)")),
			Ok((cbs(""), operator(
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
			)))
		);

		assert_eq!(
			expression(cbs("sum by (bar) (foo) * count without (bar) (foo)")),
			Ok((cbs(""), operator(
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
			)))
		);
	}
}
