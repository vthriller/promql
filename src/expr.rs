use vec::{vector, label_name, Vector};
use str::string;
use nom::{float, digit};

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

named!(function_aggregation <AggregationMod>, complete!(ws!(do_parse!(
	action: alt!(
		  tag!("by") => { |_| AggregationAction::By }
		| tag!("without") => { |_| AggregationAction::Without }
	) >>
	labels: delimited!(
		char!('('),
		separated_list!(char!(','), label_name),
		char!(')')
	) >>
	(AggregationMod { action, labels })
))));

// it's up to the library user to decide whether argument list is valid or not
named!(function_args <Vec<Node>>, delimited!(
	char!('('),
	separated_list!(char!(','), alt!(
		  expression => { |e| e }
		| string => { |s| Node::String(s) }
	)),
	char!(')')
));

named!(function <Node>, ws!(do_parse!(
	// I have no idea what counts as a function name but label_name fits well for what's built into the prometheus so let's use that
	name: label_name >>
	args: function_args >>
	aggregation: opt!(function_aggregation) >>
	(Node::Function { name, args, aggregation })
)));

named!(atom <Node>, ws!(alt!(
	map!(tag_no_case!("NaN"), |_| Node::Scalar(::std::f32::NAN)) // XXX define Node::NaN instead?
	|
	alt!(
		// https://github.com/Geal/nom/issues/437
		map!(float, Node::Scalar)
		|
		// from_utf8_unchecked() on [0-9]+ is actually totally safe
		map_res!(digit, |x: &[u8]| unsafe { String::from_utf8_unchecked(x.to_vec()) }.parse::<f32>().map(Node::Scalar))
	)
	|
	// unary + does nothing
	preceded!(char!('+'), atom)
	|
	// unary -, well, negates whatever is following it
	map!(preceded!(char!('-'), atom), |a| Node::negation(a))
	|
	// function call is parsed before vector: the latter can actually consume function name as a vector, effectively rendering the rest of the expression invalid
	complete!(function)
	|
	// FIXME? things like 'and' and 'group_left' are not supposed to parse as a vector: prometheus lexes them unambiguously
	map!(vector, Node::Vector)
	|
	delimited!(char!('('), expression, char!(')'))
)));

named!(op_modifier <OpMod>, ws!(do_parse!(
	action: alt!(
		  tag!("on") => { |_| OpModAction::RestrictTo }
		| tag!("ignoring") => { |_| OpModAction::Ignore }
	) >>
	labels: delimited!(
		char!('('),
		separated_list!(char!(','), label_name),
		char!(')')
	) >>
	// TODO > Grouping modifiers can only be used for comparison and arithmetic. Operations as and, unless and or operations match with all possible entries in the right vector by default.
	group: opt!(ws!(do_parse!(
		side: alt!(
			  tag!("group_left") => { |_| OpGroupSide::Left }
			| tag!("group_right") => { |_| OpGroupSide::Right }
		) >>
		labels: map!(
			opt!(delimited!(
				char!('('),
				separated_list!(char!(','), label_name),
				char!(')')
			)),
			|labels| labels.unwrap_or(vec![])
		) >>
		(OpGroupMod { side, labels })
	))) >>
	(OpMod { action, labels, group })
)));

// ^ is right-associative, so we can actually keep it simple and recursive
named!(power <Node>, ws!(do_parse!(
	x: atom >>
	y: opt!(complete!(preceded!(
		tag!("^"),
		tuple!(
			opt!(op_modifier),
			power
		)
	))) >>
	( match y {
		None => x,
		Some((op_mod, y)) => Node::operator(x, Op::Pow(op_mod), y),
	} )
)));

// foo op bar op baz → Node[Node[foo op bar] op baz]
macro_rules! left_op {
	// $next is the parser for operator that takes precenence, or any other kind of non-operator token sequence
	($name:ident, $next:ident!($($next_args:tt)*), $op:ident!($($op_args:tt)*)) => (
		named!($name <Node>, ws!(do_parse!(
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

// for now I think I'd better keep alt!() with closures than return boxed closures:
// that way I'm avoiding another match {} later down the operator parser just to construct the value
// also, it allows me to keep list of operator literals in one place so I won't forget to change them somewhere else down the parser code in the future
type ModdedOpMaker = Box<Fn(Option<OpMod>) -> Op>;

left_op!(mul_div_mod, power, do_parse!(
	op: alt!(
		  tag!("*") => { |_| -> ModdedOpMaker { Box::new(Op::Mul) } }
		| tag!("/") => { |_| -> ModdedOpMaker { Box::new(Op::Div) } }
		| tag!("%") => { |_| -> ModdedOpMaker { Box::new(Op::Mod) } }
	) >>
	op_mod: opt!(op_modifier) >>
	(op(op_mod))
));

left_op!(plus_minus, mul_div_mod, do_parse!(
	op: alt!(
		  tag!("+") => { |_| -> ModdedOpMaker { Box::new(Op::Plus) } }
		| tag!("-") => { |_| -> ModdedOpMaker { Box::new(Op::Minus) } }
	) >>
	op_mod: opt!(op_modifier) >>
	(op(op_mod))
));

type ModdedCmpOpMaker = Box<Fn(bool, Option<OpMod>) -> Op>;

// if you thing this kind of operator chaining makes little to no sense, think again: it actually matches 'foo' that is both '> bar' and '!= baz'.
// or, speaking another way: comparison operators are really just filters for values in a vector, and this is a chain of filters.
left_op!(comparison, plus_minus, ws!(do_parse!(
	op: alt!(
		  tag!("==") => { |_| -> ModdedCmpOpMaker { Box::new(Op::Eq) } }
		| tag!("!=") => { |_| -> ModdedCmpOpMaker { Box::new(Op::Ne) } }
		| tag!("<=") => { |_| -> ModdedCmpOpMaker { Box::new(Op::Le) } }
		| tag!(">=") => { |_| -> ModdedCmpOpMaker { Box::new(Op::Ge) } }
		| tag!("<")  => { |_| -> ModdedCmpOpMaker { Box::new(Op::Lt) } }
		| tag!(">")  => { |_| -> ModdedCmpOpMaker { Box::new(Op::Gt) } }
	) >>
	boolness: opt!(tag!("bool")) >>
	op_mod: opt!(op_modifier) >>
	(op(boolness.is_some(), op_mod))
)));

left_op!(and_unless, comparison, do_parse!(
	op: alt!(
		  tag!("and")    => { |_| -> ModdedOpMaker { Box::new(Op::And) } }
		| tag!("unless") => { |_| -> ModdedOpMaker { Box::new(Op::Unless) } }
	) >>
	op_mod: opt!(op_modifier) >>
	(op(op_mod))
));

left_op!(or_op, and_unless, do_parse!(
	op: map!(tag!("or"), |_| -> ModdedOpMaker { Box::new(Op::Or) }) >>
	op_mod: opt!(op_modifier) >>
	(op(op_mod))
));

named_attr!(
/**
Parse expression string into an AST.

This parser operates on byte sequence instead of `&str` because of the fact that PromQL, like Go, allows raw byte sequences to be included in the string literals (e.g. `{omg='∞'}` is equivalent to both `{omg='\u221e'}` and `{omg='\xe2\x88\x9e'}`).
*/,
pub expression <Node>, call!(or_op));

#[cfg(test)]
mod tests {
	use super::*;
	use vec;
	use nom::IResult::*;
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
		match vec::vector(expr.as_bytes()) {
			Done(b"", x) => Node::Vector(x),
			_ => panic!("failed to parse label correctly")
		}
	}

	#[test]
	fn ops() {
		assert_eq!(
			expression(&b"foo > bar != 0 and 15.5 < xyzzy"[..]),
			Done(&b""[..], operator(
				operator(
					operator(vector("foo"), Gt(false, None), vector("bar")),
					Ne(false, None),
					Scalar(0.)
				),
				And(None),
				operator(Scalar(15.5), Lt(false, None), vector("xyzzy")),
			))
		);

		assert_eq!(
			expression(&b"foo + bar - baz <= quux + xyzzy"[..]),
			Done(&b""[..], operator(
				operator(
					operator(vector("foo"), Plus(None), vector("bar")),
					Minus(None),
					vector("baz"),
				),
				Le(false, None),
				operator(vector("quux"), Plus(None), vector("xyzzy")),
			))
		);

		assert_eq!(
			expression(&b"foo + bar % baz"[..]),
			Done(&b""[..], operator(
				vector("foo"),
				Plus(None),
				operator(vector("bar"), Mod(None), vector("baz")),
			))
		);

		assert_eq!(
			expression(&b"x^y^z"[..]),
			Done(&b""[..], operator(
				vector("x"),
				Pow(None),
				operator(vector("y"), Pow(None), vector("z")),
			))
		);

		assert_eq!(
			expression(&b"(a+b)*c"[..]),
			Done(&b""[..], operator(
				operator(vector("a"), Plus(None), vector("b")),
				Mul(None),
				vector("c"),
			))
		);
	}

	#[test]
	fn op_mods() {
		assert_eq!(
			expression(&b"foo + ignoring (instance) bar / on (cluster) baz"[..]),
			Done(&b""[..], operator(
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
			))
		);

		assert_eq!(
			expression(&b"foo + ignoring (instance) group_right bar / on (cluster, shmuster) group_left (job) baz"[..]),
			Done(&b""[..], operator(
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
			))
		);

		assert_eq!(
			expression(&b"node_cpu{cpu='cpu0'} > bool ignoring (cpu) node_cpu{cpu='cpu1'}"[..]),
			Done(&b""[..], operator(
				vector("node_cpu{cpu='cpu0'}"),
				Gt(true, Some(OpMod {
					action: OpModAction::Ignore,
					labels: vec!["cpu".to_string()],
					group: None,
				})),
				vector("node_cpu{cpu='cpu1'}"),
			))
		);
	}

	#[test]
	fn unary() {
		assert_eq!(
			expression(&b"a + -b"[..]),
			Done(&b""[..], operator(
				vector("a"),
				Plus(None),
				negation(vector("b")),
			))
		);

		assert_eq!(
			expression(&b"a ^ - 1 - b"[..]),
			Done(&b""[..], operator(
				operator(
					vector("a"),
					Pow(None),
					negation(Scalar(1.)),
				),
				Minus(None),
				vector("b"),
			))
		);

		assert_eq!(
			expression(&b"a ^ - (1 - b)"[..]),
			Done(&b""[..], operator(
				vector("a"),
				Pow(None),
				negation(operator(
					Scalar(1.),
					Minus(None),
					vector("b"),
				)),
			))
		);

		// yes, these are also valid

		assert_eq!(
			expression(&b"a +++++++ b"[..]),
			Done(&b""[..], operator(
				vector("a"),
				Plus(None),
				vector("b"),
			))
		);

		assert_eq!(
			expression(&b"a * --+-b"[..]),
			Done(&b""[..], operator(
				vector("a"),
				Mul(None),
				negation(negation(negation(vector("b")))),
			))
		);
	}

	#[test]
	fn functions() {
		assert_eq!(
			expression(&b"foo() + bar(baz) + quux(xyzzy, plough)"[..]),
			Done(&b""[..], operator(
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
			))
		);

		assert_eq!(
			expression(&b"round(rate(whatever [5m]) > 0, 0.2)"[..]),
			Done(&b""[..],
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
			)
		);

		assert_eq!(
			expression(&b"label_replace(up, 'instance', '', 'instance', '.*')"[..]),
			Done(&b""[..], Function {
				name: "label_replace".to_string(),
				args: vec![
					vector("up"),
					Node::String("instance".to_string()),
					Node::String("".to_string()),
					Node::String("instance".to_string()),
					Node::String(".*".to_string()),
				],
				aggregation: None,
			})
		);
	}

	#[test]
	fn agg_functions() {
		assert_eq!(
			expression(&b"sum(foo) by (bar) * count(foo) without (bar)"[..]),
			Done(&b""[..], operator(
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
			))
		);
	}
}
