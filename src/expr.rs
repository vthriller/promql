use vec::{vector, label_name, Vector};
use str::string;
use nom::{float, digit};

/// PromQL operators
#[derive(Debug, PartialEq)]
pub enum Op {
	/** `^` */ Pow,

	/** `*` */ Mul,
	/** `/` */ Div,
	/** `%` */ Mod,

	/** `+` */ Plus,
	/** `-` */ Minus,

	/** `==` */ Eq,
	/** `!=` */ Ne,
	/** `<` */ Lt,
	/** `>` */ Gt,
	/** `<=` */ Le,
	/** `>=` */ Ge,

	/** `and` */ And,
	/** `unless` */ Unless,

	/** `or` */ Or,
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

/// AST node.
#[derive(Debug, PartialEq)]
pub enum Node {
	/// Operator: `a + ignoring (foo) b`
	Operator {
		/// First operand.
		x: Box<Node>,
		/// Operator itself.
		op: Op,
		/// Operator modifier.
		op_mod: Option<OpMod>,
		/// Second operand.
		y: Box<Node>
	},
	/// Time series vector.
	Vector(Vector),
	/// Floating point number.
	Scalar(f32),
	/// String literal.
	String(String),
	/// Function call, with arguments.
	Function(String, Vec<Node>),
	/// Unary negation, e.g. `-b` in `a + -b`
	Negation(Box<Node>),
}
impl Node {
	// these functions are here primarily to avoid explicit mention of `Box::new()` in the code

	fn operator(x: Node, op: Op, op_mod: Option<OpMod>, y: Node) -> Node {
		Node::Operator {
			x: Box::new(x),
			op,
			op_mod,
			y: Box::new(y)
		}
	}
	fn negation(x: Node) -> Node {
		Node::Negation(Box::new(x))
	}
}

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
	complete!(ws!(do_parse!(
		// I have no idea what counts as a function name but label_name fits well for what's built into the prometheus so let's use that
		name: label_name >>
		// it's up to the library user to decide whether argument list is valid or not
		args: delimited!(
			char!('('),
			separated_list!(char!(','), alt!(
				  expression => { |e| e }
				| string => { |s| Node::String(s) }
			)),
			char!(')')
		) >>
		(Node::Function(name, args))
	)))
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
		many1!(label_name),
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
				many1!(label_name),
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
		Some((op_mod, y)) => Node::operator(x, Op::Pow, op_mod, y),
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
				for ((op, op_mod), y) in ops {
					x = Node::operator(x, op, op_mod, y);
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

left_op!(mul_div_mod, power, tuple!(
	alt!(
		  tag!("*") => { |_| Op::Mul }
		| tag!("/") => { |_| Op::Div }
		| tag!("%") => { |_| Op::Mod }
	),
	opt!(op_modifier)
));

left_op!(plus_minus, mul_div_mod, tuple!(
	alt!(
		  tag!("+") => { |_| Op::Plus }
		| tag!("-") => { |_| Op::Minus }
	),
	opt!(op_modifier)
));

// if you thing this kind of operator chaining makes little to no sense, think again: it actually matches 'foo' that is both '> bar' and '!= baz'.
// or, speaking another way: comparison operators are really just filters for values in a vector, and this is a chain of filters.
left_op!(comparison, plus_minus, tuple!(
	alt!(
		  tag!("==") => { |_| Op::Eq }
		| tag!("!=") => { |_| Op::Ne }
		| tag!("<=") => { |_| Op::Le }
		| tag!(">=") => { |_| Op::Ge }
		| tag!("<")  => { |_| Op::Lt }
		| tag!(">")  => { |_| Op::Gt }
	),
	opt!(op_modifier)
));

left_op!(and_unless, comparison, tuple!(
	alt!(
		  tag!("and") => { |_| Op::And }
		| tag!("unless") => { |_| Op::Unless }
	),
	opt!(op_modifier)
));

left_op!(or_op, and_unless, tuple!(
	map!(tag!("or"), |_| Op::Or),
	opt!(op_modifier)
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
	const operator: fn(Node, Op, Option<OpMod>, Node) -> Node = Node::operator;
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
					operator(vector("foo"), Gt, None, vector("bar")),
					Ne, None,
					Scalar(0.)
				),
				And, None,
				operator(Scalar(15.5), Lt, None, vector("xyzzy")),
			))
		);

		assert_eq!(
			expression(&b"foo + bar - baz <= quux + xyzzy"[..]),
			Done(&b""[..], operator(
				operator(
					operator(vector("foo"), Plus, None, vector("bar")),
					Minus, None,
					vector("baz"),
				),
				Le, None,
				operator(vector("quux"), Plus, None, vector("xyzzy")),
			))
		);

		assert_eq!(
			expression(&b"foo + bar % baz"[..]),
			Done(&b""[..], operator(
				vector("foo"),
				Plus, None,
				operator(vector("bar"), Mod, None, vector("baz")),
			))
		);

		assert_eq!(
			expression(&b"x^y^z"[..]),
			Done(&b""[..], operator(
				vector("x"),
				Pow, None,
				operator(vector("y"), Pow, None, vector("z")),
			))
		);

		assert_eq!(
			expression(&b"(a+b)*c"[..]),
			Done(&b""[..], operator(
				operator(vector("a"), Plus, None, vector("b")),
				Mul, None,
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
				Plus,
				Some(OpMod { action: OpModAction::Ignore, labels: vec!["instance".to_string()], group: None }),
				operator(
					vector("bar"),
					Div,
					Some(OpMod { action: OpModAction::RestrictTo, labels: vec!["cluster".to_string()], group: None }),
					vector("baz"),
				)
			))
		);

		assert_eq!(
			expression(&b"foo + ignoring (instance) group_right bar / on (cluster) group_left (job) baz"[..]),
			Done(&b""[..], operator(
				vector("foo"),
				Plus,
				Some(OpMod {
					action: OpModAction::Ignore,
					labels: vec!["instance".to_string()],
					group: Some(OpGroupMod { side: OpGroupSide::Right, labels: vec![] }),
				}),
				operator(
					vector("bar"),
					Div,
					Some(OpMod {
						action: OpModAction::RestrictTo,
						labels: vec!["cluster".to_string()],
						group: Some(OpGroupMod { side: OpGroupSide::Left, labels: vec!["job".to_string()] }),
					}),
					vector("baz"),
				)
			))
		);
	}

	#[test]
	fn unary() {
		assert_eq!(
			expression(&b"a + -b"[..]),
			Done(&b""[..], operator(
				vector("a"),
				Plus, None,
				negation(vector("b")),
			))
		);

		assert_eq!(
			expression(&b"a ^ - 1 - b"[..]),
			Done(&b""[..], operator(
				operator(
					vector("a"),
					Pow, None,
					negation(Scalar(1.)),
				),
				Minus, None,
				vector("b"),
			))
		);

		assert_eq!(
			expression(&b"a ^ - (1 - b)"[..]),
			Done(&b""[..], operator(
				vector("a"),
				Pow, None,
				negation(operator(
					Scalar(1.),
					Minus, None,
					vector("b"),
				)),
			))
		);

		// yes, these are also valid

		assert_eq!(
			expression(&b"a +++++++ b"[..]),
			Done(&b""[..], operator(
				vector("a"),
				Plus, None,
				vector("b"),
			))
		);

		assert_eq!(
			expression(&b"a * --+-b"[..]),
			Done(&b""[..], operator(
				vector("a"),
				Mul, None,
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
					Function("foo".to_string(), vec![]),
					Plus, None,
					Function("bar".to_string(), vec![
						vector("baz")
					])
				),
				Plus, None,
				Function("quux".to_string(), vec![
					vector("xyzzy"),
					vector("plough"),
				])
			))
		);

		assert_eq!(
			expression(&b"round(rate(whatever [5m]) > 0, 0.2)"[..]),
			Done(&b""[..],
				Function("round".to_string(), vec![
					operator(
						Function("rate".to_string(), vec![
							vector("whatever [5m]")
						]),
						Gt, None,
						Scalar(0.),
					),
					Scalar(0.2)
				])
			)
		);

		assert_eq!(
			expression(&b"label_replace(up, 'instance', '', 'instance', '.*')"[..]),
			Done(&b""[..], Function(
				"label_replace".to_string(),
				vec![
					vector("up"),
					Node::String("instance".to_string()),
					Node::String("".to_string()),
					Node::String("instance".to_string()),
					Node::String(".*".to_string()),
				],
			))
		);
	}
}
