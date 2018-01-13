use vec::{vector, label_name, Vector};
use nom::{float, digit};

#[derive(Debug, PartialEq)]
pub enum Op {
	Pow, // ^

	Mul, // *
	Div, // /
	Mod, // %

	Plus, // +
	Minus, // -

	Eq, // ==
	Ne, // !=
	Lt, // <
	Gt, // >
	Le, // <=
	Ge, // >=

	And, // and
	Unless, // unless

	Or, // or
}

#[derive(Debug, PartialEq)]
pub enum OpMatchMod {
	None,
	On(Vec<String>),
	Ignoring(Vec<String>),
}

#[derive(Debug, PartialEq)]
pub enum OpGroupMod {
	None,
	Left(Vec<String>),
	Right(Vec<String>),
}

#[derive(Debug, PartialEq)]
pub enum Node {
	Operator {
		x: Box<Node>,
		op: Op,
		match_mod: OpMatchMod,
		group_mod: OpGroupMod,
		y: Box<Node>
	},
	InstantVector(Vector),
	Scalar(f32),
}
impl Node {
	fn operator(x: Node, op: Op, match_mod: OpMatchMod, group_mod: OpGroupMod, y: Node) -> Node {
		Node::Operator {
			x: Box::new(x),
			op,
			match_mod,
			group_mod,
			y: Box::new(y)
		}
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
	map!(vector, Node::InstantVector)
	|
	delimited!(char!('('), expression, char!(')'))
)));

// ^ is right-associative, so we can actually keep it simple and recursive
named!(power <Node>, ws!(do_parse!(
	x: atom >>
	y: opt!(complete!(preceded!(
		tag!("^"),
		// TODO operator modifiers (e.g. 'ignoring (instance)')?
		// who's going to raise one metric's value to the power of another metric's value? for WHAT?!
		power
	))) >>
	( match y {
		None => x,
		Some(y) => Node::operator(x, Op::Pow, OpMatchMod::None, OpGroupMod::None, y),
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
				opt!(ws!(tuple!(
					alt!(
						  tag!("on") => { |_| false }
						| tag!("ignoring") => { |_| true }
					),
					delimited!(
						char!('('),
						many1!(label_name),
						char!(')')
					)
				))),
				// TODO > Grouping modifiers can only be used for comparison and arithmetic. Operations as and, unless and or operations match with all possible entries in the right vector by default.
				opt!(ws!(tuple!(
					alt!(
						  tag!("group_left") => { |_| false }
						| tag!("group_right") => { |_| true }
					),
					opt!(delimited!(
						char!('('),
						many1!(label_name),
						char!(')')
					))
				))),
				$next!($($next_args)*)
			)) >>
			({
				let mut x = x;
				for (op, match_mod, group_mod, y) in ops {
					let match_mod = match match_mod {
						None => OpMatchMod::None,
						Some((true, labels)) => OpMatchMod::Ignoring(labels),
						Some((false, labels)) => OpMatchMod::On(labels),
					};
					let group_mod = match group_mod {
						None => OpGroupMod::None,
						Some((false, labels)) => OpGroupMod::Left(labels.unwrap_or(vec![])),
						Some((true, labels)) => OpGroupMod::Right(labels.unwrap_or(vec![])),
					};
					x = Node::operator(x, op, match_mod, group_mod, y);
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
	  tag!("*") => { |_| Op::Mul }
	| tag!("/") => { |_| Op::Div }
	| tag!("%") => { |_| Op::Mod }
));

left_op!(plus_minus, mul_div_mod, alt!(
	  tag!("+") => { |_| Op::Plus }
	| tag!("-") => { |_| Op::Minus }
));

// if you thing this kind of operator chaining makes little to no sense, think again: it actually matches 'foo' that is both '> bar' and '!= baz'.
// or, speaking another way: comparison operators are really just filters for values in a vector, and this is a chain of filters.
left_op!(comparison, plus_minus, alt!(
	  tag!("==") => { |_| Op::Eq }
	| tag!("!=") => { |_| Op::Ne }
	| tag!("<=") => { |_| Op::Le }
	| tag!(">=") => { |_| Op::Ge }
	| tag!("<")  => { |_| Op::Lt }
	| tag!(">")  => { |_| Op::Gt }
));

left_op!(and_unless, comparison, alt!(
	  tag!("and") => { |_| Op::And }
	| tag!("unless") => { |_| Op::Unless }
));

left_op!(or_op, and_unless, map!(tag!("or"), |_| Op::Or));

named!(pub expression <Node>, call!(or_op));

#[cfg(test)]
mod tests {
	use super::*;
	use vec;
	use nom::IResult::*;
	use nom::ErrorKind;

	// we can't make vec::Vector ourselves due to private fields,
	// and we really don't need to 'cause that's what's already tested in the 'mod vec'
	fn vector(expr: &str) -> Node {
		match vec::vector(expr.as_bytes()) {
			Done(b"", x) => Node::InstantVector(x),
			_ => panic!("failed to parse label correctly")
		}
	}

	#[test]
	fn whatever() {
		use self::Node::Scalar;
		use self::Op::*;
		// cannot 'use self::Node::operator' for some reason
		let operator = Node::operator;

		assert_eq!(
			expression(&b"foo > bar != 0 and 15.5 < xyzzy"[..]),
			Done(&b""[..], operator(
				operator(
					operator(vector("foo"), Gt, OpMatchMod::None, OpGroupMod::None, vector("bar")),
					Ne, OpMatchMod::None, OpGroupMod::None,
					Scalar(0.)
				),
				And, OpMatchMod::None, OpGroupMod::None,
				operator(Scalar(15.5), Lt, OpMatchMod::None, OpGroupMod::None, vector("xyzzy")),
			))
		);

		assert_eq!(
			expression(&b"foo + bar - baz <= quux + xyzzy"[..]),
			Done(&b""[..], operator(
				operator(
					operator(vector("foo"), Plus, OpMatchMod::None, OpGroupMod::None, vector("bar")),
					Minus, OpMatchMod::None, OpGroupMod::None,
					vector("baz"),
				),
				Le, OpMatchMod::None, OpGroupMod::None,
				operator(vector("quux"), Plus, OpMatchMod::None, OpGroupMod::None, vector("xyzzy")),
			))
		);

		assert_eq!(
			expression(&b"foo + bar % baz"[..]),
			Done(&b""[..], operator(
				vector("foo"),
				Plus, OpMatchMod::None, OpGroupMod::None,
				operator(vector("bar"), Mod, OpMatchMod::None, OpGroupMod::None, vector("baz")),
			))
		);

		assert_eq!(
			expression(&b"x^y^z"[..]),
			Done(&b""[..], operator(
				vector("x"),
				Pow, OpMatchMod::None, OpGroupMod::None,
				operator(vector("y"), Pow, OpMatchMod::None, OpGroupMod::None, vector("z")),
			))
		);

		assert_eq!(
			expression(&b"(a+b)*c"[..]),
			Done(&b""[..], operator(
				operator(vector("a"), Plus, OpMatchMod::None, OpGroupMod::None, vector("b")),
				Mul, OpMatchMod::None, OpGroupMod::None,
				vector("c"),
			))
		);

		assert_eq!(
			expression(&b"foo + ignoring (instance) bar / on (cluster) baz"[..]),
			Done(&b""[..], operator(
				vector("foo"),
				Plus,
				OpMatchMod::Ignoring(vec!["instance".to_string()]),
				OpGroupMod::None,
				operator(
					vector("bar"),
					Div,
					OpMatchMod::On(vec!["cluster".to_string()]),
					OpGroupMod::None,
					vector("baz"),
				)
			))
		);

		assert_eq!(
			expression(&b"foo + ignoring (instance) group_right bar / on (cluster) group_left (job) baz"[..]),
			Done(&b""[..], operator(
				vector("foo"),
				Plus,
				OpMatchMod::Ignoring(vec!["instance".to_string()]),
				OpGroupMod::Right(vec![]),
				operator(
					vector("bar"),
					Div,
					OpMatchMod::On(vec!["cluster".to_string()]),
					OpGroupMod::Left(vec!["job".to_string()]),
					vector("baz"),
				)
			))
		);
	}
}
