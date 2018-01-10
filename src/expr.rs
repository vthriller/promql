use vec::{instant_vec, LabelMatch};

#[derive(Debug)]
pub enum Op {
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

#[derive(Debug)]
pub enum Node {
	Operator(Box<Node>, Op, Box<Node>),
	InstantVector(Vec<LabelMatch>),
}

named!(comparison_op <Op>, alt!(
	  tag!("==") => { |_| Op::Eq }
	| tag!("!=") => { |_| Op::Ne }
	| tag!("<=") => { |_| Op::Le }
	| tag!(">=") => { |_| Op::Ge }
	| tag!("<")  => { |_| Op::Lt }
	| tag!(">")  => { |_| Op::Gt }
));

// foo > bar != baz → Node[Node[foo > bar] != baz]
// if you thing this kind of operator chaining makes little to no sense, think again: it actually matches 'foo' that is both '> bar' and '!= baz'.
// or, speaking another way: comparison operators are really just filters for values in a vector, and this is a chain of filters.
named!(comparison <Node>, ws!(do_parse!(
	x: map!(instant_vec, Node::InstantVector) >>
	ops: many0!(do_parse!(
		op: comparison_op >>
		y: map!(instant_vec, Node::InstantVector) >>
		((op, y))
	)) >>
	({
		let mut x = x;
		for (op, y) in ops {
			x = Node::Operator(Box::new(x), op, Box::new(y));
		}
		x
	})
)));

named!(and_unless <Node>, ws!(do_parse!(
	x: comparison >>
	ops: many0!(do_parse!(
		op: alt!(
			  tag!("and") => { |_| Op::And }
			| tag!("unless") => { |_| Op::Unless }
		) >>
		y: comparison >>
		((op, y))
	)) >>
	({
		let mut x = x;
		for (op, y) in ops {
			x = Node::Operator(Box::new(x), op, Box::new(y));
		}
		x
	})
)));

named!(pub expression <Node>, ws!(do_parse!(
	x: and_unless >>
	ops: many0!(do_parse!(
		tag!("or") >>
		y: and_unless >>
		(y)
	)) >>
	({
		let mut x = x;
		for y in ops {
			x = Node::Operator(Box::new(x), Op::Or, Box::new(y));
		}
		x
	})
)));
