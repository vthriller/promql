#[macro_use]
extern crate nom;

mod vec;
mod expr;

use nom::IResult;
use std::fmt::Debug;

fn show<O: Debug, E: Debug>(f: fn(&[u8]) -> IResult<&[u8], O, E>, s: &str) {
	print!("{:?}\n", s);
	match f(s.as_bytes()) {
		IResult::Done(tail, res) => print!(
			"Done({:#?},\n\t{:?},\n)",
			res,
			String::from_utf8(tail.to_vec()).unwrap()
		),
		x => print!("{:?}", x),
	}
	print!("\n\n");
}

fn main() {
	show(vec::vector, "foo");
	show(vec::vector, "foo {  }");
	show(vec::vector, "foo { bar = 'baz', quux !~ 'xyzzy', lorem = `ipsum \\n dolor \"sit amet\"` }");
	show(vec::vector, "{lorem=~\"ipsum\"}");
	show(vec::vector, "{}"); // should be invalid

	show(vec::vector, "foo [1m]");
	show(vec::vector, "foo [1m] offset 5m");
	show(vec::vector, "foo offset 5m");
	show(vec::vector, "foo offset 5m [1m]"); // should be invalid

	show(expr::expression, "foo > bar != 0 and 15.5 < xyzzy");
	show(expr::expression, "foo + bar - baz <= quux + xyzzy");
	show(expr::expression, "foo + bar % baz");
	show(expr::expression, "x^y^z");
	show(expr::expression, "(a+b)*c");
}
