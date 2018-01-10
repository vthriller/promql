#[macro_use]
extern crate nom;

mod vec;
mod expr;

use vec::instant_vec;

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
	show(instant_vec, "foo");
	show(instant_vec, "foo {  }");
	show(instant_vec, "foo { bar = 'baz', quux !~ 'xyzzy', lorem = `ipsum \\n dolor \"sit amet\"` }");
	show(instant_vec, "{lorem=~\"ipsum\"}");
	show(instant_vec, "{}"); // should be invalid

	show(expr::expression, "foo > bar > baz")
}
