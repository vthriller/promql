#[macro_use]
extern crate nom;

use nom::{alpha, alphanumeric, IResult};
use std::fmt::Debug;

#[derive(Debug)]
enum Op {
	Eq, // =
	Ne, // !=
	REq, // =~
	RNe, // !~
}

#[derive(Debug)]
struct LabelMatch {
	name: String,
	op: Op,
	value: String,
}

named!(label_set <Vec<LabelMatch>>,
	do_parse!(
		char!('{') >>
		labels: ws!(separated_list!(char!(','), do_parse!(
			name: label_name >>
			op: label_op >>
			value: string >>
			(LabelMatch { name, op, value })
		))) >>
		char!('}') >>
		(labels)
	)
);

named!(instant_vec <Vec<LabelMatch>>, map_res!(ws!(do_parse!(
	name: opt!(metric_name) >>
	labels: opt!(complete!(label_set)) >>
	({
		let mut ret = match name {
			Some(name) => vec![ LabelMatch{
				name: "__name__".to_string(),
				op: Op::Eq,
				value: name,
			} ],
			None => vec![],
		};
		if let Some(labels) = labels {
			ret.extend(labels)
		}

		if ret.is_empty() {
			Err("vector selector must contain label matchers or metric name")
		} else { Ok(ret) }
	})
)), |x| x));

// > The metric name … must match the regex [a-zA-Z_:][a-zA-Z0-9_:]*.
// > Label names … must match the regex [a-zA-Z_][a-zA-Z0-9_]*. Label names beginning with __ are reserved for internal use.

named!(metric_name <String>, do_parse!(
	x: alt!(call!(alpha) | is_a!("_:")) >>
	xs: many0!(alt!(call!(alphanumeric) | is_a!("_:"))) >>
	({
		// safe to unwrap in this block: we already matched subset of valid ASCII
		let mut s = String::from_utf8(x.to_vec()).unwrap();
		for x in xs {
			s.push_str(&String::from_utf8(x.to_vec()).unwrap());
		}
		s
	})
));

named!(label_name <String>, do_parse!(
	x: alt!(call!(alpha) | is_a!("_")) >>
	xs: many0!(alt!(call!(alphanumeric) | is_a!("_"))) >>
	({
		// safe to unwrap in this block: we already matched subset of valid ASCII
		let mut s = String::from_utf8(x.to_vec()).unwrap();
		for x in xs {
			s.push_str(&String::from_utf8(x.to_vec()).unwrap());
		}
		s
	})
));

named!(label_op <Op>, alt!(
	  tag!("=~") => { |_| Op::REq }
	| tag!("!~") => { |_| Op::RNe }
	| tag!("=")  => { |_| Op::Eq  } // should come after =~
	| tag!("!=") => { |_| Op::Ne  }
));

// > Label values may contain any Unicode characters.
// > PromQL follows the same [escaping rules as Go](https://golang.org/ref/spec#String_literals).

/* TODO
\OOO (oct)
\xXX
\uXXXX (std::char::from_u32)
\UXXXXXXXX (std::char::from_u32)

TODO? should we really care whether \' is used in ""-strings or vice versa? (Prometheus itself does…)
*/
named!(rune <char>, preceded!(char!('\\'),
        alt!(
		map!(one_of!("abfnrtv\\'\""), |c| match c {
			'a' => '\u{0007}',
			'b' => '\u{0008}',
			'f' => '\u{000c}',
			'n' => '\n',
			'r' => '\r',
			't' => '\t',
			'v' => '\u{000b}',
			'\\' => '\\',
			'\'' => '\'',
			'"' => '"',
			_ => unreachable!(),
		})
	)
));

named!(string <String>, alt!(
	do_parse!(
		char!('"') >>
		s: many0!(alt!(rune | none_of!("\"\\"))) >>
		char!('"') >>
		(s.into_iter().collect())
	)
	|
	do_parse!(
		char!('\'') >>
		s: many0!(alt!(rune | none_of!("'\\"))) >>
		char!('\'') >>
		(s.into_iter().collect())
	)
	|
	do_parse!(
		// raw string literals, where "backslashes have no special meaning"
		char!('`') >>
		s: map_res!(is_not!("`"), |s: &[u8]| String::from_utf8(s.to_vec())) >>
		char!('`') >>
		(s)
	)
));

fn show<O: Debug, E: Debug>(f: fn(&[u8]) -> IResult<&[u8], O, E>, s: &str) {
	print!("{:?}\n", s);
	match f(s.as_bytes()) {
		IResult::Done(tail, res) => print!(
			"Done(\n\t{:?},\n\t{:?},\n)",
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
}
