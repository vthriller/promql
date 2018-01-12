use nom::{alpha, alphanumeric, digit};

#[derive(Debug, PartialEq)]
pub enum LabelMatchOp {
	Eq, // =
	Ne, // !=
	REq, // =~
	RNe, // !~
}

#[derive(Debug, PartialEq)]
pub struct LabelMatch {
	name: String,
	op: LabelMatchOp,
	value: String,
}

named!(label_set <Vec<LabelMatch>>, delimited!(
	char!('{'),
	ws!(separated_list!(char!(','), do_parse!(
		name: label_name >>
		op: label_op >>
		value: string >>
		(LabelMatch { name, op, value })
	))),
	char!('}')
));

#[derive(Debug, PartialEq)]
pub struct Vector {
	labels: Vec<LabelMatch>,
	range: Option<usize>,
	offset: Option<usize>,
}

named!(instant_vec <Vec<LabelMatch>>, map_res!(ws!(do_parse!(
	name: opt!(metric_name) >>
	labels: opt!(complete!(label_set)) >>
	({
		let mut ret = match name {
			Some(name) => vec![ LabelMatch{
				name: "__name__".to_string(),
				op: LabelMatchOp::Eq,
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

named!(range_literal <usize>, map!(
	pair!(digit, one_of!("smhdwy")),
	|(n, suf)| {
		// from_utf8_unchecked() on [0-9]+ is actually totally safe
		// FIXME unwrap? FIXME copy-pasted from expr.rs
		let n = unsafe { String::from_utf8_unchecked(n.to_vec()) }.parse::<usize>().unwrap();
		n * match suf {
			's' => 1,
			'm' => 60,
			'h' => 60 * 60,
			'd' => 60 * 60 * 24,
			'w' => 60 * 60 * 24 * 7,
			'y' => 60 * 60 * 24 * 365, // XXX leap years?
			_ => unreachable!(),
		}
	}
));

named!(pub vector <Vector>, ws!(do_parse!(
	labels: instant_vec >>
	range: opt!(complete!(
		delimited!(char!('['), range_literal, char!(']'))
	)) >>
	offset: opt!(complete!(
		ws!(preceded!(tag!("offset"), range_literal))
	)) >>
	(Vector {labels, range, offset})
)));

// > The metric name … must match the regex [a-zA-Z_:][a-zA-Z0-9_:]*.
// > Label names … must match the regex [a-zA-Z_][a-zA-Z0-9_]*. Label names beginning with __ are reserved for internal use.

named!(metric_name <String>, map!(
	recognize!(tuple!(
		alt!(call!(alpha) | is_a!("_:")),
		many0!(alt!(call!(alphanumeric) | is_a!("_:")))
	)),
	// safe to unwrap: we already matched subset of valid ASCII
	|s| String::from_utf8(s.to_vec()).unwrap()
));

named!(label_name <String>, map!(
	recognize!(tuple!(
		alt!(call!(alpha) | is_a!("_")),
		many0!(alt!(call!(alphanumeric) | is_a!("_")))
	)),
	// safe to unwrap: we already matched subset of valid ASCII
	|s| String::from_utf8(s.to_vec()).unwrap()
));

named!(label_op <LabelMatchOp>, alt!(
	  tag!("=~") => { |_| LabelMatchOp::REq }
	| tag!("!~") => { |_| LabelMatchOp::RNe }
	| tag!("=")  => { |_| LabelMatchOp::Eq  } // should come after =~
	| tag!("!=") => { |_| LabelMatchOp::Ne  }
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

#[cfg(test)]
mod tests {
	use super::*;
	use nom::IResult::*;
	use nom::ErrorKind;

	#[test]
	fn instant_vectors() {
		assert_eq!(vector(&b"foo"[..]), Done(&b""[..], Vector{
			labels: vec![
				LabelMatch{
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: "foo".to_string(),
				},
			],
			range: None,
			offset: None
		}));

		assert_eq!(vector(&b"foo { }"[..]), Done(&b""[..], Vector{
			labels: vec![
				LabelMatch{
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: "foo".to_string(),
				},
			],
			range: None,
			offset: None
		}));

		assert_eq!(vector(&b"foo { bar = 'baz', quux !~ 'xyzzy', lorem = `ipsum \\n dolor \"sit amet\"` }"[..]), Done(&b""[..], Vector{
			labels: vec![
				LabelMatch{
					name: "__name__".to_string(),
					op: LabelMatchOp::Eq,
					value: "foo".to_string(),
				},
				LabelMatch{
					name: "bar".to_string(),
					op: LabelMatchOp::Eq,
					value: "baz".to_string(),
				},
				LabelMatch{
					name: "quux".to_string(),
					op: LabelMatchOp::RNe,
					value: "xyzzy".to_string(),
				},
				LabelMatch{
					name: "lorem".to_string(),
					op: LabelMatchOp::Eq,
					value: "ipsum \\n dolor \"sit amet\"".to_string(),
				},
			],
			range: None,
			offset: None
		}));

		assert_eq!(vector(&b"{lorem=~\"ipsum\"}"[..]), Done(&b""[..], Vector{
			labels: vec![
				LabelMatch{
					name: "lorem".to_string(),
					op: LabelMatchOp::REq,
					value: "ipsum".to_string(),
				},
			],
			range: None,
			offset: None
		}));

		assert_eq!(vector(&b"{}"[..]), Error(ErrorKind::MapRes));
	}

	#[test]
	fn modified_vectors() {
		modified_vectors_for_instant("foo", || vec![
			LabelMatch{
				name: "__name__".to_string(),
				op: LabelMatchOp::Eq,
				value: "foo".to_string(),
			},
		]);

		modified_vectors_for_instant("foo {bar!~\"baz\"}", || vec![
			LabelMatch{
				name: "__name__".to_string(),
				op: LabelMatchOp::Eq,
				value: "foo".to_string(),
			},
			LabelMatch{
				name: "bar".to_string(),
				op: LabelMatchOp::RNe,
				value: "baz".to_string(),
			},
		]);

		modified_vectors_for_instant("{instance!=`localhost`}", || vec![
			LabelMatch{
				name: "instance".to_string(),
				op: LabelMatchOp::Ne,
				value: "localhost".to_string(),
			},
		]);
	}

	fn modified_vectors_for_instant(instant: &str, labels: fn() -> Vec<LabelMatch>) {
		assert_eq!(vector(format!("{} [1m]", instant).as_bytes()), Done(&b""[..], Vector{
			labels: labels(),
			range: Some(60),
			offset: None,
		}));

		assert_eq!(vector(format!("{} offset 5m", instant).as_bytes()), Done(&b""[..], Vector{
			labels: labels(),
			range: None,
			offset: Some(300),
		}));

		assert_eq!(vector(format!("{} [1m] offset 5m", instant).as_bytes()), Done(&b""[..], Vector{
			labels: labels(),
			range: Some(60),
			offset: Some(300),
		}));

		// FIXME should be Error()?
		assert_eq!(vector(format!("{} offset 5m [1m]", instant).as_bytes()), Done(&b"[1m]"[..], Vector{
			labels: labels(),
			range: None,
			offset: Some(300),
		}));
	}
}
