use nom::{alpha, alphanumeric};

#[derive(Debug)]
pub enum LabelMatchOp {
	Eq, // =
	Ne, // !=
	REq, // =~
	RNe, // !~
}

#[derive(Debug)]
pub struct LabelMatch {
	name: String,
	op: LabelMatchOp,
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

named!(pub instant_vec <Vec<LabelMatch>>, map_res!(ws!(do_parse!(
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
