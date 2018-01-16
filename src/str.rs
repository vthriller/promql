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
		  char!('a') => { |_| '\u{0007}' }
		| char!('b') => { |_| '\u{0008}' }
		| char!('f') => { |_| '\u{000c}' }
		| char!('n') => { |_| '\n' }
		| char!('r') => { |_| '\r' }
		| char!('t') => { |_| '\t' }
		| char!('v') => { |_| '\u{000b}' }
		| char!('\\') => { |_| '\\' }
		| char!('\'') => { |_| '\'' }
		| char!('"') => { |_| '"' }
	)
));

named!(pub string <String>, alt!(
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
	use nom::{Err, ErrorKind};

	#[test]
	fn strings() {
		assert_eq!(
			string(&b"\"lorem ipsum \\\"dolor\\nsit amet\\\"\""[..]),
			Done(&b""[..], "lorem ipsum \"dolor\nsit amet\"".to_string())
		);

		assert_eq!(
			string(&b"'lorem ipsum \\'dolor\\nsit\\tamet\\''"[..]),
			Done(&b""[..], "lorem ipsum 'dolor\nsit\tamet'".to_string())
		);

		assert_eq!(
			string(&b"`lorem ipsum \\\"dolor\\nsit\\tamet\\\"`"[..]),
			Done(&b""[..], "lorem ipsum \\\"dolor\\nsit\\tamet\\\"".to_string())
		);
	}
}
