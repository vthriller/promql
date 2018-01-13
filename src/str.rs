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
