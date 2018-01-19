// > Label values may contain any Unicode characters.
// > PromQL follows the same [escaping rules as Go](https://golang.org/ref/spec#String_literals).

/* TODO
\uXXXX (std::char::from_u32)
\UXXXXXXXX (std::char::from_u32)

TODO? should we really care whether \' is used in ""-strings or vice versa? (Prometheus itself does…)
*/

macro_rules! fixed_length_radix {
	($i:expr, $len:expr, $radix:expr) => {
		// there's no easy way to combine nom::is_(whatever)_digit with something like length_count
		// besides u123::from_str_radix will validate chars anyways, so why do extra work?
		map_res!($i, take!($len), |n: &[u8]| u8::from_str_radix(
			&unsafe { String::from_utf8_unchecked(n.to_vec()) },
			$radix
		))
	}
}

named!(rune <Vec<u8>>, map!(
	preceded!(char!('\\'),
		alt!(
			  char!('a') => { |_| 0x07 }
			| char!('b') => { |_| 0x08 }
			| char!('f') => { |_| 0x0c }
			| char!('n') => { |_| 0x0a }
			| char!('r') => { |_| 0x0d }
			| char!('t') => { |_| 0x09 }
			| char!('v') => { |_| 0x0b }
			| char!('\\') => { |_| 0x5c }
			| char!('\'') => { |_| 0x27 }
			| char!('"') => { |_| 0x22 }
			| fixed_length_radix!(3, 8)
			| preceded!(char!('x'), fixed_length_radix!(2, 16))
		)
	),
	|c| vec![c]
));

// none_of!() returns &[char]
// is_not!() returns &[u8]
// what we need here is Vec<u8>
macro_rules! is_not_v {
	($i:expr, $arg:expr) => {
		map!($i, is_not!($arg), |bytes| bytes.to_vec())
	}
}

macro_rules! chars_except {
	($i:expr, $arg:expr) => {
			map!(
				$i,
				many0!(alt!(rune | is_not_v!($arg))),
				|s| s.concat()
			)
	}
}

named!(pub string <String>, map_res!(
	alt!(
		delimited!(char!('"'), chars_except!("\"\\"), char!('"'))
		|
		delimited!(char!('\''), chars_except!("'\\"), char!('\''))
		|
		// raw string literals, where "backslashes have no special meaning"
		delimited!(char!('`'), is_not_v!("`"), char!('`') )
	),
	|s: Vec<u8>| String::from_utf8(s)
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

	#[test]
	fn runes() {
		assert_eq!(
			rune(&b"\\123"[..]),
			Done(&b""[..], vec![0o123])
		);

		assert_eq!(
			rune(&b"\\x23"[..]),
			Done(&b""[..], vec![0x23])
		);
	}
}
