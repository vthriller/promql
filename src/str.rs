// > Label values may contain any Unicode characters.
// > PromQL follows the same [escaping rules as Go](https://golang.org/ref/spec#String_literals).

/* TODO
\UXXXXXXXX (std::char::from_u32)

TODO? should we really care whether \' is used in ""-strings or vice versa? (Prometheus itself does…)
*/

macro_rules! fixed_length_radix {
	// $type is :ident, not :ty; otherwise "error: expected expression, found `u8`" in "$type::from_str_radix"
	($i:expr, $type:ident, $len:expr, $radix:expr) => {
		// there's no easy way to combine nom::is_(whatever)_digit with something like length_count
		// besides u123::from_str_radix will validate chars anyways, so why do extra work?
		map_res!($i, take!($len), |n: &[u8]| $type::from_str_radix(
			&unsafe { String::from_utf8_unchecked(n.to_vec()) },
			$radix
		))
	}
}

named!(rune <Vec<u8>>,
	preceded!(char!('\\'),
		alt!(
			  char!('a') => { |_| vec![0x07] }
			| char!('b') => { |_| vec![0x08] }
			| char!('f') => { |_| vec![0x0c] }
			| char!('n') => { |_| vec![0x0a] }
			| char!('r') => { |_| vec![0x0d] }
			| char!('t') => { |_| vec![0x09] }
			| char!('v') => { |_| vec![0x0b] }
			| char!('\\') => { |_| vec![0x5c] }
			| char!('\'') => { |_| vec![0x27] }
			| char!('"') => { |_| vec![0x22] }
			| map!(
				fixed_length_radix!(u8, 3, 8),
				|n| vec![n]
			)
			| map!(
				preceded!(char!('x'), fixed_length_radix!(u8, 2, 16)),
				|n| vec![n]
			)
			// go does not allow invalid unicode scalars (surrogates, chars beyond U+10ffff), and the same applies to from_u32()
			| map_opt!(
				preceded!(char!('u'), fixed_length_radix!(u32, 4, 16)),
				|n| ::std::char::from_u32(n).map(|c| {
					let mut tmp = [0; 4];
					c.encode_utf8(&mut tmp).as_bytes().to_vec()
				})
			)
		)
	)
);

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

		assert_eq!(
			rune(&b"\\uabcd"[..]),
			Done(&b""[..], "\u{abcd}".as_bytes().to_vec())
		);

		// high surrogate
		assert_eq!(
			rune(&b"\\uD801"[..]),
			Error(Err::Position(ErrorKind::Alt, &b"uD801"[..]))
		);
	}
}
