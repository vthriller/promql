use nom::IResult;
use nom::bytes::complete::{
	is_not,
	take,
};
use nom::branch::alt;
use nom::character::complete::char;
use nom::combinator::{map, map_opt};
use nom::sequence::preceded;

// > Label values may contain any Unicode characters.
// > PromQL follows the same [escaping rules as Go](https://golang.org/ref/spec#String_literals).

// XXX is it an overkill to employ quick-error just to couple two error types that user wouldn't even see?
quick_error! {
	#[derive(Debug)]
	pub enum UnicodeRuneError {
		UTF8(err: ::std::string::FromUtf8Error) {
			from()
		}
		Int(err: ::std::num::ParseIntError) {
			from()
		}
	}
}

// `fixed_length_radix!(T, n, radix)` parses sequence of `n` chars as a `radix`-base number into a type `T`
macro_rules! fixed_length_radix {
	// $type is :ident, not :ty; otherwise "error: expected expression, found `u8`" in "$type::from_str_radix"
	($i:expr, $type:ident, $len:expr, $radix:expr) => {
		// there's no easy way to combine nom::is_(whatever)_digit with something like length_count
		// besides u123::from_str_radix will validate chars anyways, so why do extra work?
		map_res!(
			$i,
			call!(take($len)),
			|n: &[u8]| -> Result<_, UnicodeRuneError> {
				Ok($type::from_str_radix(
					&String::from_utf8(n.to_vec())?,
					$radix,
				)?)
				}
			)
	};
}

// go does not allow invalid unicode scalars (surrogates, chars beyond U+10ffff), and the same applies to from_u32()
fn validate_unicode_scalar(n: u32) -> Option<Vec<u8>> {
	::std::char::from_u32(n).map(|c| {
		let mut tmp = [0; 4];
		c.encode_utf8(&mut tmp).as_bytes().to_vec()
	})
}

fn rune(input: &[u8]) -> IResult<&[u8], Vec<u8>> {
	preceded(char('\\'),
		alt((
			map(char('a'), |_| vec![0x07]),
			map(char('b'), |_| vec![0x08]),
			map(char('f'), |_| vec![0x0c]),
			map(char('n'), |_| vec![0x0a]),
			map(char('r'), |_| vec![0x0d]),
			map(char('t'), |_| vec![0x09]),
			map(char('v'), |_| vec![0x0b]),
			// TODO? should we really care whether \' is used in ""-strings or vice versa? (Prometheus itself does…)
			map(char('\\'), |_| vec![0x5c]),
			map(char('\''), |_| vec![0x27]),
			map(char('"'), |_| vec![0x22]),
			map(
				|input| fixed_length_radix!(input, u8, 3u8, 8),
				|n| vec![n]
			),
			map(
				preceded(char('x'), |input| fixed_length_radix!(input, u8, 2u8, 16)),
				|n| vec![n]
			),
			map_opt(
				preceded(char('u'), |input| fixed_length_radix!(input, u32, 4u8, 16)),
				validate_unicode_scalar
			),
			map_opt(
				preceded(char('U'), |input| fixed_length_radix!(input, u32, 8u8, 16)),
				validate_unicode_scalar
			),
		))
	)(input)
}

// parses sequence of chars that are not in $arg
// returns Vec<u8> (unlike none_of!() which returns &[char], or is_not!() which returns &[u8])
macro_rules! is_not_v {
	($i:expr, $arg:expr) => {
		map!($i, call!(is_not($arg)), |bytes| bytes.to_vec())
	};
}

// sequence of chars (except those marked as invalid in $arg) or rune literals, parsed into Vec<u8>
macro_rules! chars_except {
	($i:expr, $arg:expr) => {
		map!($i, many0!(alt!(rune | is_not_v!($arg))), |s| s.concat())
	};
}

pub fn string(input: &[u8]) -> IResult<&[u8], String> {
	map_res!(input,
		alt!(
			// newlines are not allowed in interpreted quotes, but are totally fine in raw string literals
			delimited!(call!(char('"')), chars_except!("\n\"\\"), call!(char('"')))
			|
			delimited!(call!(char('\'')), chars_except!("\n'\\"), call!(char('\'')))
			|
			// raw string literals, where "backslashes have no special meaning"
			delimited!(call!(char('`')), is_not_v!("`"), call!(char('`')))
		),
		|s: Vec<u8>| String::from_utf8(s)
	)
}

#[allow(unused_imports)]
#[cfg(test)]
mod tests {
	use super::*;
	use crate::utils::tests::*;
	use nom::error::ErrorKind;

	fn cbs(s: &str) -> &[u8] {
		s.as_bytes()
	}

	#[test]
	fn strings() {
		assert_eq!(
			string(cbs("\"lorem ipsum \\\"dolor\\nsit amet\\\"\"")),
			Ok((cbs(""), "lorem ipsum \"dolor\nsit amet\"".to_string()))
		);

		assert_eq!(
			string(cbs("'lorem ipsum \\'dolor\\nsit\\tamet\\''")),
			Ok((cbs(""), "lorem ipsum 'dolor\nsit\tamet'".to_string()))
		);

		assert_eq!(
			string(cbs("`lorem ipsum \\\"dolor\\nsit\\tamet\\\"`")),
			Ok((
				cbs(""),
				"lorem ipsum \\\"dolor\\nsit\\tamet\\\"".to_string()
			))
		);

		// literal, non-escaped newlines

		assert_eq!(
			string(cbs("'this\nis not valid'")),
			err(
				cbs("'this\nis not valid'"),
				ErrorKind::Alt
			)
		);

		assert_eq!(
			string(cbs("`but this\nis`")),
			Ok((cbs(""), "but this\nis".to_string()))
		);
	}

	#[test]
	fn runes() {
		assert_eq!(rune(cbs("\\123")), Ok((cbs(""), vec![0o123])));

		assert_eq!(rune(cbs("\\x23")), Ok((cbs(""), vec![0x23])));

		assert_eq!(
			rune(cbs("\\uabcd")),
			Ok((cbs(""), "\u{abcd}".as_bytes().to_vec()))
		);

		// high surrogate
		assert_eq!(
			rune(cbs("\\uD801")),
			err(cbs("uD801"), ErrorKind::Char)
		);

		assert_eq!(
			rune(cbs("\\U00010330")),
			Ok((cbs(""), "\u{10330}".as_bytes().to_vec()))
		);

		// out of range
		assert_eq!(
			rune(cbs("\\UdeadDEAD")),
			err(cbs("UdeadDEAD"), ErrorKind::MapOpt)
		);

		// utter nonsense

		assert_eq!(
			rune(cbs("\\xxx")),
			err(cbs("xxx"), ErrorKind::Char)
		);

		assert_eq!(
			rune(cbs("\\x1")),
			err(cbs("x1"), ErrorKind::Char)
		);
	}
}
