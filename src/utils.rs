use nom::character::complete::multispace0;
use nom::combinator::map;
use nom::sequence::delimited;

use nom::{
	AsChar,
	InputTakeAtPosition,
};
use nom::IResult;
use nom::error::ParseError;

use nom::Parser;

#[macro_export]
macro_rules! tuple_separated {
	($delim:expr, ($first:expr, $($rest:expr),* $(,)?)) => {{
		use nom::sequence::{tuple, preceded};
		tuple((
			$first,
			$(
				preceded($delim, $rest),
			)*
		))
	}};
}

pub(crate) fn surrounded_ws<I, O, E, P: FnMut(I) -> IResult<I, O, E>>(parser: P) -> impl FnMut(I) -> IResult<I, O, E>
where
	I: InputTakeAtPosition,
	E: ParseError<I>,
	<I as InputTakeAtPosition>::Item: AsChar + Clone,
{
	delimited(multispace0, parser, multispace0)
}

#[macro_export]
macro_rules! tuple_ws {
	(($($args:expr),* $(,)?)) => {{
		use nom::character::complete::multispace0;
		use $crate::utils::surrounded_ws;
		use $crate::tuple_separated;

		surrounded_ws(
			tuple_separated!(multispace0, ($($args,)*)),
		)
	}};
}

/**
Whitespace-agnostic version of `nom::sequence::delimited`.

Ignores whitespace before and after each of passed parsers.

Unlike `ws!`, it does not affect whitespace handling within passed parsers.
*/
pub(crate) fn delimited_ws<I, O1, O2, O3, E, P1, P2, P3>(p1: P1, p2: P2, p3: P3) -> impl FnMut(I) -> IResult<I, O2, E>
where
	I: InputTakeAtPosition + Clone,
	E: ParseError<I>,
	<I as InputTakeAtPosition>::Item: AsChar + Clone,
	P1: FnMut(I) -> IResult<I, O1, E>,
	P2: FnMut(I) -> IResult<I, O2, E>,
	P3: FnMut(I) -> IResult<I, O3, E>,
{
	map(
		tuple_ws!((p1, p2, p3)),
		|result| result.1
	)
}

/**
A version of nom's `value()` with arguments reversed (makes it look like a `match` arm—just like `map()`!)
*/
pub(crate) fn value<I, O1: Clone, O2, E: ParseError<I>, F: Parser<I, O2, E>,>(
	parser: F,
	val: O1,
) -> impl FnMut(I) -> IResult<I, O1, E> {
	nom::combinator::value(val, parser)
}

#[cfg(test)]
pub(crate) mod tests {
	use nom::Err;
	use nom::error::{Error, ErrorKind};

	pub(crate) fn err<I, O>(input: I, kind: ErrorKind) -> Result<O, Err<Error<I>>> {
		Err(Err::Error(Error::new(input, kind)))
	}
}
