use nom::character::complete::multispace0;
use nom::combinator::map;
use nom::sequence::delimited;

use nom::error::VerboseError;

pub(crate) type IResult<I, O> = nom::IResult<I, O, VerboseError<I>>;

use nom::{AsChar, InputTakeAtPosition};

use nom::Parser;

#[macro_export]
#[doc(hidden)]
macro_rules! tuple_separated {
	($delim:expr, ($first:expr, $($rest:expr),* $(,)?)) => {{
		use nom::sequence::{tuple, preceded};

		delimited(
			$delim,
			tuple((
				$first,
				$(
					preceded($delim, $rest),
				)*
			)),
			$delim,
		)
	}};
}

pub(crate) fn surrounded_ws<I, Item, O, P: FnMut(I) -> IResult<I, O>>(
	parser: P,
) -> impl FnMut(I) -> IResult<I, O>
where
	I: InputTakeAtPosition<Item = Item>,
	Item: AsChar + Clone,
{
	delimited(multispace0, parser, multispace0)
}

/**
Whitespace-agnostic version of `nom::sequence::delimited`.

Ignores whitespace before and after each of passed parsers.
*/
pub(crate) fn delimited_ws<I, Item, O1, O2, O3, P1, P2, P3>(
	p1: P1,
	p2: P2,
	p3: P3,
) -> impl FnMut(I) -> IResult<I, O2>
where
	I: InputTakeAtPosition<Item = Item> + Clone,
	Item: AsChar + Clone,
	P1: FnMut(I) -> IResult<I, O1>,
	P2: FnMut(I) -> IResult<I, O2>,
	P3: FnMut(I) -> IResult<I, O3>,
{
	map(tuple_separated!(multispace0, (p1, p2, p3)), |result| {
		result.1
	})
}

/**
A version of nom's `value()` with arguments reversed (makes it look like a `match` arm—just like `map()`!)
*/
pub(crate) fn value<I, O1: Clone, O2, F: Parser<I, O2, VerboseError<I>>>(
	parser: F,
	val: O1,
) -> impl FnMut(I) -> IResult<I, O1> {
	nom::combinator::value(val, parser)
}

#[cfg(test)]
pub(crate) mod tests {
	use nom::error::{VerboseError, VerboseErrorKind};
	use nom::Err;

	pub(crate) fn err<I, O>(errors: Vec<(I, VerboseErrorKind)>) -> Result<O, Err<VerboseError<I>>> {
		Err(Err::Error(VerboseError { errors }))
	}
}
