use nom::character::complete::multispace0;
use nom::sequence::delimited;

use nom::{
	AsChar,
	InputTakeAtPosition,
};
use nom::IResult;
use nom::error::ParseError;

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

pub(crate) fn delim_ws<I, O, E, P: Fn(I) -> IResult<I, O, E>>(parser: P) -> impl Fn(I) -> IResult<I, O, E>
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
		use $crate::utils::delim_ws;

		delim_ws(
			tuple_separated!(multispace0, ($($args,)*)),
		)
	}};
}
