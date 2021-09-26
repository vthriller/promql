use nom::{
	AsChar,
	Compare,
	InputIter,
	InputLength,
	InputTake,
	InputTakeAtPosition,
	Offset,
	Slice,
};
use std::ops::{
	Range,
	RangeFrom,
	RangeTo,
};
use nom::branch::alt;
use nom::character::complete::{
	char,
	multispace1,
	not_line_ending,
};
use nom::combinator::{
	fail,
	recognize,
};
use nom::multi::many0;
use nom::sequence::{
	delimited,
	tuple,
};
use crate::ParserOptions;
use crate::utils::{
	IResult,
	value,
};

pub(crate) fn ws_or_comment<I, C>(opts: ParserOptions) -> impl FnMut(I) -> IResult<I, ()>
where
	I: Clone
		+ Compare<&'static str>
		+ InputIter<Item = C>
		+ InputLength
		+ InputTake
		+ InputTakeAtPosition<Item = C>
		+ Offset
		+ Slice<Range<usize>>
		+ Slice<RangeFrom<usize>>
		+ Slice<RangeTo<usize>>
		,
	C: AsChar + Clone,
{
	value(
		many0(alt((
			move |input| if opts.comments {
				recognize(
					tuple((
						char('#'),
						not_line_ending,
					))
				)(input)
			} else {
				fail(input)
			},
			recognize(multispace1),
		))),
		(),
	)
}

pub(crate) fn surrounded_ws_or_comment<I, C, O, P>(opts: ParserOptions, parser: P) -> impl FnMut(I) -> IResult<I, O>
where
	P: FnMut(I) -> IResult<I, O>,
	I: Clone
		+ Compare<&'static str>
		+ InputIter<Item = C>
		+ InputLength
		+ InputTake
		+ InputTakeAtPosition<Item = C>
		+ Offset
		+ Slice<Range<usize>>
		+ Slice<RangeFrom<usize>>
		+ Slice<RangeTo<usize>>
		,
	C: AsChar + Clone,
{
	delimited(
		ws_or_comment(opts),
		parser,
		ws_or_comment(opts),
	)
}

#[allow(unused_imports)]
#[cfg(test)]
mod tests {
	use super::*;
	use crate::vec;

	use nom::error::{
		VerboseError,
		VerboseErrorKind,
	};

	#[test]
	fn comments() {
		let src = " \n \t # whatever\n";

		let opts = ParserOptions::new()
			.comments(true)
			.build();

		assert_eq!(
			ws_or_comment(opts)(src),
			Ok(("", ())),
		);

		let opts = ParserOptions::new()
			.comments(false)
			.build();

		assert_eq!(
			ws_or_comment(opts)(src),
			Ok(("# whatever\n", ())),
		);
	}
}
