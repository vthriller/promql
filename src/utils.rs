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

#[macro_export]
macro_rules! tuple_ws {
	(($($args:expr),* $(,)?)) => {{
		use nom::character::complete::multispace0;
		use nom::sequence::delimited;

		delimited(
			multispace0,
			tuple_separated!(multispace0, ($($args,)*)),
			multispace0,
		)
	}};
}
