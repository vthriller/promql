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
