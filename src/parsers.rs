
// 3rd-party imports

use chomp::combinators::{or};

/// Override the or-combinator used by parse! macro in chomp
macro_rules! __parse_internal_or {
    ($input:expr, $lhs:expr, $rhs:expr) => {
        println!("rofl");
        or($input, $lhs, $rhs)
    };
}
