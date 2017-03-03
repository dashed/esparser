#![recursion_limit="1000"]

// crates

#[macro_use]
extern crate chomp;
extern crate enum_set;

// modules

#[macro_use]
mod parsers;

// TODO: implement
// ECMAScript 2011 Language Specification (5.1 Edition)
// NOTE: Same as 5th Edition with corrections.
// pub mod june_2011;
// pub use june_2011 as ecmascript_2011;
// pub use june_2011 as es_2011;
// pub use june_2011 as es5;

// TODO: implement
// ECMAScript 2015 Language Specification (6 Edition)
// pub mod june_2015;
// pub use june_2015 as ecmascript_2015;
// pub use june_2015 as es_2015;
// pub use june_2015 as es6;

// ECMAScript 2016 Language Specification (7 Edition)
pub mod june_2016;
pub use june_2016 as ecmascript_2016;
pub use june_2016 as es_2016;
pub use june_2016 as es7;

// TODO: implement
// Next ECMAScript in development (8 Edition)
// pub mod edge;
// pub mod edge as es8;
