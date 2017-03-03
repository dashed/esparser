// 5.3 Static Semantic Rules
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-static-semantic-rules

// local imports

use parsers::SyntaxError;

// traits

pub trait StaticSemantics {}

// Ref: http://www.ecma-international.org/ecma-262/7.0/#early-error
pub trait EarlyErrors: StaticSemantics {
    fn check_early_error(&self) -> Option<SyntaxError> {
        None
    }
}
