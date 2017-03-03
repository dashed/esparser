// 15 ECMAScript Language: Scripts and Modules
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-scripts-and-modules

// 3rd-party imports

use chomp::types::{U8Input, Input};

// local imports

use super::types::Parameters;
use parsers::{ESInput, ESParseResult};

// 15.1 Scripts

pub struct Script;

// TODO: test
pub fn script<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, Script> {

    i.ret(Script)
}

#[test]
fn foo() {}
