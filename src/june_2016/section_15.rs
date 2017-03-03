// 15 ECMAScript Language: Scripts and Modules
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-scripts-and-modules

// 3rd-party imports

use chomp::types::{U8Input, Input};

// local imports

use super::types::Parameters;
use parsers::{ESInput, ESParseResult, option};

// 15.1 Scripts

pub struct Script(Option<ScriptBody>);

// TODO: test
pub fn script<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Script> {
    option(i, |i| script_body(i).map(Some), None).map(Script)
}

pub struct ScriptBody;

// TODO: test
pub fn script_body<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ScriptBody> {
    // TODO: complete
    i.ret(ScriptBody)
}
