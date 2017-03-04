// 3rd-party imports

use chomp::types::{U8Input, Input};

// local imports

use super::types::Parameters;
use parsers::{ESInput, ESParseResult, option};
use super::section_13::{StatementList, statement_list};

// 15 ECMAScript Language: Scripts and Modules
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-scripts-and-modules

// 15.1 Scripts

pub struct Script(Option<ScriptBody>);

// TODO: test
pub fn script<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Script> {
    option(i, |i| script_body(i).map(Some), None).map(Script)
}

pub struct ScriptBody(StatementList);

// TODO: test
pub fn script_body<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ScriptBody> {
    // TODO: move this somewhere else
    let params = Parameters::new();
    statement_list(i, &params).map(ScriptBody)
}
