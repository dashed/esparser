// 3rd-party imports

use chomp::types::{U8Input, Input};
use downcast_rs::Downcast;

// local imports

use super::types::Parameters;
use parsers::{ESInput, ESParseResult, option, eof};
use super::section_13::{StatementList, statement_list};

// 15 ECMAScript Language: Scripts and Modules
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-scripts-and-modules

// 15.1 Scripts

// Script

pub trait ScriptTrait: Downcast {}
impl_downcast!(ScriptTrait);

pub enum Script {
    ScriptBody(Option<ScriptBody>),
    Custom(Box<ScriptTrait>),
}

type ScriptTraitParser<I> = Box<FnMut(ESInput<I>) -> ESParseResult<I, Box<ScriptTrait>>>;

// TODO: test
pub fn script<I: U8Input>(i: ESInput<I>,
                          custom_parser: Option<ScriptTraitParser<I>>)
                          -> ESParseResult<I, Script> {

    #[inline]
    fn parse<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Script> {
        option(i, |i| script_body(i).map(Some), None).map(Script::ScriptBody)
    }

    match custom_parser {
        None => parse(i).bind(|i, result| eof(i).map(|_| result)),
        Some(mut custom_parser) => {
            parse!{i;

                let script =
                    (i -> custom_parser(i).map(Script::Custom)) <|>
                    parse();

                eof();

                ret script
            }
        }
    }
}

#[cfg(test)]
mod script_test {

    // 3rd-party imports

    use chomp::primitives::IntoInner;
    use chomp::types::numbering::InputPosition;
    use chomp::types::U8Input;
    use chomp::types::Input;
    use chomp::primitives::Primitives;

    // crate imports

    use june_2016::section_15::{script, ScriptTrait, Script};
    use parsers::{ESParseResult, ESInput};
    use parsers::current_position::CurrentPosition;
    use parsers::string;

    #[test]
    fn custom_parser() {

        struct Foo;
        impl ScriptTrait for Foo {}

        fn user_parser<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Box<ScriptTrait>> {
            string(i, b"input").map(|_| -> Box<ScriptTrait> { Box::new(Foo) })
        }

        let user_parser = Box::new(user_parser);


        let i = InputPosition::new("input".as_bytes(), CurrentPosition::new());

        let (mut input, parse_result) = script(i, Some(user_parser)).into_inner();

        let buf = input.consume_remaining();
        assert!(buf.is_empty());

        match parse_result {
            Ok(result) => {
                match result {
                    Script::Custom(t) => {
                        if let Some(_foo) = t.downcast_ref::<Foo>() {
                            assert!(true);
                        } else {
                            assert!(false);
                        }
                    }
                    _ => assert!(false),
                }
            }
            Err(_) => {
                assert!(false);
            }
        }

    }

}

// ScriptBody

pub struct ScriptBody(StatementList);

// TODO: test
pub fn script_body<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ScriptBody> {
    // TODO: move this somewhere else
    let params = Parameters::new();
    statement_list(i, &params).map(ScriptBody)
}
