// 3rd-party imports

use chomp::types::{U8Input, Input};
use chomp::prelude::Either;

// local imports

use super::types::{Parameters, Parameter};
use super::section_11::{common_delim, common_delim_required, CommonDelim, SemiColon, semicolon};
use super::section_12::{initializer, Initializer, binding_identifier, BindingIdentifier,
                        PropertyName, property_name};
use parsers::{ESInput, ESParseResult, parse_list, token, option, string, on_error, either};
use parsers::error_location::ErrorLocation;

// 14 ECMAScript Language: Functions and Classes
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-functions-and-classes

// 14.3 Method Definitions

// MethodDefinition

enum MethodDefinition {
    Method(PropertyName,
           Vec<CommonDelim>,
           Vec<CommonDelim>,
           StrictFormalParameters,
           Vec<CommonDelim>,
           Vec<CommonDelim>,
           Vec<CommonDelim>,
           FunctionBody,
           Vec<CommonDelim>),

    GeneratorMethod(GeneratorMethod),

    Get(Vec<CommonDelim>,
        PropertyName,
        Vec<CommonDelim>,
        Vec<CommonDelim>,
        Vec<CommonDelim>,
        Vec<CommonDelim>,
        FunctionBody,
        Vec<CommonDelim>),

    Set(Vec<CommonDelim>,
        PropertyName,
        Vec<CommonDelim>,
        Vec<CommonDelim>,
        PropertySetParameterList,
        Vec<CommonDelim>,
        Vec<CommonDelim>,
        Vec<CommonDelim>,
        FunctionBody,
        Vec<CommonDelim>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-MethodDefinition
fn method_definition<I: U8Input>(i: ESInput<I>,
                                 params: &Parameters)
                                 -> ESParseResult<I, MethodDefinition> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of method_definition");
        }

    }

    #[inline]
    fn method_definition<I: U8Input>(i: ESInput<I>,
                                     params: &Parameters)
                                     -> ESParseResult<I, MethodDefinition> {

        parse!{i;

            let prop_name = property_name(&params);

            let delim_1 = common_delim();
            token(b'(');
            let delim_2 = common_delim();

            let formal_params = strict_formal_parameters(&params);

            let delim_3 = common_delim();
            token(b')');
            let delim_4 = common_delim();
            token(b'{');
            let delim_5 = common_delim();

            let body = function_body(&params);

            let delim_6 = common_delim();
            token(b'}');

            ret MethodDefinition::Method(prop_name, delim_1, delim_2, formal_params, delim_3, delim_4, delim_5, body, delim_6)
        }

    }

    #[inline]
    fn method_definition_get<I: U8Input>(i: ESInput<I>,
                                         params: &Parameters)
                                         -> ESParseResult<I, MethodDefinition> {
        parse!{i;

            (i -> {
                on_error(
                    string(i, b"get"),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected 'get' keyword.".to_string())
                    }
                )
            });



            let delim_1 = common_delim_required();
            let prop_name = property_name(&params);
            let delim_2 = common_delim();

            token(b'(');
            let delim_3 = common_delim();
            token(b')');

            let delim_4 = common_delim();
            token(b'{');
            let delim_5 = common_delim();

            let body = function_body(&params);

            let delim_6 = common_delim();
            token(b'}');

            ret MethodDefinition::Get(delim_1, prop_name, delim_2, delim_3, delim_4, delim_5, body, delim_6)
        }
    }

    #[inline]
    fn method_definition_set<I: U8Input>(i: ESInput<I>,
                                         params: &Parameters)
                                         -> ESParseResult<I, MethodDefinition> {
        parse!{i;

            (i -> {
                on_error(
                    string(i, b"set"),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected 'set' keyword.".to_string())
                    }
                )
            });

            let delim_1 = common_delim_required();
            let prop_name = property_name(&params);
            let delim_2 = common_delim();

            token(b'(');
            let delim_3 = common_delim();

            let list = property_set_parameter_list();

            let delim_4 = common_delim();
            token(b')');

            let delim_5 = common_delim();
            token(b'{');
            let delim_6 = common_delim();

            let body = function_body(&params);

            let delim_7 = common_delim();
            token(b'}');

            ret MethodDefinition::Set(delim_1, prop_name, delim_2, delim_3, list, delim_4, delim_5, delim_6, body, delim_7)
        }
    }

    parse!{i;

        let result =
            method_definition(&params) <|>
            (i -> generator_method(i, &params).map(|x| MethodDefinition::GeneratorMethod(x))) <|>
            method_definition_get(&params) <|>
            method_definition_set(&params);

        ret result
    }
}

// PropertySetParameterList

struct PropertySetParameterList(FormalParameter);

// TODO: test
fn property_set_parameter_list<I: U8Input>(i: ESInput<I>)
                                           -> ESParseResult<I, PropertySetParameterList> {

    let params = Parameters::new();

    formal_parameter(i, params).map(PropertySetParameterList)
}
