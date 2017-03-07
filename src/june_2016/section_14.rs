// rust imports

use std::rc::Rc;
use std::cell::RefCell;

// 3rd-party imports

use chomp::types::{U8Input, Input};
use chomp::prelude::Either;

// local imports

use super::types::{Parameters, Parameter};
use super::section_11::{common_delim, common_delim_required, CommonDelim, SemiColon, semicolon};
use super::section_12::{initializer, Initializer, binding_identifier, BindingIdentifier,
                        PropertyName, property_name};
use super::section_13::{statement_list, StatementList, binding_element, BindingElement,
                        binding_rest_element, BindingRestElement};
use parsers::{ESInput, ESParseResult, parse_list, token, option, string, on_error, either, or};
use parsers::error_location::ErrorLocation;

// 14 ECMAScript Language: Functions and Classes
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-functions-and-classes

// 14.1 Function Definitions

// FunctionDeclaration

enum FunctionDeclaration {
    NamedFunction(/* function */
                  Vec<CommonDelim>,
                  BindingIdentifier,
                  Vec<CommonDelim>,
                  /* ( */
                  Vec<CommonDelim>,
                  FormalParameters,
                  Vec<CommonDelim>,
                  /* ) */
                  Vec<CommonDelim>,
                  /* { */
                  Vec<CommonDelim>,
                  FunctionBody,
                  Vec<CommonDelim> /* } */),

    AnonymousFunction(/* function */
                      Vec<CommonDelim>,
                      /* ( */
                      Vec<CommonDelim>,
                      FormalParameters,
                      Vec<CommonDelim>,
                      /* ) */
                      Vec<CommonDelim>,
                      /* { */
                      Vec<CommonDelim>,
                      FunctionBody,
                      Vec<CommonDelim> /* } */),
}

// TODO: test
fn function_declaration<I: U8Input>(i: ESInput<I>,
                                    params: &Parameters)
                                    -> ESParseResult<I, FunctionDeclaration> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield) ||
             params.contains(&Parameter::Default)) {
            panic!("misuse of function_declaration");
        }
    }

    #[inline]
    fn function_name<I: U8Input>
        (i: ESInput<I>,
         params: &Parameters)
         -> ESParseResult<I, Option<(Vec<CommonDelim>, BindingIdentifier)>> {

        if params.contains(&Parameter::Default) {

            option(i,
                   |i| {
                parse!{i;

                        let delim = common_delim_required();
                        let ident = binding_identifier(&params);

                        ret {
                            Some((delim, ident))
                        }
                    }
            },
                   None)

        } else {
            parse!{i;

                let delim = common_delim_required();
                let ident = binding_identifier(&params);


                ret {
                    Some((delim, ident))
                }
            }
        }

    }

    type ReturnType = (/* function */
                       Option<(Vec<CommonDelim>, BindingIdentifier)>,
                       Vec<CommonDelim>,
                       /* ( */
                       Vec<CommonDelim>,
                       FormalParameters,
                       Vec<CommonDelim>,
                       /* ) */
                       Vec<CommonDelim>,
                       /* { */
                       Vec<CommonDelim>,
                       FunctionBody,
                       Vec<CommonDelim> /* } */);

    let foo: ESParseResult<I, ReturnType> = parse!{i;

        string(b"function");

        let name = function_name(&params);

        let delim_2 = common_delim();
        token(b'(');

        let delim_3 = common_delim();

        let formal_params = formal_parameters(&params);

        let delim_4 = common_delim();

        token(b')');

        let delim_5 = common_delim();

        token(b'{');

        let delim_6 = common_delim();

        let body = function_body(&params);

        let delim_7 = common_delim();

        token(b'}');

        ret {
            (name, delim_2, delim_3, formal_params, delim_4, delim_5, delim_6, body, delim_7)
        }
    };

    foo.bind(|i, result| {

        let (name, delim_2, delim_3, formal_params, delim_4, delim_5, delim_6, body, delim_7) =
            result;

        let result = match name {
            Some((delim_1, ident)) => {
                FunctionDeclaration::NamedFunction(delim_1,
                                                   ident,
                                                   delim_2,
                                                   delim_3,
                                                   formal_params,
                                                   delim_4,
                                                   delim_5,
                                                   delim_6,
                                                   body,
                                                   delim_7)
            }
            None => {
                FunctionDeclaration::AnonymousFunction(delim_2,
                                                       delim_3,
                                                       formal_params,
                                                       delim_4,
                                                       delim_5,
                                                       delim_6,
                                                       body,
                                                       delim_7)
            }
        };

        i.ret(result)
    })

}

// FunctionExpression

pub enum FunctionExpression {
    NamedFunction(/* function */
                  Vec<CommonDelim>,
                  BindingIdentifier,
                  Vec<CommonDelim>,
                  /* ( */
                  Vec<CommonDelim>,
                  FormalParameters,
                  Vec<CommonDelim>,
                  /* ) */
                  Vec<CommonDelim>,
                  /* { */
                  Vec<CommonDelim>,
                  FunctionBody,
                  Vec<CommonDelim> /* } */),

    AnonymousFunction(/* function */
                      Vec<CommonDelim>,
                      /* ( */
                      Vec<CommonDelim>,
                      FormalParameters,
                      Vec<CommonDelim>,
                      /* ) */
                      Vec<CommonDelim>,
                      /* { */
                      Vec<CommonDelim>,
                      FunctionBody,
                      Vec<CommonDelim> /* } */),
}

// TODO: test
pub fn function_expression<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, FunctionExpression> {

    // this is intentionally empty
    let params = Parameters::new();

    type ReturnType = (/* function */
                       Option<(Vec<CommonDelim>, BindingIdentifier)>,
                       Vec<CommonDelim>,
                       /* ( */
                       Vec<CommonDelim>,
                       FormalParameters,
                       Vec<CommonDelim>,
                       /* ) */
                       Vec<CommonDelim>,
                       /* { */
                       Vec<CommonDelim>,
                       FunctionBody,
                       Vec<CommonDelim> /* } */);

    let foo: ESParseResult<I, ReturnType> = parse!{i;

        string(b"function");

        let fn_name = option(|i| -> ESParseResult<I, Option<(Vec<CommonDelim>, BindingIdentifier)>> {
            parse!{i;

                let delim = common_delim_required();
                let ident = binding_identifier(&params);

                ret {
                    Some((delim, ident))
                }
            }
        },
        None);

        let delim_2 = common_delim();
        token(b'(');

        let delim_3 = common_delim();

        let formal_params = formal_parameters(&params);

        let delim_4 = common_delim();

        token(b')');

        let delim_5 = common_delim();

        token(b'{');

        let delim_6 = common_delim();

        let body = function_body(&params);

        let delim_7 = common_delim();

        token(b'}');

        ret {
            (fn_name, delim_2, delim_3, formal_params, delim_4, delim_5, delim_6, body, delim_7)
        }

    };

    foo.bind(|i, result| {

        let (fn_name, delim_2, delim_3, formal_params, delim_4, delim_5, delim_6, body, delim_7) =
            result;

        let result = match fn_name {
            Some((delim_1, ident)) => {
                FunctionExpression::NamedFunction(delim_1,
                                                  ident,
                                                  delim_2,
                                                  delim_3,
                                                  formal_params,
                                                  delim_4,
                                                  delim_5,
                                                  delim_6,
                                                  body,
                                                  delim_7)
            }
            None => {
                FunctionExpression::AnonymousFunction(delim_2,
                                                      delim_3,
                                                      formal_params,
                                                      delim_4,
                                                      delim_5,
                                                      delim_6,
                                                      body,
                                                      delim_7)
            }
        };

        i.ret(result)
    })

}

// StrictFormalParameters

struct StrictFormalParameters(FormalParameterList);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-StrictFormalParameters
fn strict_formal_parameters<I: U8Input>(i: ESInput<I>,
                                        params: &Parameters)
                                        -> ESParseResult<I, StrictFormalParameters> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of strict_formal_parameters");
        }
    }

    formal_parameter_list(i, params).map(StrictFormalParameters)
}

// FormalParameters

enum FormalParameters {
    Empty,
    FormalParameterList(FormalParameterList),
}

// TODO: test
fn formal_parameters<I: U8Input>(i: ESInput<I>,
                                 params: &Parameters)
                                 -> ESParseResult<I, FormalParameters> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of formal_parameters");
        }
    }

    option(i,
           |i| formal_parameter_list(i, params).map(FormalParameters::FormalParameterList),
           FormalParameters::Empty)
}

// FormalParameterList

enum FormalParameterList {
    FunctionRestParameter(FunctionRestParameter),
    FormalsList(FormalsList),
    FormalsListWithRest(FormalsList,
                        Vec<CommonDelim>,
                        /* comma */
                        Vec<CommonDelim>,
                        FunctionRestParameter),
}

// TODO: test
fn formal_parameter_list<I: U8Input>(i: ESInput<I>,
                                     params: &Parameters)
                                     -> ESParseResult<I, FormalParameterList> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of formal_parameter_list");
        }
    }

    or(i,
       |i| function_rest_parameter(i, &params).map(FormalParameterList::FunctionRestParameter),
       |i| {
        parse!{i;

            let list = formals_list(&params);

            let rest = option(|i| -> ESParseResult<I, Option<(Vec<CommonDelim>, Vec<CommonDelim>, FunctionRestParameter)>> {parse!{i;

                let delim_1 = common_delim();

                token(b',');

                let delim_2 = common_delim();

                let rest = function_rest_parameter(&params);

                ret {

                    Some((delim_1, delim_2, rest))
                }

            }}, None);

            ret {

                match rest {
                    None => FormalParameterList::FormalsList(list),
                    Some((delim_1, delim_2, rest)) => {
                        FormalParameterList::FormalsListWithRest(list, delim_1, delim_2, rest)
                    }
                }
            }
        }
    })
}

// FormalsList

struct FormalsList(FormalParameter, Vec<FormalsListRest>);

impl FormalsList {
    fn new(rhs_val: FormalParameter) -> Self {
        FormalsList(rhs_val, vec![])
    }

    fn add_item(self, operator_delim: FormalsListDelim, rhs_val: FormalParameter) -> Self {

        let FormalsList(head, rest) = self;
        let mut rest = rest;

        let FormalsListDelim(delim_1, delim_2) = operator_delim;

        let rhs = FormalsListRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        FormalsList(head, rest)
    }
}

struct FormalsListRest(Vec<CommonDelim>,
                       /* , (comma) */
                       Vec<CommonDelim>,
                       FormalParameter);

struct FormalsListDelim(Vec<CommonDelim>,
                        /* , (comma) */
                        Vec<CommonDelim>);

generate_list_parser!(
    FormalsList;
    FormalsListRest;
    FormalsListState;
    FormalsListDelim;
    FormalParameter);

// TODO: test
fn formals_list<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, FormalsList> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of formals_list");
        }
    }

    type Accumulator = Rc<RefCell<FormalsListState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            (i -> {
                on_error(
                    token(i, b','),
                    |i| {
                        let loc = i.position();
                        // TODO: proper err message?
                        ErrorLocation::new(loc, "Expected , here.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();

            ret {
                let delim = FormalsListDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        formal_parameter(i, &params).bind(|i, rhs| {
            accumulator.borrow_mut().add_item(rhs);
            i.ret(())
        })
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// FunctionRestParameter

struct FunctionRestParameter(BindingRestElement);

// TODO: test
fn function_rest_parameter<I: U8Input>(i: ESInput<I>,
                                       params: &Parameters)
                                       -> ESParseResult<I, FunctionRestParameter> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of function_rest_parameter");
        }
    }

    binding_rest_element(i, params).map(FunctionRestParameter)
}

// FormalParameter

struct FormalParameter(BindingElement);

// TODO: test
fn formal_parameter<I: U8Input>(i: ESInput<I>,
                                params: &Parameters)
                                -> ESParseResult<I, FormalParameter> {
    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of formal_parameter");
        }
    }

    binding_element(i, params).map(FormalParameter)
}

// FunctionBody

struct FunctionBody(FunctionStatementList);

// TODO: test
fn function_body<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, FunctionBody> {
    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of function_body");
        }
    }

    function_statement_list(i, params).map(FunctionBody)
}

// FunctionStatementList

struct FunctionStatementList(Option<StatementList>);

// TODO: test
fn function_statement_list<I: U8Input>(i: ESInput<I>,
                                       params: &Parameters)
                                       -> ESParseResult<I, FunctionStatementList> {
    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of function_statement_list");
        }
    }

    let mut params = params.clone();
    params.insert(Parameter::Return);

    option(i, |i| statement_list(i, &params).map(Some), None).map(FunctionStatementList)
}

// 14.3 Method Definitions

// MethodDefinition

pub enum MethodDefinition {
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
pub fn method_definition<I: U8Input>(i: ESInput<I>,
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

    formal_parameter(i, &params).map(PropertySetParameterList)
}

// 14.4 Generator Function Definitions

// GeneratorMethod

struct GeneratorMethod(Vec<CommonDelim>,
                       PropertyName,
                       Vec<CommonDelim>,
                       Vec<CommonDelim>,
                       StrictFormalParameters,
                       Vec<CommonDelim>,
                       Vec<CommonDelim>,
                       Vec<CommonDelim>,
                       GeneratorBody,
                       Vec<CommonDelim>);

// TODO: test
fn generator_method<I: U8Input>(i: ESInput<I>,
                                params: &Parameters)
                                -> ESParseResult<I, GeneratorMethod> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of generator_method");
        }
    }

    parse!{i;

        token(b'*');

        let delim_1 = common_delim();

        let name = property_name(&params);

        let delim_2 = common_delim();
        token(b'(');
        let delim_3 = common_delim();

        let formal_params = strict_formal_parameters(&params);

        let delim_4 = common_delim();
        token(b'(');
        let delim_5 = common_delim();

        token(b'{');
        let delim_6 = common_delim();

        let body = generator_body();

        let delim_7 = common_delim();
        token(b'}');

        ret GeneratorMethod(delim_1, name, delim_2, delim_3, formal_params, delim_4, delim_5, delim_6, body, delim_7)
    }

}


// TODO: http://www.ecma-international.org/ecma-262/7.0/#prod-GeneratorDeclaration

// TODO: http://www.ecma-international.org/ecma-262/7.0/#prod-GeneratorExpression

// GeneratorBody

struct GeneratorBody(FunctionBody);

// TODO: test
fn generator_body<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, GeneratorBody> {

    let mut params = Parameters::new();
    params.insert(Parameter::Yield);

    function_body(i, &params).map(GeneratorBody)
}
