// 3rd-party imports

use chomp::types::{U8Input, Input};
use chomp::prelude::Either;

// local imports

use parsers::{ESParseResult, ESInput, string, parse_utf8_char, on_error, many, many1, string_till,
              token, option, either};
use super::section_11::{reserved_word, identifier_name, IdentifierName, CommonDelim, common_delim,
                        string_literal, StringLiteral, numeric_literal, NumericLiteral};
use super::types::{Parameters, Parameter};
use parsers::error_location::ErrorLocation;

// 12 ECMAScript Language: Expressions
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-expressions

// 12.1 Identifiers

// TODO: move this somewhere
#[inline]
fn yield_keyword<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, I::Buffer> {
    on_error(string(i, b"yield"), |i| {
        let reason = format!("Expected yield keyword.");
        ErrorLocation::new(i.position(), reason)
    })
}

// IdentifierReference

enum IdentifierReference {
    Identifier(Identifier),
    Yield,
}

// TODO: test
fn identifier_reference<I: U8Input>(i: ESInput<I>,
                                    params: &Parameters)
                                    -> ESParseResult<I, IdentifierReference> {

    if !params.contains(&Parameter::Yield) {

        let result = either(i,
                            // left
                            yield_keyword,
                            // right
                            identifier)
            .bind(|i, result| {
                match result {
                    Either::Left(_) => i.ret(IdentifierReference::Yield),
                    Either::Right(ident) => i.ret(IdentifierReference::Identifier(ident)),
                }
            });

        return result;
    }

    if is_debug_mode!() {
        if params.len() >= 2 {
            panic!("misuse of identifier_reference");
        }
    }

    identifier(i).map(|ident| IdentifierReference::Identifier(ident))

}

// BindingIdentifier

pub enum BindingIdentifier {
    Identifier(Identifier),
    Yield,
}

// TODO: test
pub fn binding_identifier<I: U8Input>(i: ESInput<I>,
                                      params: &Parameters)
                                      -> ESParseResult<I, BindingIdentifier> {

    if !params.contains(&Parameter::Yield) {

        let result = either(i,
                            // left
                            yield_keyword,
                            // right
                            identifier)
            .bind(|i, result| {
                match result {
                    Either::Left(_) => i.ret(BindingIdentifier::Yield),
                    Either::Right(ident) => i.ret(BindingIdentifier::Identifier(ident)),
                }
            });

        return result;
    }

    if is_debug_mode!() {
        // validation
        if params.len() >= 2 {
            panic!("misuse of binding_identifier");
        }
    }

    identifier(i).map(BindingIdentifier::Identifier)

}

// LabelIdentifier

enum LabelIdentifier {
    Identifier(Identifier),
    Yield,
}

// TODO: test
fn label_identifier<I: U8Input>(i: ESInput<I>,
                                params: &Parameters)
                                -> ESParseResult<I, LabelIdentifier> {

    if !params.contains(&Parameter::Yield) {

        let result = either(i,
                            // left
                            yield_keyword,
                            // right
                            identifier)
            .bind(|i, result| {
                match result {
                    Either::Left(_) => i.ret(LabelIdentifier::Yield),
                    Either::Right(ident) => i.ret(LabelIdentifier::Identifier(ident)),
                }
            });

        return result;
    }

    if params.len() >= 2 {
        panic!("misuse of binding_identifier");
    }

    identifier(i).map(|ident| LabelIdentifier::Identifier(ident))

}

// Identifier

struct Identifier(IdentifierName);

// TODO: test
fn identifier<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Identifier> {
    either(i,
           |i| reserved_word(i), // left
           |i| identifier_name(i) /* right */)
        .bind(|i, result| {
            match result {
                Either::Left(_) => {
                    let loc = i.position();
                    let reason = format!("Reserved keyword may not be used as an identifier.");
                    i.err(ErrorLocation::new(loc, reason).into())
                }
                Either::Right(name) => i.ret(Identifier(name)),
            }
        })
}

// 12.2.6 Object Initializer

// PropertyName

pub enum PropertyName {
    LiteralPropertyName(LiteralPropertyName),
    ComputedPropertyName(ComputedPropertyName),
}

// TODO: test
pub fn property_name<I: U8Input>(i: ESInput<I>,
                                 params: &Parameters)
                                 -> ESParseResult<I, PropertyName> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of property_name");
        }
    }

    parse!{i;

        let prop_name = (i -> literal_property_name(i).map(PropertyName::LiteralPropertyName))
        <|>
        (i -> computed_property_name(i, &params).map(PropertyName::ComputedPropertyName));

        ret prop_name
    }
}

// LiteralPropertyName

enum LiteralPropertyName {
    IdentifierName(IdentifierName),
    StringLiteral(StringLiteral),
    NumericLiteral(NumericLiteral),
}

// TODO: test
fn literal_property_name<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, LiteralPropertyName> {
    parse!{i;

        let literal_prop_name =
            (i -> identifier_name(i).map(LiteralPropertyName::IdentifierName))
            <|>
            (i -> string_literal(i).map(LiteralPropertyName::StringLiteral))
            <|>
            (i -> numeric_literal(i).map(LiteralPropertyName::NumericLiteral));

        ret literal_prop_name
    }
}

// ComputedPropertyName

struct ComputedPropertyName(/* [ */
                            Vec<CommonDelim>,
                            AssignmentExpression,
                            Vec<CommonDelim> /* ] */);

// TODO: test
fn computed_property_name<I: U8Input>(i: ESInput<I>,
                                      params: &Parameters)
                                      -> ESParseResult<I, ComputedPropertyName> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of computed_property_name");
        }
    }

    let mut params = params.clone();
    params.insert(Parameter::In);
    let params = params;

    parse!{i;

        token(b'[');
        let delim_left = common_delim();

        let expr = assignment_expression(&params);

        let delim_right = common_delim();
        token(b']');

        ret ComputedPropertyName(delim_left, expr, delim_right)
    }
}

// CoverInitializedName

struct CoverInitializedName(IdentifierReference, Vec<CommonDelim>, Initializer);

// TODO: test
fn cover_initialized_name<I: U8Input>(i: ESInput<I>,
                                      params: &Parameters)
                                      -> ESParseResult<I, CoverInitializedName> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of cover_initialized_name");
        }
    }

    parse!{i;

        let id_ref = identifier_reference(&params);

        let delim = common_delim();

        let initializer = (i -> {

            let mut params = params.clone();
            params.insert(Parameter::In);

            initializer(i, &params)
        });

        ret CoverInitializedName(id_ref, delim, initializer)
    }
}

// Initializer

pub struct Initializer(/* = */
                       Vec<CommonDelim>,
                       AssignmentExpression);

// TODO: test
pub fn initializer<I: U8Input>(i: ESInput<I>,
                               params: &Parameters)
                               -> ESParseResult<I, Initializer> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::In) ||
             params.contains(&Parameter::Yield)) {
            panic!("misuse of initializer");
        }
    }

    parse!{i;

        token(b'=');

        let delim = common_delim();

        let expr = assignment_expression(params);

        ret Initializer(delim, expr)
    }
}

// 12.15 Assignment Operators

// AssignmentExpression

struct AssignmentExpression;
// TODO: fix
// enum AssignmentExpression {
//     ConditionalExpression(Box<ConditionalExpression>),
// }

// TODO: test
fn assignment_expression<I: U8Input>(i: ESInput<I>,
                                     params: &Parameters)
                                     -> ESParseResult<I, AssignmentExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::In) ||
             params.contains(&Parameter::Yield)) {
            panic!("misuse of assignment_expression");
        }
    }

    i.ret(AssignmentExpression)
    // TODO: fix
    // parse!{i;

    //     let result = (i -> conditional_expression(i, params)
    //         .map(|x| AssignmentExpression::ConditionalExpression(Box::new(x))));

    //     // TODO: complete

    //     ret {
    //         result
    //     }
    // }
}
