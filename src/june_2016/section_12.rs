// 3rd-party imports

use chomp::types::{U8Input, Input};
use chomp::prelude::Either;

// local imports

use parsers::{ESParseResult, ESInput, string, parse_utf8_char, on_error, many, many1, string_till,
              token, option, either};
use super::section_11::{reserved_word, identifier_name, IdentifierName};
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

pub struct Initializer;

pub fn initializer<I: U8Input>(i: ESInput<I>,
                               params: &Parameters)
                               -> ESParseResult<I, Initializer> {
    i.ret(Initializer)
}
