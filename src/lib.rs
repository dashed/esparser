#![recursion_limit="1000"]
#![feature(unicode)]
// == crates ==
#[macro_use]
extern crate chomp;
// TODO: remove
// extern crate unicode_xid;

// == 3rd-party imports ==

use chomp::parsers::{SimpleResult, scan, token, any, take_till, string, satisfy};
use chomp::combinators::{look_ahead, many_till, many1, many, or, either};
use chomp::types::{Buffer, Input, ParseResult, U8Input};
use chomp::parse_only;
use chomp::parsers::Error as ChompError;
use chomp::primitives::Primitives;
use chomp::prelude::{Either};

/*

Reference:
- http://www.ecma-international.org/ecma-262/7.0
- http://www.ecma-international.org/ecma-262/7.0/#sec-grammar-notation

Start:
http://www.ecma-international.org/ecma-262/7.0/#sec-types-of-source-code


http://www.ecma-international.org/ecma-262/7.0/#sec-lexical-and-regexp-grammars

Bookmark:
- http://www.ecma-international.org/ecma-262/7.0/#prod-VariableStatement

 */

// == parser helpers ==

#[inline]
fn string_to_unicode_char(s: &str) -> Option<char> {
    u32::from_str_radix(s, 16)
        .ok()
        .and_then(std::char::from_u32)
}

#[inline]
fn token_as_char<I: U8Input>(i: I, c: u8) -> SimpleResult<I, char> {
    parse!{i;
        let i = token(c);
        ret {
            i as char
        }
    }
}

// TODO: test
#[inline]
fn parse_utf8_char_of_bytes<I: U8Input>(i: I, needle: &[u8]) -> SimpleResult<I, char> {
    parse!{i;
        look_ahead(|i| string(i, needle));
        let c = parse_utf8_char();
        ret c
    }
}

#[inline]
fn parse_utf8_char<I: U8Input>(mut i: I) -> SimpleResult<I, char> {

    let mut internal_buf = vec![];
    let mut valid_utf8 = false;

    let mut result = "".to_string();

    let _b = i.consume_while(|c| {
        if valid_utf8 || internal_buf.len() >= 4 {
            false // break from consume_while
        } else {

            internal_buf.push(c);

            match std::str::from_utf8(&internal_buf) {
                Err(_) => {
                    // not valid_utf8
                },
                Ok(__result) => {
                    result = __result.to_string();
                    valid_utf8 = true;
                }
            }

            true // continue consume_while
        }
    });

    if valid_utf8 && internal_buf.len() <= 4 && result.len() >= 1 {
        return i.ret(result.chars().next().unwrap());
    }

    return i.err(ChompError::unexpected());

}

#[test]
fn parse_utf8_char_test() {

    let sparkle_heart = vec![240, 159, 146, 150];

    match parse_only(parse_utf8_char, &sparkle_heart) {
        Ok(result) => {
            assert_eq!(result, '\u{1f496}');
        }
        Err(_) => {
            assert!(false);
        }
    }

    // case: only one sparkle heart is parsed

    let two_sparkle_hearts = vec![240, 159, 146, 150, 240, 159, 146, 150];

    match parse_only(parse_utf8_char, &two_sparkle_hearts) {
        Ok(result) => {
            assert_eq!(result, '\u{1f496}');
        }
        Err(_) => {
            assert!(false);
        }
    }
}

// == Tokens ==
enum Token {
    WhiteSpace
}

// Since there is no separate lexing step apart from parsing step,
// common_delim() is used where appropriate.
//
// The appropriate delimeters are derived from the 'goal symbols':
// - InputElementDiv
// - InputElementRegExp
// - InputElementRegExpOrTemplateTail
// - InputElementTemplateTail
//
// as defined in: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-lexical-grammar
fn common_delim<I: U8Input>(i: I) -> SimpleResult<I, Vec<Token>> {

    #[inline]
    fn __common_delim<I: U8Input>(i: I) -> SimpleResult<I, Token> {
        parse!{i;
            let delim: Token = whitespace();
            ret delim
        }
    }

    parse!{i;
        let delims: Vec<Token> = many(__common_delim);
        ret delims
    }
}


// == Parameters ==
// Based on: http://www.ecma-international.org/ecma-262/7.0/#sec-grammar-notation
enum Parameter {
    In,
    Yield,
    Return
}

// == 11.2 White Space ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-white-space

// http://www.ecma-international.org/ecma-262/7.0/#prod-WhiteSpace
fn whitespace<I: U8Input>(i: I) -> SimpleResult<I, Token> {

    #[inline]
    fn other_whitespace<I: U8Input>(i: I) -> SimpleResult<I, char> {
        parse_utf8_char(i)
            .bind(|i, c: char| {
                if c.is_whitespace() {
                    i.ret(c)
                } else {
                    i.err(ChompError::unexpected())
                }
            })
    }

    parse!{i;

        let _result =
            parse_utf8_char_of_bytes(b"\x0009") <|> // <TAB>; CHARACTER TABULATION
            parse_utf8_char_of_bytes(b"\x000B") <|> // <VT>; LINE TABULATION
            parse_utf8_char_of_bytes(b"\x000C") <|> // <FF>; FORM FEED (FF)
            parse_utf8_char_of_bytes(b"\x0020") <|> // <SP>; SPACE
            parse_utf8_char_of_bytes(b"\x00A0") <|> // <NBSP>; NO-BREAK SPACE
            parse_utf8_char_of_bytes(b"\xFEFF") <|> // <ZWNBSP>; ZERO WIDTH NO-BREAK SPACE
            other_whitespace(); // Any other Unicode "Separator, space" code point

        ret {Token::WhiteSpace}
    }
}

// == 11.6 Names and Keywords ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-names-and-keywords

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierName
fn identifier_name<I: U8Input>(i: I) -> SimpleResult<I, ()> {
    parse!{i;

        let _l: Vec<char> = many1(identifier_start);
        let _ll: Vec<char> = many(identifier_part);

        ret {()}
    }
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierStart
fn identifier_start<I: U8Input>(i: I) -> SimpleResult<I, char> {

    #[inline]
    fn identifier_start_unicode<I: U8Input>(i: I) -> SimpleResult<I, char> {
        parse!{i;
            token(b'\\');
            let sequence = unicode_escape_seq();
            ret sequence
        }
    }

    parse!{i;

        let start = unicode_id_start() <|>
        token_as_char(b'$') <|>
        token_as_char(b'_') <|>
        identifier_start_unicode();

        ret start
    }
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierPart
fn identifier_part<I: U8Input>(i: I) -> SimpleResult<I, char> {

    #[inline]
    fn identifier_part_unicode<I: U8Input>(i: I) -> SimpleResult<I, char> {
        parse!{i;
            token(b'\\');
            let sequence = unicode_escape_seq();
            ret sequence
        }
    }

    parse!{i;

        let part = unicode_id_continue() <|>
        token_as_char(b'$') <|>
        token_as_char(b'_') <|>
        identifier_part_unicode() <|>
        parse_utf8_char_of_bytes(b"\x200C") <|> // <ZWNJ>
        parse_utf8_char_of_bytes(b"\x200D"); // <ZWJ>

        ret part
    }
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-UnicodeIDStart
fn unicode_id_start<I: U8Input>(i: I) -> SimpleResult<I, char> {
    parse_utf8_char(i)
        .bind(|i, c: char| {
            if c.is_xid_start() {
                i.ret(c)
            } else {
                i.err(ChompError::unexpected())
            }
        })
}

#[test]
fn unicode_id_start_test() {

    match parse_only(unicode_id_start, b"a") {
        Ok(result) => {
            assert_eq!(result, 'a');
        }
        Err(_) => {
            assert!(false);
        }
    }

    let fails = vec!["1", " ", "\t", "\n", "\r", ";", "?", "_"];

    for input in fails {
        match parse_only(unicode_id_start, input.as_bytes()) {
            Ok(_) => {
                assert!(false);
            }
            Err(_) => {
                assert!(true);
            }
        }
    }
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-UnicodeIDContinue
fn unicode_id_continue<I: U8Input>(i: I) -> SimpleResult<I, char> {
    parse_utf8_char(i)
        .bind(|i, c: char| {

            if c.is_xid_continue() {
                i.ret(c)
            } else {
                i.err(ChompError::unexpected())
            }

        })
}

#[test]
fn unicode_id_continue_test() {

    let success: Vec<&str> = vec!["a", "1"];

    for input in success {
        match parse_only(unicode_id_continue, input.as_bytes()) {
            Ok(result) => {
                assert_eq!(result, input.chars().next().unwrap());
            }
            Err(_) => {
                assert!(false);
            }
        }
    }

    let fails: Vec<&str> = vec![" ", "\t", "\n", "\r", ";", "?", "_"];

    for input in fails {
        match parse_only(unicode_id_start, input.as_bytes()) {
            Ok(_) => {
                assert!(false);
            }
            Err(_) => {
                assert!(true);
            }
        }
    }
}

// == 11.6.2 Reserved Words

// TODO: enum Keyword type

// TODO: test case: A code point in a ReservedWord cannot be expressed by a \UnicodeEscapeSequence.
// http://www.ecma-international.org/ecma-262/7.0/#sec-reserved-words
fn reserved_word<I: U8Input>(i: I) -> SimpleResult<I, I::Buffer> {
    parse!{i;
        let keyword =
            // == 11.6.2.1 Keywords ==
            // http://www.ecma-international.org/ecma-262/7.0/#prod-Keyword
            string(b"break") <|>
            string(b"do") <|>
            string(b"in") <|>
            string(b"typeof") <|>
            string(b"case") <|>
            string(b"else") <|>
            string(b"instanceof") <|>
            string(b"var") <|>
            string(b"catch") <|>
            string(b"export") <|>
            string(b"new") <|>
            string(b"void") <|>
            string(b"class") <|>
            string(b"extends") <|>
            string(b"return") <|>
            string(b"while") <|>
            string(b"const") <|>
            string(b"finally") <|>
            string(b"super") <|>
            string(b"with") <|>
            string(b"continue") <|>
            string(b"for") <|>
            string(b"switch") <|>
            string(b"yield") <|>
            string(b"debugger") <|>
            string(b"function") <|>
            string(b"this") <|>
            string(b"default") <|>
            string(b"if") <|>
            string(b"throw") <|>
            string(b"delete") <|>
            string(b"import") <|>
            string(b"try") <|>

            // TODO: [edit] remove; replaced by syntax error
            // TODO: is this right?
            // http://www.ecma-international.org/ecma-262/7.0/#sec-keywords
            // string(b"let") <|>
            // string(b"static") <|>

            // == 11.6.2.2 Future Reserved Words ==
            // http://www.ecma-international.org/ecma-262/7.0/#sec-future-reserved-words
            string(b"enum") <|>
            string(b"await") <|>

            // == 11.8.1 Null Literals ==
            // http://www.ecma-international.org/ecma-262/7.0/#prod-NullLiteral
            string(b"null") <|>

            // == 11.8.2 Boolean Literals ==
            // http://www.ecma-international.org/ecma-262/7.0/#prod-BooleanLiteral
            string(b"true") <|>
            string(b"false");

        ret keyword
    }
}

// == 11.8.3 Numeric Literals ==

// http://www.ecma-international.org/ecma-262/7.0/#prod-HexDigit
#[inline]
fn hex_digit<I: U8Input>(i: I) -> SimpleResult<I, u8> {

    #[inline]
    fn is_hex_digit(c: u8) -> bool {
        (b'0' <= c && c <= b'9') ||
        (b'a' <= c && c <= b'f') ||
        (b'A' <= c && c <= b'F')
    }

    satisfy(i, is_hex_digit)
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-HexDigits
fn hex_digits<I: U8Input>(i: I) -> SimpleResult<I, i32> {
    or(i,
        |i| parse!{i;

            let digit_1 = hex_digit();
            let digit_2 = hex_digit();

            ret {
                let mut result = String::with_capacity(2);
                result.push(digit_1 as char);
                result.push(digit_2 as char);
                i32::from_str_radix(&result, 16).unwrap()
            }
        },
        |i| parse!{i;

            let digit_1 = hex_digit();

            ret {
                let mut result = String::with_capacity(1);
                result.push(digit_1 as char);
                i32::from_str_radix(&result, 16).unwrap()
            }
        }
    )
}

#[test]
fn hex_digits_test() {

    match parse_only(hex_digits, b"ad") {
        Ok(result) => {
            assert_eq!(result, 173);
        }
        Err(_) => {
            assert!(false);
        }
    }

    match parse_only(hex_digits, b"e") {
        Ok(result) => {
            assert_eq!(result, 14);
        }
        Err(_) => {
            assert!(false);
        }
    }
}

// == 11.8.4 String Literals ==

// http://www.ecma-international.org/ecma-262/7.0/#prod-UnicodeEscapeSequence
// TODO: needs test
fn unicode_escape_seq<I: U8Input>(i: I) -> SimpleResult<I, char> {
    or(i,
        |i| parse!{i;
            // e.g. u{9A9A}
            token(b'u');
            token(b'{');
            let sequence = hex_4_digits();
            token(b'}');
            ret {
                string_to_unicode_char(&sequence).unwrap()
            }
        },
        |i| parse!{i;
            // e.g. u9A9A
            token(b'u');
            let sequence = hex_4_digits();
            ret {
                string_to_unicode_char(&sequence).unwrap()
            }
        }
    )
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-Hex4Digits
fn hex_4_digits<I: U8Input>(i: I) -> SimpleResult<I, String> {
    parse!{i;

        let digit_1 = hex_digit();
        let digit_2 = hex_digit();
        let digit_3 = hex_digit();
        let digit_4 = hex_digit();

        ret {
            let mut result = String::with_capacity(4);
            result.push(digit_1 as char);
            result.push(digit_2 as char);
            result.push(digit_3 as char);
            result.push(digit_4 as char);
            result
        }
    }
}

#[test]
fn hex_4_digits_test() {
    match parse_only(hex_4_digits, b"adad") {
        Ok(result) => {
            assert_eq!(result, "adad".to_string());
        }
        Err(_) => {
            assert!(false);
        }
    }
}

// == 12.1 Identifiers ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-identifiers

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BindingIdentifier
fn binding_identifier<I: U8Input>(i: I, maybe_params: &Option<Parameter>) -> SimpleResult<I, ()> {

    #[inline]
    fn __binding<I: U8Input>(i: I) -> SimpleResult<I, ()> {
        parse!{i;
            identifier();

            // TODO: token
            ret {()}
        }
    }

    match *maybe_params {
        None => {
            either(i,
                // left
                |i| parse!{i;

                    string(b"yield");

                    // TODO: token
                    ret {()}
                },
                // right
                __binding
            )
            .bind(|i, result| {
                match result {
                    Either::Left(_) => {
                        // TODO: fix
                        i.ret(())
                    },
                    Either::Right(_) => {
                        // TODO: fix
                        i.ret(())
                    }
                }
            })
        },
        Some(ref params) => {
            match *params {
                Parameter::Yield => {},
                _ => {
                    panic!("misuse of binding_identifier");
                }
            }

            __binding(i)
        }
    }


}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Identifier
fn identifier<I: U8Input>(i: I) -> SimpleResult<I, ()> {
    either(i,
        |i| reserved_word(i),  // left
        |i| identifier_name(i) // right
    )
    .bind(|i, result| {
        match result {
            Either::Left(_) => {
                i.err(ChompError::unexpected())
            },
            Either::Right(_) => {
                i.ret(())
            }
        }
    })
}

// == 12.2 Primary Expression ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-primary-expression

// == 12.2.6 Object Initializer ==

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Initializer
fn initializer<I: U8Input>(i: I, params: &Option<Parameter>) -> SimpleResult<I, ()> {

    // validation
    match *params {
        None |
        Some(Parameter::In) |
        Some(Parameter::Yield) => {},
        _ => {
            panic!("misuse of initializer");
        }
    }

    parse!{i;

        token(b'=');

        let delim_1 = common_delim();

        // TODO: assignment_expression(params);

        // TODO: token
        ret {()}
    }
}

// == 12.14 Conditional Operator ( ? : ) ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-conditional-operator

// TODO: test
fn conditional_expression<I: U8Input>(i: I, params: &Option<Parameter>) -> SimpleResult<I, ()> {

    // validation
    match *params {
        None |
        Some(Parameter::In) |
        Some(Parameter::Yield) => {},
        _ => {
            panic!("misuse of conditional_expression");
        }
    }

    either(i,
        // left
        |i| parse!{i;

            logical_or_expression(&params);

            let delim_1 = common_delim();
            token(b'?');
            let delim_2 = common_delim();

            let consequent = assignment_expression(&params);

            let delim_3 = common_delim();
            token(b':');
            let delim_4 = common_delim();

            let alternative = assignment_expression(&params);

            // TODO: token
            ret {()}

        },
        // right
        |i| parse!{i;

            logical_or_expression(&params);

            // TODO: token
            ret {()}
        }
    )
        .bind(|i, result| {
            match result {
                Either::Left(_) => {
                    // TODO: fix
                    i.ret(())
                },
                Either::Right(_) => {
                    // TODO: fix
                    i.ret(())
                }
            }
        })
}

// == 12.13 Binary Logical Operators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-binary-logical-operators

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LogicalORExpression
fn logical_or_expression<I: U8Input>(i: I, params: &Option<Parameter>) -> SimpleResult<I, ()> {

    // validation
    match *params {
        None |
        Some(Parameter::In) |
        Some(Parameter::Yield) => {},
        _ => {
            panic!("misuse of logical_or_expression");
        }
    }

    parse!{i;

        ret {()}
    }

}

// == 12.15 Assignment Operators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-assignment-operators

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-AssignmentExpression
fn assignment_expression<I: U8Input>(i: I, params: &Option<Parameter>) -> SimpleResult<I, ()> {

    // validation
    match *params {
        None |
        Some(Parameter::In) |
        Some(Parameter::Yield) => {},
        _ => {
            panic!("misuse of assignment_expression");
        }
    }

    parse!{i;

        ret {()}
    }
}

// == 13.3.2 Variable Statement ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-variable-statement

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-VariableStatement
fn variable_statement<I: U8Input>(i: I) -> SimpleResult<I, ()> {
    parse!{i;

        let _var = string(b"var");

        let delim_1 = common_delim();

        // TODO: var declaration list
        // sep_by(decimal, |i| token(i, b';'))

        semicolon();

        ret {()}
    }
}


// http://www.ecma-international.org/ecma-262/7.0/#prod-VariableDeclaration
fn variable_declaration<I: U8Input>(i: I, maybe_params: &Option<Parameter>) -> SimpleResult<I, ()> {
    match *maybe_params {
        None => {
            parse!{i;
                // TODO: complete
                ret {()}
            }
        },
        Some(ref params) => {
            parse!{i;
                // TODO: complete
                ret {()}
            }
        }
    }
}

// TODO: test for ASI behaviour
#[inline]
fn semicolon<I: U8Input>(i: I) -> SimpleResult<I, ()> {
    parse!{i;
        // TODO: ASI rule
        token(b';');
        ret {()}
    }
}
