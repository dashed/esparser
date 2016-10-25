#![recursion_limit="1000"]
#![feature(unicode)]
// == crates ==
#[macro_use]
extern crate chomp;
extern crate unicode_xid;

// == 3rd-party imports ==

use chomp::parsers::{SimpleResult, scan, token, any, take_till, string, satisfy};
use chomp::combinators::{look_ahead, many_till, many1, many, or};
use chomp::types::{Buffer, Input, ParseResult, U8Input};
use chomp::parse_only;
use chomp::parsers::Error as ChompError;
use chomp::primitives::Primitives;

/*

Reference:
http://www.ecma-international.org/ecma-262/7.0

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
fn parse_utf8_char_of_bytes<I: U8Input>(mut i: I, needle: &[u8]) -> SimpleResult<I, char> {
    parse!{i;
        look_ahead(|i| string(i, needle));
        let c = parse_utf8_char();
        ret c
    }
}

#[inline]
fn parse_utf8_char<I: U8Input>(mut i: I) -> SimpleResult<I, char> {

    let mut internal_buf = vec![];
    let mut valid = false;

    let mut result = "".to_string();

    let _b = i.consume_while(|c| {
        if valid || internal_buf.len() >= 4 {
            false // break from while
        } else {

            internal_buf.push(c);

            match std::str::from_utf8(&internal_buf) {
                Err(_) => {
                    // not valid
                },
                Ok(__result) => {
                    result = __result.to_string();
                    valid = true;
                }
            }

            true // continue while
        }
    });

    if valid && internal_buf.len() <= 4 && result.len() >= 1 {
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

    let fails = vec![b"1", b" ", b"\t"];

    for case_fail in fails {
        match parse_only(unicode_id_start, case_fail) {
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

    match parse_only(unicode_id_continue, b"a") {
        Ok(result) => {
            assert_eq!(result, 'a');
        }
        Err(_) => {
            assert!(false);
        }
    }

    match parse_only(unicode_id_continue, b"1") {
        Ok(result) => {
            assert_eq!(result, '1');
        }
        Err(_) => {
            assert!(false);
        }
    }

    let fails = vec![b" ", b"\t"];

    for case_fail in fails {
        match parse_only(unicode_id_start, case_fail) {
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


// == 13.3.2 Variable Statement ==
//
// http://www.ecma-international.org/ecma-262/7.0/#prod-VariableStatement
