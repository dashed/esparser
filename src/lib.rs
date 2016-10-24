#![feature(unicode)]
// == crates ==
#[macro_use]
extern crate chomp;
extern crate unicode_xid;

// == 3rd-party imports ==

use chomp::parsers::{SimpleResult, scan, token, any, take_till, string, satisfy};
use chomp::combinators::{look_ahead, many_till, many1, or};
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

 */

// == parser helpers ==

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

    match parse_only(unicode_id_start, b"1") {
        Ok(_) => {
            assert!(false);
        }
        Err(_) => {
            assert!(true);
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
}

// == 11.8.3 Numeric Literals ==

#[inline]
fn is_hex_digit(c: u8) -> bool {
    (b'0' <= c && c <= b'9') ||
    (b'a' <= c && c <= b'f') ||
    (b'A' <= c && c <= b'F')
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-HexDigit
#[inline]
fn hex_digit<I: U8Input>(i: I) -> SimpleResult<I, u8> {
    satisfy(i, is_hex_digit)
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-HexDigits
fn hex_digits<I: U8Input>(i: I) -> SimpleResult<I, i32> {
    or(i,
        |i| parse!{i;

            let digit_1 = hex_digit();
            let digit_2 = hex_digit();

            ret {
                let digit_1 = digit_1 as char;
                let digit_2 = digit_2 as char;
                i32::from_str_radix(&format!("{}{}", digit_1, digit_2), 16).unwrap()
            }
        },
        |i| parse!{i;

            let digit_1 = hex_digit();

            ret {
                let digit_1 = digit_1 as char;
                i32::from_str_radix(&format!("{}", digit_1), 16).unwrap()
            }
        }
    )
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-Hex4Digits
fn hex_4_digits<I: U8Input>(i: I) -> SimpleResult<I, i32> {
    parse!{i;

        let digit_1 = hex_digit();
        let digit_2 = hex_digit();
        let digit_3 = hex_digit();
        let digit_4 = hex_digit();

        ret {
            let digit_1 = digit_1 as char;
            let digit_2 = digit_2 as char;
            let digit_3 = digit_3 as char;
            let digit_4 = digit_4 as char;
            let formatted = format!("{}{}{}{}", digit_1, digit_2, digit_3, digit_4);
            i32::from_str_radix(&formatted, 16).unwrap()
        }
    }
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

    match parse_only(hex_4_digits, b"adad") {
        Ok(result) => {
            assert_eq!(result, 44461);
        }
        Err(_) => {
            assert!(false);
        }
    }
}

// == 11.8.4 String Literals ==


