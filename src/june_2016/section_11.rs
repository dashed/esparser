// rust imports

// TODO: remove
// use std::iter::IntoIterator;

// 3rd-party imports

use chomp::types::{U8Input, Input};
use chomp::prelude::Either;

// local imports

use parsers::{ESParseResult, ESInput, string, parse_utf8_char, on_error, many, many1, string_till,
              token, option, satisfy, either};
use parsers::error_location::ErrorLocation;

// 11 ECMAScript Language: Lexical Grammar
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-lexical-grammar

#[derive(Debug)]
pub enum CommonDelim {
    WhiteSpace(WhiteSpace),
    LineTerminator(LineTerminator),
    Comment(Comment),
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
#[inline]
fn __common_delim<I: U8Input>(i: ESInput<I>,
                              parse_line_terminator: bool)
                              -> ESParseResult<I, CommonDelim> {

    if !parse_line_terminator {

        return parse!{i;
            let delim =
                (i -> whitespace(i).map(CommonDelim::WhiteSpace)) <|>
                (i -> comment(i).map(CommonDelim::Comment));
            ret delim
        };

    }

    parse!{i;
        let delim =
            (i -> whitespace(i).map(CommonDelim::WhiteSpace)) <|>
            (i -> line_terminator(i).map(CommonDelim::LineTerminator)) <|>
            (i -> comment(i).map(CommonDelim::Comment));
        ret delim
    }
}

#[inline]
pub fn common_delim<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Vec<CommonDelim>> {
    many(i, |i| __common_delim(i, true))
}

#[inline]
pub fn common_delim_required<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Vec<CommonDelim>> {
    many1(i, |i| __common_delim(i, true))
}

// 11.2 White Space

#[derive(Debug)]
enum WhiteSpace {
    CharacterTabulation,
    LineTabulation,
    FormFeed,
    Space,
    NoBreakSpace,
    ZeroWidthNoBreakSpace,
    // TODO: bound for char to be whitespace?
    OtherWhiteSpace(char),
}

fn whitespace<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, WhiteSpace> {

    #[inline]
    fn other_whitespace<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, WhiteSpace> {
        parse_utf8_char(i).bind(|i, c: char| {
            if c.is_whitespace() {
                i.ret(WhiteSpace::OtherWhiteSpace(c))
            } else {
                let loc = i.position();
                let reason = "Expected whitespace.".to_string();
                i.err(ErrorLocation::new(loc, reason).into())
            }
        })
    }

    let parse_result = parse!{i;

        let whitespace_char =
            (i -> string(i, b"\x0009").map(|_| WhiteSpace::CharacterTabulation)) <|> // <TAB>; CHARACTER TABULATION
            (i -> string(i, b"\x000B").map(|_| WhiteSpace::LineTabulation)) <|> // <VT>; LINE TABULATION
            (i -> string(i, b"\x000C").map(|_| WhiteSpace::FormFeed)) <|> // <FF>; FORM FEED (FF)
            (i -> string(i, b"\x0020").map(|_| WhiteSpace::Space)) <|> // <SP>; SPACE
            (i -> string(i, b"\x00A0").map(|_| WhiteSpace::NoBreakSpace)) <|> // <NBSP>; NO-BREAK SPACE
            (i -> string(i, b"\xFEFF").map(|_| WhiteSpace::ZeroWidthNoBreakSpace)) <|> // <ZWNBSP>; ZERO WIDTH NO-BREAK SPACE
            other_whitespace(); // Any other Unicode "Separator, space" code point

        ret whitespace_char
    };

    parse_result

    // TODO: fix
    // on_error(parse_result,
    //          |i| ErrorLocation::new(i.position(), "Expected whitespace.".to_string()))

}

// 11.3 Line Terminators

#[derive(Debug)]
enum LineTerminator {
    LineFeed,
    CarriageReturn,
    LineSeparator,
    ParagraphSeparator,
}

// TODO: test
fn line_terminator<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, LineTerminator> {

    let parse_result = parse!{i;

        let result =
            (i -> string(i, b"\x000A").map(|_| LineTerminator::LineFeed)) <|>   // <LF>; LINE FEED (LF)
            (i -> string(i, b"\x000D").map(|_| LineTerminator::CarriageReturn)) <|> // <CR>; CARRIAGE RETURN (CR)
            (i -> string(i, b"\x2028").map(|_| LineTerminator::LineSeparator))  <|> // <LS>; LINE SEPARATOR
            (i -> string(i, b"\x2029").map(|_| LineTerminator::ParagraphSeparator)); // <PS>; PARAGRAPH SEPARATOR

        ret result
    };

    // TODO: fix
    parse_result
    // on_error(parse_result, |i| {
    //     let loc = i.position();
    //     let reason = "Expected utf8 character.".to_string();
    //     ErrorLocation::new(loc, reason)
    // })
}

// 11.4 Comments

#[derive(Debug)]
enum Comment {
    MultiLineComment(String),
    SingleLineComment(String),
}

// TODO: test
fn comment<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Comment> {

    // http://www.ecma-international.org/ecma-262/7.0/#prod-MultiLineComment
    #[inline]
    fn multiline_comment<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Comment> {

        const END: &'static [u8; 2] = b"*/";

        #[inline]
        fn stop_at<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
            string(i, END).map(|_| ())
            // on_error(string(i, END).map(|_| ()), |i| {
            //     let loc = i.position();
            //     ErrorLocation::new(loc, "Expected */.".to_string())
            // })
        }

        // TODO: verify production rule satisfaction
        // http://www.ecma-international.org/ecma-262/7.0/#prod-MultiLineCommentChars

        parse!{i;

            (i -> {
                on_error(
                    string(i, b"/*"),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected /* for multi-line comment.".to_string())
                    }
                )
            });

            let contents = string_till(stop_at);
            stop_at();
            ret Comment::MultiLineComment(contents)
        }
    }

    // http://www.ecma-international.org/ecma-262/7.0/#prod-SingleLineComment
    #[inline]
    fn singleline_comment<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Comment> {

        #[inline]
        fn stop_at<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
            line_terminator(i).then(|i| i.ret(()))
        }

        parse!{i;

            (i -> {
                on_error(
                    string(i, b"//"),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected // for single-line comment.".to_string())
                    }
                )
            });

            let contents = string_till(stop_at);
            // NOTE: buffer contents matching line_terminator is not consumed
            ret Comment::SingleLineComment(contents)
        }
    }

    parse!{i;
        let contents = multiline_comment() <|>
            singleline_comment();
        ret contents
    }
}

// 11.6 Names and Keywords

// IdentifierName

pub struct IdentifierName(IdentifierStart, Vec<IdentifierStart>, Vec<IdentifierPart>);

// TODO: test
pub fn identifier_name<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, IdentifierName> {

    let parse_result = parse!{i;

        let start = identifier_start();
        let more_start: Vec<IdentifierStart> = many(identifier_start);
        let rest: Vec<IdentifierPart> = many(identifier_part);

        ret {
            IdentifierName(start, more_start, rest)
        }
    };

    on_error(parse_result, |i| {
        let reason = format!("Invalid identifier.");
        ErrorLocation::new(i.position(), reason)
    })
}

// IdentifierStart

enum IdentifierStart {
    UnicodeIDStart(UnicodeIDStart),
    DollarSign,
    Underscore,
    UnicodeEscapeSequence(UnicodeEscapeSequence),
}

// TODO: test
fn identifier_start<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, IdentifierStart> {

    #[inline]
    fn escaped_unicode_escape_seq<I: U8Input>(i: ESInput<I>)
                                              -> ESParseResult<I, UnicodeEscapeSequence> {
        token(i, b'\\').then(unicode_escape_sequence)
    }

    parse!{i;

        let start =
        (i -> unicode_id_start(i).map(|x| IdentifierStart::UnicodeIDStart(x))) <|>
        (i -> token(i, b'$').map(|_| IdentifierStart::DollarSign)) <|>
        (i -> token(i, b'_').map(|_| IdentifierStart::Underscore)) <|>
        (i -> escaped_unicode_escape_seq(i).map(|x| IdentifierStart::UnicodeEscapeSequence(x)));

        ret start
    }
}

// IdentifierPart

enum IdentifierPart {
    UnicodeIDContinue(UnicodeIDContinue),
    DollarSign,
    Underscore,
    UnicodeEscapeSequence(UnicodeEscapeSequence),
    ZeroWidthNonJoiner, // ZWNJ
    ZeroWidthJoiner, // ZWJ
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierPart
fn identifier_part<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, IdentifierPart> {

    #[inline]
    fn escaped_unicode_escape_seq<I: U8Input>(i: ESInput<I>)
                                              -> ESParseResult<I, UnicodeEscapeSequence> {
        token(i, b'\\').then(unicode_escape_sequence)
    }

    parse!{i;

        let part =
        (i -> unicode_id_continue(i).map(|x| IdentifierPart::UnicodeIDContinue(x))) <|>
        (i -> token(i, b'$').map(|_| IdentifierPart::DollarSign)) <|>
        (i -> token(i, b'_').map(|_| IdentifierPart::Underscore)) <|>
        (i -> escaped_unicode_escape_seq(i).map(|x| IdentifierPart::UnicodeEscapeSequence(x))) <|>
        // <ZWNJ> (i.e. Zero-width non-joiner)
        (i -> string(i, b"\x200C").map(|x| IdentifierPart::ZeroWidthNonJoiner)) <|>
        // <ZWJ> (i.e. Zero-width joiner)
        (i -> string(i, b"\x200D").map(|x| IdentifierPart::ZeroWidthJoiner));

        ret part
    }
}

// UnicodeIDStart

#[derive(Debug, PartialEq)]
struct UnicodeIDStart(char);

// http://www.ecma-international.org/ecma-262/7.0/#prod-UnicodeIDStart
fn unicode_id_start<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, UnicodeIDStart> {

    // any Unicode code point with the Unicode property "ID_Start"

    parse_utf8_char(i).bind(|i, c: char| {
        // TODO: https://github.com/rust-lang/rust/issues/4928
        if c.is_xid_start() {
            i.ret(UnicodeIDStart(c))
        } else {
            // TODO: better error
            let loc = i.position();
            let reason = format!("Invalid utf8 start character.");
            i.err(ErrorLocation::new(loc, reason).into())
        }
    })
}

#[test]
fn unicode_id_start_test() {

    use chomp::primitives::IntoInner;
    use parsers::current_position::CurrentPosition;
    use chomp::types::numbering::InputPosition;

    let i = InputPosition::new("a".as_bytes(), CurrentPosition::new());
    match unicode_id_start(i).into_inner().1 {
        Ok(result) => {
            let c = 'a';
            assert!(c.is_xid_start());

            assert_eq!(result, UnicodeIDStart(c));
        }
        Err(_) => {
            assert!(false);
        }
    }

    let fails = vec!["1", " ", "\t", "\n", "\r", ";", "?", "$", "_"];

    for input in fails {
        let i = InputPosition::new(input.as_bytes(), CurrentPosition::new());
        match unicode_id_start(i).into_inner().1 {
            Ok(_) => {
                assert!(false);
            }
            Err(_) => {
                assert!(true);
            }
        }
    }
}

// UnicodeIDContinue

#[derive(Debug, PartialEq)]
struct UnicodeIDContinue(char);

// http://www.ecma-international.org/ecma-262/7.0/#prod-UnicodeIDContinue
fn unicode_id_continue<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, UnicodeIDContinue> {
    parse_utf8_char(i).bind(|i, c: char| {

        if c.is_xid_continue() {
            i.ret(UnicodeIDContinue(c))
        } else {
            // TODO: better error
            let loc = i.position();
            let reason = format!("Invalid utf8 continue character: `{}`", c);
            i.err(ErrorLocation::new(loc, reason).into())
        }

    })
}

#[test]
fn unicode_id_continue_test() {

    use chomp::primitives::IntoInner;
    use chomp::types::numbering::InputPosition;
    use parsers::current_position::CurrentPosition;

    let success: Vec<&str> = vec!["a", "1", "_"];

    for input in success {
        let i = InputPosition::new(input.as_bytes(), CurrentPosition::new());
        match unicode_id_continue(i).into_inner().1 {
            Ok(result) => {
                let x = input.chars().next().unwrap();
                assert_eq!(result, UnicodeIDContinue(x));
            }
            Err(_) => {
                assert!(false);
            }
        }
    }

    let fails: Vec<&str> = vec![" ", "\t", "\n", "\r", ";", "?", "$"];

    for input in fails {
        let i = InputPosition::new(input.as_bytes(), CurrentPosition::new());
        match unicode_id_continue(i).into_inner().1 {
            Ok(_) => {
                println!("{:?}", input);
                assert!(false);
            }
            Err(err) => {
                assert!(true);
            }
        }
    }
}

// 11.6.2 Reserved Words

// TODO: test
pub fn reserved_word<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
    parse!{i;
        keyword() <|>
        future_reserved_word() <|>
        null_literal() <|>
        boolean_literal();

        ret {()}
    }
}

// 11.6.2.1 Keywords

// TODO: test
fn keyword<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
    parse!{i;
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
        string(b"try");

        ret {()}
    }
}

// 11.6.2.2 Future Reserved Words

// TODO: test
fn future_reserved_word<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
    parse!{i;
        string(b"enum") <|>
        string(b"await");

        // TODO: strict mode keywords

        ret {()}
    }
}

// 11.8 Literals

// 11.8.1 Null Literals

// TODO: test
fn null_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
    string(i, b"null").map(|_| ())
}

// 11.8.2 Boolean Literals

fn boolean_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
    parse!{i;
        string(b"true") <|>
        string(b"false");

        ret {()}
    }
}

// 11.8.3 Numeric Literals

// TODO: complete

// HexDigits

#[derive(PartialEq, Debug)]
struct HexDigits(HexDigit, Vec<HexDigit>);

impl HexDigits {
    fn as_string(&self) -> String {
        let mut foo = vec![self.0.clone()];
        foo.extend_from_slice(&self.1);
        foo.into_iter().map(|HexDigit(c)| c).collect()
    }
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-HexDigits
fn hex_digits<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, HexDigits> {

    let parse_result = parse!{i;

        let head = hex_digit();
        let rest: Vec<HexDigit> = many(hex_digit);

        ret {
            HexDigits(head, rest)
        }
    };

    on_error(parse_result, |i| {
        let loc = i.position();
        ErrorLocation::new(loc, "Expected hex digit.".to_string())
    })
}

#[test]
fn hex_digits_test() {

    use chomp::types::numbering::InputPosition;
    use chomp::primitives::IntoInner;
    use parsers::current_position::CurrentPosition;

    let i = InputPosition::new(&b"e"[..], CurrentPosition::new());
    match hex_digits(i).into_inner().1 {
        Ok(result) => {
            assert_eq!(result, HexDigits(HexDigit('e'), vec![]));
        }
        Err(_) => {
            assert!(false);
        }
    }

    let i = InputPosition::new(&b"ad"[..], CurrentPosition::new());
    match hex_digits(i).into_inner().1 {
        Ok(result) => {
            assert_eq!(result, HexDigits(HexDigit('a'), vec![HexDigit('d')]));
        }
        Err(_) => {
            assert!(false);
        }
    }

    let i = InputPosition::new(&b"gad"[..], CurrentPosition::new());
    match hex_digits(i).into_inner().1 {
        Ok(_) => {
            assert!(false);
        }
        Err(_) => {
            assert!(true);
        }
    }

}

// HexDigit

#[derive(PartialEq, Debug, Clone)]
struct HexDigit(char);

#[inline]
fn hex_digit<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, HexDigit> {

    #[inline]
    fn is_hex_digit(c: u8) -> bool {
        (b'0' <= c && c <= b'9') || (b'a' <= c && c <= b'f') || (b'A' <= c && c <= b'F')
    }

    on_error(satisfy(i, is_hex_digit), |i| {
            let loc = i.position();
            ErrorLocation::new(loc, "Expected hex digit (0 to F).".to_string())
        })
        .map(|x| HexDigit(x as char))
}

// 11.8.4 String Literals

enum UnicodeEscapeSequence {
    HexDigits(HexDigits),
    Hex4Digits(Hex4Digits),
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-UnicodeEscapeSequence
// TODO: needs test
fn unicode_escape_sequence<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, UnicodeEscapeSequence> {
    either(i,
        |i| -> ESParseResult<I, HexDigits> {parse!{i;
            // e.g. u{9A9A}
            token(b'u');
            token(b'{');
            let sequence = hex_digits();
            token(b'}');
            ret sequence
        }},
        |i| {parse!{i;
            // e.g. u9A9A
            token(b'u');
            let sequence = hex_4_digits();
            ret {
                UnicodeEscapeSequence::Hex4Digits(sequence)
                // TODO: remove
                // string_to_unicode_char(&sequence).unwrap()
            }
        }}
    )
    .bind(|i, result| -> ESParseResult<I, UnicodeEscapeSequence> {
        match result {
            Either::Left(sequence) => {

                i.ret(UnicodeEscapeSequence::HexDigits(sequence))

                // TODO: moved to traits; remove
                // // == 11.8.4.1 Static Semantics: Early Errors ==
                // //
                // // http://www.ecma-international.org/ecma-262/7.0/#sec-string-literals-static-semantics-early-errors
                // if (
                //         sequence.0[0] != HexDigit('0') &&
                //         sequence.0.len() > 6) ||
                //     sequence.mathematical_value() > 1114111 /* 10ffff */ {

                //     let err_val = ErrorLocation::new(i.position(),
                //         "Invalid unicode escape sequence. Expect to be less or equal to 10ffff.".to_string());

                //     i.err(err_val.into())
                // } else {
                //     // TODO: remove
                //     // let HexDigits(sequence) = sequence;
                //     // let c = string_to_unicode_char(&sequence).unwrap();
                //     i.ret(UnicodeEscapeSequence::HexDigits(sequence))
                // }
            },
            Either::Right(c) => {
                i.ret(c)
            }
        }
    })
    // TODO: fix
    // .bind(|i, result| -> ESParseResult<I, UnicodeEscapeSequence> {
    //     match result.check_early_error() {
    //         None => i.ret(result),
    //         Some(syntax_error) => i.err(syntax_error.into())
    //     }
    // })
}

// Hex4Digits

#[derive(PartialEq, Debug)]
struct Hex4Digits(HexDigit, HexDigit, HexDigit, HexDigit);

fn hex_4_digits<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Hex4Digits> {
    parse!{i;

        let digit_1 = hex_digit();
        let digit_2 = hex_digit();
        let digit_3 = hex_digit();
        let digit_4 = hex_digit();

        ret {
            Hex4Digits(digit_1, digit_2, digit_3, digit_4)
        }
    }
}

#[test]
fn hex_4_digits_test() {

    use chomp::types::numbering::InputPosition;
    use chomp::primitives::IntoInner;
    use parsers::current_position::CurrentPosition;

    let i = InputPosition::new(&b"adad"[..], CurrentPosition::new());
    match hex_4_digits(i).into_inner().1 {
        Ok(result) => {
            assert_eq!(result,
                       Hex4Digits(HexDigit('a'), HexDigit('d'), HexDigit('a'), HexDigit('d')));
        }
        Err(_) => {
            assert!(false);
        }
    }

    // TODO: more tests
}

// 11.9 Automatic Semicolon Insertion

#[must_use = "SemiColon should be moved into another AST type."]
pub enum SemiColon {
    HasSemiColon(Vec<CommonDelim> /* ; */),
    NoSemiColon,
}

// This parser is used in grammar that expects a semi-colon.
pub fn semicolon<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, SemiColon> {
    option(i,
           |i| {
        parse!{i;
            let delim = common_delim();
            token(b';');

            ret SemiColon::HasSemiColon(delim)
        }
    },
           // A semi-colon was expected, but none was encountered.
           SemiColon::NoSemiColon)
}
