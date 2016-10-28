#![recursion_limit="1000"]
#![feature(unicode)]
// == crates ==
#[macro_use] extern crate chomp;
#[macro_use] extern crate quick_error;
extern crate enum_set;

// == rust std imports ==

use std::mem;
use std::rc::Rc;
use std::cell::RefCell;

// == 3rd-party imports ==

use chomp::run_parser;
use chomp::parsers::{SimpleResult, scan, token, any, take_till, string, satisfy, take_while1};
use chomp::combinators::{option, look_ahead, many_till, many1, many, or, either};
use chomp::types::{Buffer, Input, ParseResult, U8Input};
use chomp::parse_only;
use chomp::parsers::Error as ChompError;
use chomp::primitives::Primitives;
use chomp::prelude::{Either};
use chomp::types::numbering::{InputPosition, LineNumber, Numbering};
use chomp::primitives::IntoInner;

use enum_set::{EnumSet, CLike};

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

type ESInput<I> = InputPosition<I, CurrentPosition>;
type ESParseResult<I, T> = ParseResult<ESInput<I>, T, ParseError>;

// == errors ==

quick_error! {
    #[derive(Debug)]
    pub enum ParseError {
        Expected(loc: CurrentPosition, descr: String) {
            description(descr)
            display("Line {}, Column {}: {}", loc.line(), loc.col(), descr)
        }
    }
}

// == helpers ==

// like ParseResult::map_err, but this higher-order helper passes &Input to
// error mapping/transform function
#[inline]
fn on_error<I: Input, T, E, F, V, G>(i: I, f: F, g: G) -> ParseResult<I, T, V>
    where F: FnOnce(I) -> ParseResult<I, T, E>,
          G: FnOnce(E, &I) -> V {

    match f(i).into_inner() {
        (i, Ok(t))  => i.ret(t),
        (i, Err(e)) => {
            let err_val = g(e, &i);
            i.err(err_val)
        }
    }
}

#[inline]
fn string_to_unicode_char(s: &str) -> Option<char> {
    u32::from_str_radix(s, 16)
        .ok()
        .and_then(std::char::from_u32)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct CurrentPosition(
    // The current line, zero-indexed.
    u64,
    // The current col, zero-indexed.
    u64
);

impl CurrentPosition {
    // Creates a new (line, col) counter with zero.
    pub fn new() -> Self {
        CurrentPosition(0, 0)
    }

    pub fn line(&self) -> u64 {
        // zero-indexed to one-indexed
        self.0 + 1
    }

    pub fn col(&self) -> u64 {
        // zero-indexed to one-indexed
        self.1 + 1
    }
}

impl Numbering for CurrentPosition {
    type Token  = u8;

    fn update<'a, B>(&mut self, b: &'a B)
        where B: Buffer<Token=Self::Token> {
            b.iterate(|c| if c == b'\n' {
                self.0 += 1; // line num
                self.1 = 0;  // col num
            } else {
                self.1 += 1; // col num
            });
    }

    fn add(&mut self, t: Self::Token) {
        if t == b'\n' {
            self.0 += 1; // line num
            self.1 = 0;  // col num
        } else {
            self.1 += 1; // col num
        }
    }
}


// == delimeted list parser ==
//
// Source: http://www.engr.mun.ca/~theo/Misc/exp_parsing.htm#classic
// Source: https://en.wikipedia.org/wiki/Operator-precedence_parser#Precedence_climbing_method
//
// invariant:
// - item does not consume eof (may lookahead eof to stop)
// - item does not consume delim (may lookahead delim to stop)
// - delim does not consume eof
// - delim does not consume item
//
// pseudo grammar:
//
// list(delim, item, rest) = item rest(delim, item) | item
// rest(delim, item) = delim item rest(delim) | delim item
//
// list(delim, reducer) = reducer(accumulator) rest(delim) | reducer(accumulator)
// rest(delim, accumulator, reducer) = delim reducer(accumulator) rest(delim, accumulator, reducer) |
//                                     delim reducer(accumulator)
#[inline]
fn parse_list<I: U8Input, D, Delim, A, R, Reduced>(input: I, delimiter: D, reducer: R) -> SimpleResult<I, A>
    where D: Fn(I, Rc<RefCell<A>>) -> SimpleResult<I, Delim>,
          R: Fn(I, Rc<RefCell<A>>) -> SimpleResult<I, Reduced>,
          A: Default
{

    let accumulator: A = Default::default();
    let initial_accumulator: Rc<RefCell<A>> = Rc::new(RefCell::new(accumulator));

    reducer(input, initial_accumulator.clone())
        .then(|i| {
            option(i, |i| parse_list_rest(i, delimiter, initial_accumulator.clone(), reducer), ())
        })
        .map(|_| {
            Rc::try_unwrap(initial_accumulator)
                .ok()
                .unwrap()
                .into_inner()
        })
}

#[inline]
fn parse_list_rest<I: U8Input, D, Delim, A, R, Reduced>(input: I, delimiter: D, accumulator: Rc<RefCell<A>>,
    reducer: R) -> SimpleResult<I, ()>
    where D: Fn(I, Rc<RefCell<A>>) -> SimpleResult<I, Delim>,
          R: Fn(I, Rc<RefCell<A>>) -> SimpleResult<I, Reduced>,
          A: Default
{

    let mut should_continue = true;
    let mut parse_result = delimiter(input, accumulator.clone())
        .then(|i| reducer(i, accumulator.clone()))
        .map(|_| ())
        .map_err(|e| {
            should_continue = false;
            e
        });

    while should_continue {
        parse_result = parse_result
            .then(|i| {
                either(i,
                    // left
                    |i| {
                        delimiter(i, accumulator.clone())
                            .then(|i| reducer(i, accumulator.clone()))
                            .map(|_| ())
                    },
                    // right
                    |i| i.ret(())
                )
            })
            .bind(|i, result| {
                match result {
                    Either::Left(_) => {
                        // continue while loop
                    },
                    Either::Right(_) => {
                        // break while loop
                        should_continue = false;
                    }
                }
                i.ret(())
            })
            .map_err(|e| {
                should_continue = false;
                e
            });
    }

    parse_result

    // NOTE: above is iterative version
    // parse!{input;
    //     delimiter();
    //     reducer(accumulator.clone());
    //     option(|i| parse_list_rest(i, delimiter, accumulator, reducer), ());
    //     ret {()}
    // }
}

#[inline]
fn parse_single_quote_string<I: U8Input>(input: I) -> SimpleResult<I, String> {
    parse!{input;

        token(b'\'');

        let line: Vec<u8> = parse_list(
            // delimiter
            |i, _| string(i, br#"\'"#),
            // reducer
            parse_single_quote_string_reducer

        );

        token(b'\'');

        ret {
            let line = String::from_utf8_lossy(line.as_slice()).into_owned();
            line
        }
    }
}

#[inline]
fn parse_single_quote_string_reducer<I: U8Input>(input: I, accumulator: Rc<RefCell<Vec<u8>>>)
    -> SimpleResult<I, ()> {
    parse!{input;

        let line: Vec<u8> = many_till(any, parse_single_quote_string_look_ahead);

        let has_quote = option(
            |i| look_ahead(i, |i| string(i, br#"\'"#)).map(|_| true),
            false
        );

        ret {

            if line.len() > 0 {
                let mut line = line;
                accumulator.borrow_mut().append(&mut line);
            }

            if has_quote {
                accumulator.borrow_mut().push(b'\'');
            }

            ()
        }
    }
}

#[inline]
fn parse_single_quote_string_look_ahead<I: U8Input>(input: I) -> SimpleResult<I, ()> {
    parse!{input;
        look_ahead(|i| or(i,
            |i| string(i, br#"\'"#).map(|_| ()),
            |i| token(i, b'\'').map(|_| ())
        ));
        ret {()}
    }
}

#[test]
fn parse_single_quote_string_test() {

    match parse_only(parse_single_quote_string, br#"foo"#) {
        Ok(_) => {
            assert!(false);
        }
        Err(_) => {
            assert!(true);
        }
    }

    match parse_only(parse_single_quote_string, br#"bar'foo'"#) {
        Ok(result) => {
            assert!(false);
        }
        Err(_) => {
            assert!(true);
        }
    }

    match parse_only(parse_single_quote_string, br#"'\'foo\''"#) {
        Ok(result) => {
            assert_eq!(result, r#"'foo'"#.to_owned());
        }
        Err(_) => {
            assert!(false);
        }
    }

    match parse_only(parse_single_quote_string, br#"'\'foo'"#) {
        Ok(result) => {
            assert_eq!(result, r#"'foo"#.to_owned());
        }
        Err(_) => {
            assert!(false);
        }
    }

    match parse_only(parse_single_quote_string, br#"'foo'bar"#) {
        Ok(result) => {
            assert_eq!(result, "foo".to_owned());
        }
        Err(_) => {
            assert!(false);
        }
    }

    match parse_only(parse_single_quote_string, br#"'\'foo\'baz'bar"#) {
        Ok(result) => {
            assert_eq!(result, r#"'foo'baz"#.to_owned());
        }
        Err(_) => {
            assert!(false);
        }
    }

}

// == parser helpers ==

#[inline]
fn string_till<I: U8Input, F>(input: I, mut stop_at: F) -> SimpleResult<I, String>
    where F: Fn(I) -> SimpleResult<I, ()>  {

    many_till(input, any, |i| look_ahead(i, &mut stop_at))
        .bind(|i, line: Vec<u8>| {
            let string: String = String::from_utf8_lossy(line.as_slice()).into_owned();
            i.ret(string)
        })

}

#[inline]
fn token_as_char<I: U8Input>(i: I, c: u8) -> SimpleResult<I, char> {
    token(i, c)
        .bind(|i, c| {
            i.ret(c as char)
        })
}

// TODO: test
#[inline]
fn parse_utf8_char_of_bytes<I: U8Input>(i: I, needle: &[u8]) -> SimpleResult<I, char> {
    look_ahead(i, |i| string(i, needle))
        .then(parse_utf8_char)
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

            // TODO: potential optimization point;
            //       rather than reading internal_buf.len() times on every loop
            //
            // see: https://github.com/rust-lang/rust/issues/34815

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

    // case: only sparkle heart is parsed

    let sparkle_heart_and_smile = vec![
        // http://graphemica.com/%F0%9F%92%96
        240, 159, 146, 150,
        // http://graphemica.com/%F0%9F%98%80
        240, 159, 152, 128
    ];

    match parse_only(parse_utf8_char, &sparkle_heart_and_smile) {
        Ok(result) => {
            assert_eq!(result, '\u{1f496}');
        }
        Err(_) => {
            assert!(false);
        }
    }
}

// == Tokens ==
#[derive(Debug)]
enum Comment {
    MultiLineComment(String),
    SingleLineComment(String)
}

#[derive(Debug)]
enum Token {
    WhiteSpace(char),
    LineTerminator(char),
    Comment(Comment),
    This,
    Null
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
            let delim: Token =
                whitespace() <|>
                line_terminator() <|>
                comment();
            ret delim
        }
    }

    many(i, __common_delim)
}


// == Parameters ==
// Based on: http://www.ecma-international.org/ecma-262/7.0/#sec-grammar-notation
#[repr(u32)]
#[derive(Clone)]
enum Parameter {
    In,
    Yield,
    Return
}

impl CLike for Parameter {
    fn to_u32(&self) -> u32 {
        let encoded: Self = self.clone();
        encoded as u32
    }

    unsafe fn from_u32(v: u32) -> Self {
        mem::transmute(v)
    }
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

        let whitespace_char =
            parse_utf8_char_of_bytes(b"\x0009") <|> // <TAB>; CHARACTER TABULATION
            parse_utf8_char_of_bytes(b"\x000B") <|> // <VT>; LINE TABULATION
            parse_utf8_char_of_bytes(b"\x000C") <|> // <FF>; FORM FEED (FF)
            parse_utf8_char_of_bytes(b"\x0020") <|> // <SP>; SPACE
            parse_utf8_char_of_bytes(b"\x00A0") <|> // <NBSP>; NO-BREAK SPACE
            parse_utf8_char_of_bytes(b"\xFEFF") <|> // <ZWNBSP>; ZERO WIDTH NO-BREAK SPACE
            other_whitespace(); // Any other Unicode "Separator, space" code point

        ret Token::WhiteSpace(whitespace_char)
    }
}

// == 11.3 Line Terminators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-line-terminators

// http://www.ecma-international.org/ecma-262/7.0/#prod-LineTerminator
fn line_terminator<I: U8Input>(i: I) -> SimpleResult<I, Token> {
    parse!{i;

        let line_terminator_char =
            parse_utf8_char_of_bytes(b"\x000A") <|> // <LF>; LINE FEED (LF)
            parse_utf8_char_of_bytes(b"\x000D") <|> // <CR>; CARRIAGE RETURN (CR)
            parse_utf8_char_of_bytes(b"\x2028") <|> // <LS>; LINE SEPARATOR
            parse_utf8_char_of_bytes(b"\x2029");    // <PS>; PARAGRAPH SEPARATOR

        ret Token::LineTerminator(line_terminator_char)
    }
}

// == 11.4 Comments ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-comments

// http://www.ecma-international.org/ecma-262/7.0/#prod-Comment
fn comment<I: U8Input>(i: I) -> SimpleResult<I, Token> {

    // http://www.ecma-international.org/ecma-262/7.0/#prod-MultiLineComment
    #[inline]
    fn multiline_comment<I: U8Input>(i: I) -> SimpleResult<I, Comment> {

        const END: &'static [u8; 2] = b"*/";

        #[inline]
        fn stop_at<I: U8Input>(i: I) -> SimpleResult<I, ()> {
            string(i, END).then(|i| i.ret(()))
        }

        // TODO: verify production rule satisfaction
        // http://www.ecma-international.org/ecma-262/7.0/#prod-MultiLineCommentChars

        parse!{i;
            string(b"/*");
            let contents = string_till(stop_at);
            string(END);
            ret Comment::MultiLineComment(contents)
        }
    }

    // http://www.ecma-international.org/ecma-262/7.0/#prod-SingleLineComment
    #[inline]
    fn singleline_comment<I: U8Input>(i: I) -> SimpleResult<I, Comment> {

        #[inline]
        fn stop_at<I: U8Input>(i: I) -> SimpleResult<I, ()> {
            line_terminator(i).then(|i| i.ret(()))
        }

        parse!{i;
            string(b"//");
            let contents = string_till(stop_at);
            // NOTE: buffer contents matching line_terminator is not consumed
            ret Comment::SingleLineComment(contents)
        }
    }

    parse!{i;
        let contents = multiline_comment() <|>
            singleline_comment();
        ret Token::Comment(contents)
    }
}

// == 11.6 Names and Keywords ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-names-and-keywords

struct IdentifierName(String);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierName
fn identifier_name<I: U8Input>(i: I) -> SimpleResult<I, IdentifierName> {
    parse!{i;

        let start: Vec<char> = many1(identifier_start);
        let rest: Vec<char> = many(identifier_part);

        ret {
            // TODO: room for optimization
            let mut start: String = start.into_iter().collect();
            let rest: String = rest.into_iter().collect();
            start.push_str(&rest);
            IdentifierName(start)
        }
    }
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierStart
fn identifier_start<I: U8Input>(i: I) -> SimpleResult<I, char> {

    #[inline]
    fn identifier_start_unicode<I: U8Input>(i: I) -> SimpleResult<I, char> {
        escaped_unicode_escape_seq(i)
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
        token(i, b'\\')
            .then(unicode_escape_seq)
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

    let fails = vec!["1", " ", "\t", "\n", "\r", ";", "?", "$", "_"];

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

    let fails: Vec<&str> = vec![" ", "\t", "\n", "\r", ";", "?", "$", "_"];

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

// == 11.6.2 Reserved Words ==

// TODO: enum Keyword type

// http://www.ecma-international.org/ecma-262/7.0/#sec-reserved-words
fn reserved_word<I: U8Input>(i: I) -> SimpleResult<I, I::Buffer> {

    #[inline]
    fn string_not_utf8<I: U8Input>(i: I, needle: &[u8]) -> SimpleResult<I, I::Buffer> {

        let mark = i.mark();
        let mut current_needle = needle;
        let mut should_continue = true;

        let mut parse_result = either(i,
            // left
            escaped_unicode_escape_seq,
            // right
            parse_utf8_char
        ).map_err(|e| {
            should_continue = false;
            e
        });

        while should_continue {

            parse_result = parse_result
                .bind(|i, result| {
                    match result {
                        Either::Left(c) => {
                            // TODO: Reserved keyword must not contain escaped characters.
                            i.err(ChompError::unexpected())
                        },
                        Either::Right(c) => {

                            let mut buf = String::with_capacity(1);
                            buf.push(c);
                            let bytes = buf.as_bytes();

                            if current_needle.starts_with(bytes) {
                                current_needle = current_needle.split_at(bytes.len()).1;
                                i.ret(Either::Right(c))
                            } else {
                                i.err(ChompError::unexpected())
                            }
                        }
                    }
                })
                .map_err(|e| {
                    should_continue = false;
                    e
                });

            if current_needle.len() <= 0 || !should_continue {
                should_continue = false;
                break;
            }

            parse_result = parse_result
                .then(|i| {
                    either(i,
                        // left
                        escaped_unicode_escape_seq,
                        // right
                        parse_utf8_char
                    )
                })
                .map_err(|e| {
                    should_continue = false;
                    e
                });
        }

        parse_result
        .then(|mut i| {
            let res = (&mut i).consume_from(mark);
            i.ret(res)
        })
    }

    parse!{i;
        let keyword =
            // == 11.6.2.1 Keywords ==
            // http://www.ecma-international.org/ecma-262/7.0/#prod-Keyword
            string_not_utf8(b"break") <|>
            string_not_utf8(b"do") <|>
            string_not_utf8(b"in") <|>
            string_not_utf8(b"typeof") <|>
            string_not_utf8(b"case") <|>
            string_not_utf8(b"else") <|>
            string_not_utf8(b"instanceof") <|>
            string_not_utf8(b"var") <|>
            string_not_utf8(b"catch") <|>
            string_not_utf8(b"export") <|>
            string_not_utf8(b"new") <|>
            string_not_utf8(b"void") <|>
            string_not_utf8(b"class") <|>
            string_not_utf8(b"extends") <|>
            string_not_utf8(b"return") <|>
            string_not_utf8(b"while") <|>
            string_not_utf8(b"const") <|>
            string_not_utf8(b"finally") <|>
            string_not_utf8(b"super") <|>
            string_not_utf8(b"with") <|>
            string_not_utf8(b"continue") <|>
            string_not_utf8(b"for") <|>
            string_not_utf8(b"switch") <|>
            string_not_utf8(b"yield") <|>
            string_not_utf8(b"debugger") <|>
            string_not_utf8(b"function") <|>
            string_not_utf8(b"this") <|>
            string_not_utf8(b"default") <|>
            string_not_utf8(b"if") <|>
            string_not_utf8(b"throw") <|>
            string_not_utf8(b"delete") <|>
            string_not_utf8(b"import") <|>
            string_not_utf8(b"try") <|>

            // TODO: [edit] remove; replaced by syntax error
            // TODO: is this right?
            // http://www.ecma-international.org/ecma-262/7.0/#sec-keywords
            // string_not_utf8(b"let") <|>
            // string_not_utf8(b"static") <|>

            // == 11.6.2.2 Future Reserved Words ==
            // http://www.ecma-international.org/ecma-262/7.0/#sec-future-reserved-words
            string_not_utf8(b"enum") <|>
            string_not_utf8(b"await") <|>

            // == 11.8.1 Null Literals ==
            // http://www.ecma-international.org/ecma-262/7.0/#prod-NullLiteral
            string_not_utf8(b"null") <|>

            // == 11.8.2 Boolean Literals ==
            // http://www.ecma-international.org/ecma-262/7.0/#prod-BooleanLiteral
            string_not_utf8(b"true") <|>
            string_not_utf8(b"false");

        ret keyword
    }
}

#[test]
fn reserved_word_test() {

    match parse_only(reserved_word, b"var") {
        Ok(_) => {
            assert!(true);
        }
        Err(_) => {
            assert!(false);
        }
    }

    // A code point in a ReservedWord cannot be expressed by a \UnicodeEscapeSequence.

    let fails = vec![
        r"\u0076\u0061\u0072",
        r"\u0076\u{0061}\u0072",
        r"v\u0061\u0072",
        r"\u0076a\u0072",
        r"\u0076\u0061r",
    ];

    for fail in fails {
        match parse_only(reserved_word, fail.as_bytes()) {
            Ok(_) => {
                assert!(false);
            }
            Err(_) => {
                assert!(true);
            }
        }
    }

}

// == 11.8 Literals ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-lexical-grammar-literals

// == 11.8.1 Null Literals ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-null-literals

struct Null;

// http://www.ecma-international.org/ecma-262/7.0/#prod-NullLiteral
#[inline]
fn null_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Null> {
    on_error(
        i,
        |i| string(i, b"null").map(|_| Null),
        |_err, i| {
            let loc = i.position();
            ParseError::Expected(loc, "Expected null keyword.".to_string())
        }
    )
}

// == 11.8.2 Boolean Literals ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-boolean-literals

enum Bool {
    True,
    False
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-BooleanLiteral
#[inline]
fn boolean_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Bool> {
    on_error(
        i,
        |i| parse!{i;

            let result = string(b"true").map(|_| Bool::True) <|>
            string(b"false").map(|_| Bool::False);

            ret result
        },
        |_err, i| {
            let loc = i.position();
            ParseError::Expected(loc, "Expected boolean literal.".to_string())
        }
    )
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


fn escaped_unicode_escape_seq<I: U8Input>(i: I) -> SimpleResult<I, char> {
    token(i, b'\\')
        .then(unicode_escape_seq)
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

enum IdentifierReference {
    Identifier,
    Yield
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierReference
fn identifier_reference<I: U8Input>(i: I, params: &EnumSet<Parameter>) -> SimpleResult<I, ()> {

    #[inline]
    fn __binding<I: U8Input>(i: I) -> SimpleResult<I, ()> {
        parse!{i;
            identifier();
            // TODO: token
            ret {()}
        }
    }

    if !params.contains(&Parameter::Yield) {

        let result = either(i,
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
        });

        return result;
    }

    if params.len() >= 2 {
        panic!("misuse of identifier_reference");
    }

    __binding(i)

}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BindingIdentifier
fn binding_identifier<I: U8Input>(i: I, params: &EnumSet<Parameter>) -> SimpleResult<I, ()> {

    #[inline]
    fn __binding<I: U8Input>(i: I) -> SimpleResult<I, ()> {
        parse!{i;
            identifier();
            // TODO: token
            ret {()}
        }
    }

    if !params.contains(&Parameter::Yield) {

        let result = either(i,
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
        });

        return result;
    }

    if params.len() >= 2 {
        panic!("misuse of binding_identifier");
    }

    __binding(i)

}

struct Identifier(IdentifierName);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Identifier
fn identifier<I: U8Input>(i: I) -> SimpleResult<I, Identifier> {
    either(i,
        |i| reserved_word(i),  // left
        |i| identifier_name(i) // right
    )
    .bind(|i, result| {
        match result {
            Either::Left(_) => {
                i.err(ChompError::unexpected())
            },
            Either::Right(name) => {
                i.ret(Identifier(name))
            }
        }
    })
}

// == 12.2 Primary Expression ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-primary-expression

enum PrimaryExpression {
    This
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-PrimaryExpression
fn primary_expression<I: U8Input>(i: I, params: &EnumSet<Parameter>) -> SimpleResult<I, PrimaryExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of primary_expression");
    }

    parse!{i;

        let result = (i -> string(i, b"this").map(|_| PrimaryExpression::This)) <|>
        (i -> string(i, b"this").map(|_| PrimaryExpression::This));

        ret result
    }

}

// == 12.2.4 Literals ==

fn literal<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, ()> {
    parse!{i;
        let literal_result = null_literal();

        ret {()}
    }
}

// == 12.2.6 Object Initializer ==

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Initializer
fn initializer<I: U8Input>(i: I, params: &EnumSet<Parameter>) -> SimpleResult<I, ()> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::In) ||
        params.contains(&Parameter::Yield)) {
        panic!("misuse of initializer");
    }


    parse!{i;

        token(b'=');

        let delim_1 = common_delim();

        assignment_expression(params);

        // TODO: token
        ret {()}
    }
}

// == 12.14 Conditional Operator ( ? : ) ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-conditional-operator

// TODO: test
fn conditional_expression<I: U8Input>(i: I, params: &EnumSet<Parameter>) -> SimpleResult<I, ()> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::In) ||
        params.contains(&Parameter::Yield)) {
        panic!("misuse of conditional_expression");
    }

    either(i,
        // left
        |i| parse!{i;

            logical_or_expression(&params);

            let delim_1 = common_delim();
            token(b'?');
            let delim_2 = common_delim();

            let consequent = (i -> {
                let mut params = params.clone();
                params.insert(Parameter::In);
                assignment_expression(i, &params)
            });

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
// http://www.ecma-international.org/ecma-262/7.0/#prod-LogicalANDExpression
fn logical_and_expression<I: U8Input>(i: I, params: &EnumSet<Parameter>) -> SimpleResult<I, ()> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::In) ||
        params.contains(&Parameter::Yield)
        ) {
        panic!("misuse of logical_and_expression");
    }

    parse!{i;

        ret {()}
    }

}

#[derive(Debug)]
enum LogicOrExpression {
    Or(
        Box<LogicOrExpression>,
        Vec<Token>, // common_delim
        /* || */
        Vec<Token>, // common_delim
        Box<LogicOrExpression>
    ),
    Leaf(bool),
    None
}

impl Default for LogicOrExpression {
    fn default() -> Self {
        LogicOrExpression::None
    }
}

impl LogicOrExpression {
    fn add_delim(&mut self, delim_1: Vec<Token>, delim_2: Vec<Token>) {

        match *self {
            LogicOrExpression::None => {
                panic!("invariant violation");
            },
            _ => {}
        }

        let lhs = mem::replace(self, LogicOrExpression::None);

        let new_val = LogicOrExpression::Or(
            Box::new(lhs),
            delim_1,
            /* || */
            delim_2,
            Box::new(LogicOrExpression::None)
        );

        mem::replace(self, new_val);
    }

    fn add_item(&mut self, rhs_val: bool) {

        let rhs = LogicOrExpression::Leaf(rhs_val);

        match *self {
            LogicOrExpression::Leaf(_) => {
                panic!("invariant violation");
            },
            LogicOrExpression::None => {
                mem::replace(self, rhs);
            },
            LogicOrExpression::Or(_, _, _, _) => {
                if let LogicOrExpression::Or(lhs, delim_1, delim_2, _) =
                    mem::replace(self, LogicOrExpression::None) {

                    let new_val = LogicOrExpression::Or(
                        lhs,
                        delim_1,
                        /* || */
                        delim_2,
                        Box::new(rhs)
                    );

                    mem::replace(self, new_val);
                } else {
                    unreachable!();
                }
            }
        }
    }
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LogicalORExpression
fn logical_or_expression<I: U8Input>(i: I, params: &EnumSet<Parameter>) -> SimpleResult<I, LogicOrExpression> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::In) ||
        params.contains(&Parameter::Yield)) {
        panic!("misuse of logical_or_expression");
    }

    type Accumulator = Rc<RefCell<LogicOrExpression>>;

    #[inline]
    fn delimiter<I: U8Input>(i: I, accumulator: Accumulator) -> SimpleResult<I, ()> {
        parse!{i;
            let delim_1 = common_delim();
            let _or = string(b"||");
            let delim_2 = common_delim();
            ret {
                accumulator.borrow_mut().add_delim(delim_1, delim_2);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: I, accumulator: Accumulator| -> SimpleResult<I, ()> {
        parse!{i;
            let rhs = logical_and_expression(params);
            ret {
                accumulator.borrow_mut().add_item(false);
                ()
            }
        }
    };

    parse!{i;

        let line = parse_list(
            delimiter,
            reducer
        );

        ret line
    }

}

#[test]
fn logical_or_expression_test() {

    // TODO: fix
    match parse_only(|i| logical_or_expression(i, &EnumSet::new()), b"a||a ||    a") {
        Ok(result) => {
            println!("{:?}", result);
            assert!(true);
        }
        Err(_) => {
            assert!(true);
        }
    }
}

// == 12.15 Assignment Operators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-assignment-operators

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-AssignmentExpression
fn assignment_expression<I: U8Input>(i: I, params: &EnumSet<Parameter>) -> SimpleResult<I, ()> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::In) ||
        params.contains(&Parameter::Yield)
        ) {
        panic!("misuse of assignment_expression");
    }

    parse!{i;

        conditional_expression(params);

        // TODO: complete

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

// ==== sandbox ===>
// see: https://github.com/m4rw3r/chomp/issues/60

// type ESParseResult<I, T> = ParseResult<I, T, ParseError>;

// fn some_parser<I: U8Input>(i: InputPosition<I, CurrentPosition>)
//     -> ESParseResult<InputPosition<I, CurrentPosition>, ()> {
//     parse!{i;

//         let lol = on_error(
//             |i| string(i, b"var"),
//             |_err, i| {
//                 let loc = i.position();
//                 ParseError::Expected(loc, "Expected var keyword.".to_string())
//             }
//         );

//         // let _var = (i -> {
//         //     string(i, b"var")
//         //         .map_err2(|_, i| {
//         //             let loc = i.position();
//         //             ParseError::Expected(loc, "Expected var here.")
//         //         })
//         // });

//         // ...

//         ret {()}
//     }
// }

// #[test]
// fn some_parser_test() {

//     let i = InputPosition::new(&b"varvar\n/* lol */test a\ntest b\n\ntest c\n"[..], CurrentPosition::new());

//     let r:  Result<(), ParseError> = run_parser(i, |i| parse!{i;
//         some_parser();
//         some_parser();
//         // common_delim();
//         (i -> {
//             common_delim(i)
//             .map_err2(|_, i| {
//                 let loc = i.position();
//                 ParseError::Expected(loc, "Expected var here.".to_string())
//             })
//         });
//         some_parser();
//         ret {()}
//     }).1;

//     match r {
//         Ok(t) => {
//             println!("{:?}", t);
//             assert!(false);
//         }
//         Err(err) => {
//             println!("{}", err);
//             assert!(false);
//         }
//     }
// }
