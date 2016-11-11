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
use chomp::parsers::{SimpleResult, scan, take_till, string, satisfy, take_while1};
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

type U8Error = ChompError<u8>;

// == errors ==

quick_error! {
    #[derive(Debug)]
    pub enum ParseError {
        Expected(loc: CurrentPosition, descr: String) {
            description(descr)
            display("Line {}, Column {}: {}", loc.line(), loc.col(), descr)
        }
        Error {
            // TODO: fix
            description("Error with no description occured")
        }
    }
}

// TODO: remove
// impl From<chomp::parsers::Error<u8>> for ParseError {
//     fn from(_err: chomp::parsers::Error<u8>) -> Self {
//         // TODO: change this later
//         ParseError::Error
//     }
// }

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
fn parse_list<I: U8Input, D, Delim, A, R, Reduced, E>(input: I, delimiter: D, reducer: R) -> ParseResult<I, A, E>
    where D: Fn(I, Rc<RefCell<A>>) -> ParseResult<I, Delim, E>,
          R: Fn(I, Rc<RefCell<A>>) -> ParseResult<I, Reduced, E>,
          A: Default
{

    let accumulator: A = Default::default();
    let initial_accumulator: Rc<RefCell<A>> = Rc::new(RefCell::new(accumulator));

    reducer(input, initial_accumulator.clone())
        .then(|i| {
            either(i,
                |i| parse_list_rest(i, delimiter, initial_accumulator.clone(), reducer),
                |i| i.ret(())
            )
        })
        .map(|_| {
            Rc::try_unwrap(initial_accumulator)
                .ok()
                .unwrap()
                .into_inner()
        })
}

#[inline]
fn parse_list_rest<I: U8Input, D, Delim, A, R, Reduced, E>(input: I, delimiter: D, accumulator: Rc<RefCell<A>>,
    reducer: R) -> ParseResult<I, (), E>
    where D: Fn(I, Rc<RefCell<A>>) -> ParseResult<I, Delim, E>,
          R: Fn(I, Rc<RefCell<A>>) -> ParseResult<I, Reduced, E>,
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

        i -> chomp::parsers::token(i, b'\'');

        let line: Vec<u8> = parse_list(
            // delimiter
            |i, _| string(i, br#"\'"#),
            // reducer
            parse_single_quote_string_reducer

        );

        i -> chomp::parsers::token(i, b'\'');

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

        let line: Vec<u8> = many_till(chomp::parsers::any, parse_single_quote_string_look_ahead);

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
            |i| chomp::parsers::token(i, b'\'').map(|_| ())
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
fn token<I: U8Input>(i: ESInput<I>, tok: I::Token) -> ESParseResult<I, I::Token> {
    on_error(
        i,
        |i| chomp::parsers::token(i, tok),
        |_err, i| {
            let reason = format!("Expected {}", tok);
            ParseError::Expected(i.position(), reason)
        }
    )
}

// TODO: test
#[inline]
fn string_till<I: U8Input, F>(input: ESInput<I>, mut stop_at: F) -> ESParseResult<I, String>
    where F: Fn(ESInput<I>) -> ESParseResult<I, ()> {
    parse!{input;
        let line: Vec<char> = many_till(parse_utf8_char, |i| look_ahead(i, &mut stop_at));

        ret {
            line.into_iter().collect()
        }
    }
}

#[inline]
fn token_as_char<I: U8Input>(i: ESInput<I>, c: u8) -> ESParseResult<I, char> {
    token(i, c)
        .bind(|i, c| {
            i.ret(c as char)
        })
}

// TODO: test
#[inline]
fn parse_utf8_char_of_bytes<I: U8Input>(i: ESInput<I>, needle: &[u8]) -> ESParseResult<I, char> {
    // TODO: refactor this
    on_error(i,
        |i| {
            look_ahead(i, |i| string(i, needle))
                .map_err(|_| ParseError::Error)
                .then(parse_utf8_char)
        },
        |_err, i| {
            let loc = i.position();
            let reason = "Expected utf8 character.".to_string();
            ParseError::Expected(loc, reason)
        }
    )
}

#[inline]
fn parse_utf8_char<I: U8Input>(mut i: ESInput<I>) -> ESParseResult<I, char> {

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

    let loc = i.position();
    let reason = "Expected utf8 character.".to_string();
    return i.err(ParseError::Expected(loc, reason));

}

#[test]
fn parse_utf8_char_test() {

    let sparkle_heart = vec![240, 159, 146, 150];

    let i = InputPosition::new(sparkle_heart.as_slice(), CurrentPosition::new());
    match parse_utf8_char(i).into_inner().1 {
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

    let i = InputPosition::new(sparkle_heart_and_smile.as_slice(), CurrentPosition::new());
    match parse_utf8_char(i).into_inner().1 {
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
enum CommonDelim {
    WhiteSpace(char),
    LineTerminator(char),
    Comment(Comment)
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
fn __common_delim<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, CommonDelim> {
    on_error(i,
        |i| -> ESParseResult<I, CommonDelim> {parse!{i;
            let delim =
                (i -> whitespace(i).map(|w| {
                    let WhiteSpace(w) = w;
                    CommonDelim::WhiteSpace(w)
                })) <|>
                (i -> line_terminator(i).map(|w| {
                    let LineTerminator(w) = w;
                    CommonDelim::LineTerminator(w)
                })) <|>
                (i -> comment(i).map(|c| CommonDelim::Comment(c)));
            ret delim
        }},
        |_err, i| {
            let loc = i.position();
            let reason = "Expected whitespace, line terminator, or comment.".to_string();
            ParseError::Expected(loc, reason)
        }
    )
}

#[inline]
fn common_delim<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Vec<CommonDelim>> {
    many(i, __common_delim)
}

#[inline]
fn common_delim_required<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Vec<CommonDelim>> {
    many1(i, __common_delim)
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

struct WhiteSpace(char);

// http://www.ecma-international.org/ecma-262/7.0/#prod-WhiteSpace
fn whitespace<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, WhiteSpace> {

    #[inline]
    fn other_whitespace<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, char> {
        parse_utf8_char(i)
            .bind(|i, c: char| {
                if c.is_whitespace() {
                    i.ret(c)
                } else {
                    let loc = i.position();
                    let reason = "Expected whitespace.".to_string();
                    i.err(ParseError::Expected(loc, reason))
                }
            })
    }

    on_error(
        i,
        |i| -> ESParseResult<I, WhiteSpace> {parse!{i;

            let whitespace_char =
                parse_utf8_char_of_bytes(b"\x0009") <|> // <TAB>; CHARACTER TABULATION
                parse_utf8_char_of_bytes(b"\x000B") <|> // <VT>; LINE TABULATION
                parse_utf8_char_of_bytes(b"\x000C") <|> // <FF>; FORM FEED (FF)
                parse_utf8_char_of_bytes(b"\x0020") <|> // <SP>; SPACE
                parse_utf8_char_of_bytes(b"\x00A0") <|> // <NBSP>; NO-BREAK SPACE
                parse_utf8_char_of_bytes(b"\xFEFF") <|> // <ZWNBSP>; ZERO WIDTH NO-BREAK SPACE
                other_whitespace(); // Any other Unicode "Separator, space" code point

            ret WhiteSpace(whitespace_char)
        }},
        |_, i| {
            ParseError::Expected(i.position(), "Expected whitespace.".to_string())
        }
    )


}

// == 11.3 Line Terminators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-line-terminators

struct LineTerminator(char);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LineTerminator
fn line_terminator<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, LineTerminator> {
    on_error(i,
        |i| -> ESParseResult<I, LineTerminator> {parse!{i;

            let line_terminator_char =
                parse_utf8_char_of_bytes(b"\x000A") <|> // <LF>; LINE FEED (LF)
                parse_utf8_char_of_bytes(b"\x000D") <|> // <CR>; CARRIAGE RETURN (CR)
                parse_utf8_char_of_bytes(b"\x2028") <|> // <LS>; LINE SEPARATOR
                parse_utf8_char_of_bytes(b"\x2029");    // <PS>; PARAGRAPH SEPARATOR

            ret LineTerminator(line_terminator_char)
        }},
        |_err, i| {
            let loc = i.position();
            let reason = "Expected utf8 character.".to_string();
            ParseError::Expected(loc, reason)
        }
    )
}

struct LineTerminatorSequence(String);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LineTerminatorSequence
fn line_terminator_seq<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, LineTerminatorSequence> {

    #[inline]
    fn char_to_string(c: char) -> String {
        let mut s = String::with_capacity(1);
        s.push(c);
        s
    }

    on_error(i,
        |i| -> ESParseResult<I, LineTerminatorSequence> {parse!{i;

            let seq =
                (i -> parse_utf8_char_of_bytes(i, b"\x000A").map(char_to_string)) <|> // <LF>; LINE FEED (LF)
                (i -> {
                    parse!{i;
                        let cr = parse_utf8_char_of_bytes(b"\x000D");
                        let lf = parse_utf8_char_of_bytes(b"\x000A");
                        ret {
                            let mut s = String::with_capacity(2);
                            s.push(cr);
                            s.push(lf);
                            s
                        }
                    }
                }) <|>                                                                // <CR><LF>
                (i -> parse_utf8_char_of_bytes(i, b"\x000D").map(char_to_string)) <|> // <CR>; CARRIAGE RETURN (CR)
                (i -> parse_utf8_char_of_bytes(i, b"\x2028").map(char_to_string)) <|> // <LS>; LINE SEPARATOR
                (i -> parse_utf8_char_of_bytes(i, b"\x2029").map(char_to_string));    // <PS>; PARAGRAPH SEPARATOR

            ret LineTerminatorSequence(seq)
        }},
        |_err, i| {
            let loc = i.position();
            let reason = "Expected linte terminator sequence.".to_string();
            ParseError::Expected(loc, reason)
        }
    )
}

// == 11.4 Comments ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-comments

#[derive(Debug)]
enum Comment {
    MultiLineComment(String),
    SingleLineComment(String)
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Comment
fn comment<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Comment> {

    // http://www.ecma-international.org/ecma-262/7.0/#prod-MultiLineComment
    #[inline]
    fn multiline_comment<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Comment> {

        const END: &'static [u8; 2] = b"*/";

        #[inline]
        fn stop_at<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
            on_error(
                i,
                |i| string(i, END).map(|_| ()),
                |_err, i| {
                    let loc = i.position();
                    ParseError::Expected(loc, "Expected */.".to_string())
                }
            )
        }

        // TODO: verify production rule satisfaction
        // http://www.ecma-international.org/ecma-262/7.0/#prod-MultiLineCommentChars

        parse!{i;
            on_error(
                |i| string(i, b"/*"),
                |_err, i| {
                    let loc = i.position();
                    ParseError::Expected(loc, "Expected /* for multi-line comment.".to_string())
                }
            );
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
            on_error(
                |i| string(i, b"//"),
                |_err, i| {
                    let loc = i.position();
                    ParseError::Expected(loc, "Expected // for single-line comment.".to_string())
                }
            );
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

// == 11.6 Names and Keywords ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-names-and-keywords

struct IdentifierName(String);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierName
fn identifier_name<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, IdentifierName> {

    on_error(
        i,
        |i| -> ESParseResult<I, IdentifierName> {
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
        },
        |_err, i| {
            let reason = format!("Invalid identifier.");
            ParseError::Expected(i.position(), reason)
        }
    )


}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierStart
fn identifier_start<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, char> {

    #[inline]
    fn identifier_start_unicode<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, char> {
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
fn identifier_part<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, char> {

    #[inline]
    fn identifier_part_unicode<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, char> {
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
fn unicode_id_start<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, char> {
    parse_utf8_char(i)
        .bind(|i, c: char| {
            if c.is_xid_start() {
                i.ret(c)
            } else {
                // TODO: better error
                let loc = i.position();
                let reason = format!("Invalid utf8 character.");
                i.err(ParseError::Expected(loc, reason))
            }
        })
}

#[test]
fn unicode_id_start_test() {

    let i = InputPosition::new("a".as_bytes(), CurrentPosition::new());
    match unicode_id_start(i).into_inner().1 {
        Ok(result) => {
            assert_eq!(result, 'a');
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

// http://www.ecma-international.org/ecma-262/7.0/#prod-UnicodeIDContinue
fn unicode_id_continue<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, char> {
    parse_utf8_char(i)
        .bind(|i, c: char| {

            if c.is_xid_continue() {
                i.ret(c)
            } else {
                // TODO: better error
                let loc = i.position();
                let reason = format!("Invalid utf8 character: `{}`", c);
                i.err(ParseError::Expected(loc, reason))
            }

        })
}

#[test]
fn unicode_id_continue_test() {

    let success: Vec<&str> = vec!["a", "1", "_"];

    for input in success {
        let i = InputPosition::new(input.as_bytes(), CurrentPosition::new());
        match unicode_id_continue(i).into_inner().1 {
            Ok(result) => {
                assert_eq!(result, input.chars().next().unwrap());
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

// == 11.6.2 Reserved Words ==

// TODO: enum Keyword type

// http://www.ecma-international.org/ecma-262/7.0/#sec-reserved-words
fn reserved_word<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, I::Buffer> {

    #[inline]
    fn string_not_utf8<I: U8Input>(i: ESInput<I>, needle: &[u8]) -> ESParseResult<I, I::Buffer> {

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
                            // NOTE: Reserved keyword must not contain escaped characters.
                            i.err(ParseError::Error)
                        },
                        Either::Right(c) => {

                            let mut buf = String::with_capacity(1);
                            buf.push(c);
                            let bytes = buf.as_bytes();

                            if current_needle.starts_with(bytes) {
                                current_needle = current_needle.split_at(bytes.len()).1;
                                i.ret(Either::Right(c))
                            } else {
                                i.err(ParseError::Error)
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
        .then(|i| {
            on_error(
                i,
                |mut i| -> ESParseResult<I, I::Buffer> {
                    let res = (&mut i).consume_from(mark);
                    i.ret(res)
                },
                |_, i| {
                    let reason = format!("Expected keyword {}.", std::str::from_utf8(needle).unwrap());
                    ParseError::Expected(i.position(), reason)
                }
            )
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

    let i = InputPosition::new("var".as_bytes(), CurrentPosition::new());
    match reserved_word(i).into_inner().1 {
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
        let i = InputPosition::new(fail.as_bytes(), CurrentPosition::new());
        match reserved_word(i).into_inner().1 {
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
        |i| {
            either(i,
                // left
                |i| string(i, b"true"),
                // right
                |i| string(i, b"false")
            )
            .bind::<_, _, U8Error>(|i, result| {
                match result {
                    Either::Left(_left) => {
                        let _left: I::Buffer = _left;
                        i.ret(Bool::True)
                    },
                    Either::Right(_left) => {
                        let _left: I::Buffer = _left;
                        i.ret(Bool::False)
                    }
                }
            })
        },
        |_err, i| {
            let loc = i.position();
            ParseError::Expected(loc, "Expected boolean literal.".to_string())
        }
    )
}

// == 11.8.3 Numeric Literals ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-literals-numeric-literals

enum NumericLiteral {
    Decimal(DecimalLiteral),
    BinaryInteger(BinaryDigits),
    OctalInteger(OctalDigits),
    HexInteger(HexDigits)
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-NumericLiteral
fn numeric_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, NumericLiteral> {
    parse!{i;

        let result =
            (i -> decimal_literal(i).map(|x| NumericLiteral::Decimal(x))) <|>
            (i -> binary_integer_literal(i).map(|x| {
                let BinaryIntegerLiteral(x) = x;
                NumericLiteral::BinaryInteger(x)
            })) <|>
            (i -> octal_integer_literal(i).map(|x| {
                let OctalIntegerLiteral(x) = x;
                NumericLiteral::OctalInteger(x)
            })) <|>
            (i -> hex_integer_literal(i).map(|x| {
                let HexIntegerLiteral(x) = x;
                NumericLiteral::HexInteger(x)
            }));

        ret result
    }
}

enum DecimalLiteral {
    WholeFractionDecimal(DecimalIntegerLiteral, /* . */ Option<DecimalDigits>, Option<ExponentPart>),
    FractionDecimal(/* . */ DecimalDigits, Option<ExponentPart>),
    WholeDecimal(DecimalIntegerLiteral, Option<ExponentPart>)
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-DecimalLiteral
fn decimal_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, DecimalLiteral> {
    or(i,
        |i| parse!{i;

            let whole = decimal_integer_literal();
            token(b'.');
            let fraction = option(|i| decimal_digits(i).map(|c| Some(c)), None);
            let exp_part = option(|i| exponent_part(i).map(|c| Some(c)), None);

            ret DecimalLiteral::WholeFractionDecimal(whole, fraction, exp_part)
        },
        |i| or(i,
            |i| parse!{i;

                token(b'.');
                let fraction = decimal_digits();
                let exp_part = option(|i| exponent_part(i).map(|c| Some(c)), None);

                ret DecimalLiteral::FractionDecimal(fraction, exp_part)
            },
            |i| parse!{i;

                let whole = decimal_integer_literal();
                let exp_part = option(|i| exponent_part(i).map(|c| Some(c)), None);

                ret DecimalLiteral::WholeDecimal(whole, exp_part)
            }
        ))
}

struct DecimalIntegerLiteral(DecimalDigits);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-DecimalIntegerLiteral
fn decimal_integer_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, DecimalIntegerLiteral> {
    either(i,
        // left
        |i| token(i, b'0'),
        // right
        |i| parse!{i;
            // TODO: optimize this
            let prefix = non_zero_digit();
            let suffix = decimal_digits();
            ret {
                let DecimalDigits(suffix) = suffix;
                let mut s = String::with_capacity(suffix.len() + 1);
                s.push(prefix as char);
                s.push_str(&suffix);
                DecimalDigits(s)
            }
        }
    )
    .bind(|i, result| {
        match result {
            Either::Left(c) => {
                let mut s = String::with_capacity(1);
                s.push(c as char);
                i.ret(DecimalIntegerLiteral(DecimalDigits(s)))
            },
            Either::Right(dd) => {
                i.ret(DecimalIntegerLiteral(dd))
            }
        }
    })
}

struct DecimalDigits(String);

impl MathematicalValue for DecimalDigits {
    // TODO: test
    fn mathematical_value(&self) -> i64 {
        i64::from_str_radix(&self.0, 10)
            .unwrap()
    }
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-DecimalDigits
fn decimal_digits<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, DecimalDigits> {
    on_error(
        i,
        |i| -> ESParseResult<I, DecimalDigits> {
            many1(i, decimal_digit)
                .bind(|i, buf: Vec<u8>| {
                    let contents = String::from_utf8_lossy(&buf).into_owned();
                    i.ret(DecimalDigits(contents))
                })
        },
        |_, i| {
            let loc = i.position();
            ParseError::Expected(loc, "Expected decimal digit (0 or 9).".to_string())
        }
    )
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-DecimalDigit
fn decimal_digit<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, u8> {

    #[inline]
    fn is_decimal_digit(c: u8) -> bool {
        (b'0' <= c && c <= b'9')
    }

    on_error(
        i,
        |i| satisfy(i, is_decimal_digit),
        |_err, i| {
            let loc = i.position();
            ParseError::Expected(loc, "Expected decimal digit (0 to 9).".to_string())
        }
    )
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-NonZeroDigit
fn non_zero_digit<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, u8> {

    #[inline]
    fn is_non_zero_digit(c: u8) -> bool {
        (b'1' <= c && c <= b'9')
    }

    on_error(
        i,
        |i| satisfy(i, is_non_zero_digit),
        |_err, i| {
            let loc = i.position();
            ParseError::Expected(loc, "Expected non-zero digit (1 to 9).".to_string())
        }
    )
}

struct ExponentPart(SignedInteger);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ExponentPart
fn exponent_part<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ExponentPart> {
    parse!{i;
        // http://www.ecma-international.org/ecma-262/7.0/#prod-ExponentIndicator
        token(b'e') <|> token(b'E');
        let result = signed_integer();
        ret ExponentPart(result)
    }
}

enum SignedInteger {
    Unsigned(DecimalDigits),
    Positive(DecimalDigits),
    Negative(DecimalDigits)
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-SignedInteger
fn signed_integer<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, SignedInteger> {

    enum Signed {
        Unsigned,
        Positive,
        Negative
    }

    parse!{i;

        let prefix = option(|i| parse!{i;
            let signed = (i -> token(i, b'+').map(|_| Signed::Positive)) <|>
            (i -> token(i, b'-').map(|_| Signed::Negative));
            ret signed
        }, Signed::Unsigned);

        let result = decimal_digits();

        ret {
            match prefix {
                Signed::Unsigned => SignedInteger::Unsigned(result),
                Signed::Positive => SignedInteger::Positive(result),
                Signed::Negative => SignedInteger::Negative(result)
            }
        }
    }
}

struct BinaryIntegerLiteral(BinaryDigits);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BinaryIntegerLiteral
fn binary_integer_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, BinaryIntegerLiteral> {
    parse!{i;
        token(b'0');
        token(b'b') <|> token(b'B');
        let result = binary_digits();
        ret BinaryIntegerLiteral(result)
    }
}

struct BinaryDigits(String);

impl MathematicalValue for BinaryDigits {
    // TODO: test
    fn mathematical_value(&self) -> i64 {
        i64::from_str_radix(&self.0, 2)
            .unwrap()
    }
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BinaryDigits
fn binary_digits<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, BinaryDigits> {
    on_error(
        i,
        |i| -> ESParseResult<I, BinaryDigits> {
            many1(i, binary_digit)
                .bind(|i, buf: Vec<u8>| {
                    let contents = String::from_utf8_lossy(&buf).into_owned();
                    i.ret(BinaryDigits(contents))
                })
        },
        |_, i| {
            let loc = i.position();
            ParseError::Expected(loc, "Expected binary digit (0 or 1).".to_string())
        }
    )
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BinaryDigit
#[inline]
fn binary_digit<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, u8> {

    #[inline]
    fn is_binary_digit(c: u8) -> bool {
        (b'0' <= c && c <= b'1')
    }

    on_error(
        i,
        |i| satisfy(i, is_binary_digit),
        |_err, i| {
            let loc = i.position();
            ParseError::Expected(loc, "Expected binary digit (0 or 1).".to_string())
        }
    )

}

struct OctalIntegerLiteral(OctalDigits);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-OctalIntegerLiteral
fn octal_integer_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, OctalIntegerLiteral> {
    parse!{i;
        token(b'0');
        token(b'o') <|> token(b'O');
        let result = octal_digits();
        ret OctalIntegerLiteral(result)
    }
}

struct OctalDigits(String);

impl MathematicalValue for OctalDigits {
    // TODO: test
    fn mathematical_value(&self) -> i64 {
        i64::from_str_radix(&self.0, 8)
            .unwrap()
    }
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-OctalDigits
fn octal_digits<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, OctalDigits> {
    on_error(
        i,
        |i| -> ESParseResult<I, OctalDigits> {
            many1(i, octal_digit)
                .bind(|i, buf: Vec<u8>| {
                    let contents = String::from_utf8_lossy(&buf).into_owned();
                    i.ret(OctalDigits(contents))
                })
        },
        |_, i| {
            let loc = i.position();
            ParseError::Expected(loc, "Expected octal digit (0 to 7).".to_string())
        }
    )
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-OctalDigit
#[inline]
fn octal_digit<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, u8> {

    #[inline]
    fn is_octal_digit(c: u8) -> bool {
        (b'0' <= c && c <= b'7')
    }

    on_error(
        i,
        |i| satisfy(i, is_octal_digit),
        |_err, i| {
            let loc = i.position();
            ParseError::Expected(loc, "Expected octal digit (0 to 7).".to_string())
        }
    )

}

struct HexIntegerLiteral(HexDigits);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-HexIntegerLiteral
fn hex_integer_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, HexIntegerLiteral> {
    parse!{i;
        token(b'0');
        token(b'x') <|> token(b'X');
        let result = hex_digits();
        ret HexIntegerLiteral(result)
    }
}

struct HexDigits(String);

impl MathematicalValue for HexDigits {
    // TODO: test
    fn mathematical_value(&self) -> i64 {
        i64::from_str_radix(&self.0, 16)
            .unwrap()
    }
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-HexDigits
fn hex_digits<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, HexDigits> {
    on_error(
        i,
        |i| -> ESParseResult<I, HexDigits> {
            many1(i, hex_digit)
                .bind(|i, buf: Vec<u8>| {
                    let contents = String::from_utf8_lossy(&buf).into_owned();
                    i.ret(HexDigits(contents))
                })
        },
        |_, i| {
            let loc = i.position();
            ParseError::Expected(loc, "Expected hex digit.".to_string())
        }
    )
}

#[test]
fn hex_digits_test() {

    let i = InputPosition::new(&b"e"[..], CurrentPosition::new());
    match hex_digits(i).into_inner().1 {
        Ok(result) => {
            let HexDigits(result) = result;
            assert_eq!(&result, "e");
        }
        Err(_) => {
            assert!(false);
        }
    }

    let i = InputPosition::new(&b"ad"[..], CurrentPosition::new());
    match hex_digits(i).into_inner().1 {
        Ok(result) => {
            let HexDigits(result) = result;
            assert_eq!(&result, "ad");
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

// http://www.ecma-international.org/ecma-262/7.0/#prod-HexDigit
#[inline]
fn hex_digit<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, u8> {

    #[inline]
    fn is_hex_digit(c: u8) -> bool {
        (b'0' <= c && c <= b'9') ||
        (b'a' <= c && c <= b'f') ||
        (b'A' <= c && c <= b'F')
    }

    on_error(
        i,
        |i| satisfy(i, is_hex_digit),
        |_err, i| {
            let loc = i.position();
            ParseError::Expected(loc, "Expected hex digit (0 to F).".to_string())
        }
    )
}

// == 11.8.3.1 Static Semantics: MV ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-static-semantics-mv

trait MathematicalValue {
    fn mathematical_value(&self) -> i64;
}

// == 11.8.4 String Literals ==

enum StringLiteral {
    SingleQuoted(String),
    DoubleQuoted(String)
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-StringLiteral
fn string_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, StringLiteral> {
    parse!{i;
        let quoted_string =
        (i -> __string_literal(i, b'\'').map(|s| StringLiteral::SingleQuoted(s))) <|>
        (i -> __string_literal(i, b'\"').map(|s| StringLiteral::DoubleQuoted(s)));
        ret quoted_string
    }
}

// TODO: test
#[inline]
fn __string_literal<I: U8Input>(i: ESInput<I>, quote_type: u8) -> ESParseResult<I, String> {

    #[inline]
    fn string_char<I: U8Input>(i: ESInput<I>, quote_type: u8) -> ESParseResult<I, String> {
        either(i,
            |i| parse!{i;
                token(b'\\');
                token(quote_type);
                ret {
                    (quote_type as char).to_string()
                }
            },
            parse_utf8_char
        )
        .bind(|i, result| {
            match result {
                Either::Left(escaped) => {
                    i.ret(escaped)
                },
                Either::Right(c) => {
                    if c == (quote_type as char) {
                        i.err(ParseError::Error)
                    } else {
                        i.ret(c.to_string())
                    }
                }
            }
        })
    }

    parse!{i;
        token(quote_type);
        let s: Vec<String> = many(|i| string_char(i, quote_type));
        token(quote_type);

        ret {
            s
            .iter()
            .fold(String::new(), |mut acc, s| {
                acc.push_str(&s);
                acc
            })
        }
    }
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-HexEscapeSequence
fn hex_escape_seq<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, char> {
    parse!{i;
        token(b'x');
        let digit_1 = hex_digit();
        let digit_2 = hex_digit();

        ret {
            let mut result = String::with_capacity(2);
            result.push(digit_1 as char);
            result.push(digit_2 as char);
            string_to_unicode_char(&result).unwrap()
        }
    }
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-UnicodeEscapeSequence
// TODO: needs test
fn unicode_escape_seq<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, char> {
    either(i,
        |i| -> ESParseResult<I, HexDigits> {parse!{i;
            // e.g. u{9A9A}
            token(b'u');
            token(b'{');
            let sequence = hex_digits();
            token(b'}');
            ret sequence
        }},
        |i| -> ESParseResult<I, char> {parse!{i;
            // e.g. u9A9A
            token(b'u');
            let sequence = hex_4_digits();
            ret {
                string_to_unicode_char(&sequence).unwrap()
            }
        }}
    )
    .bind(|i, result| {
        match result {
            Either::Left(sequence) => {
                // == 11.8.4.1 Static Semantics: Early Errors ==
                //
                // http://www.ecma-international.org/ecma-262/7.0/#sec-string-literals-static-semantics-early-errors
                if (
                        sequence.0.chars().next().unwrap() != '0' &&
                        sequence.0.len() > 6) ||
                    sequence.mathematical_value() > 1114111 /* 10ffff */ {

                    let err_val = ParseError::Expected(i.position(),
                        "Invalid unicode escape sequence. Expect to be less or equal to 10ffff.".to_string());

                    i.err(err_val)
                } else {
                    let HexDigits(sequence) = sequence;
                    let c = string_to_unicode_char(&sequence).unwrap();
                    i.ret(c)
                }
            },
            Either::Right(c) => {
                i.ret(c)
            }
        }
    })
}

fn escaped_unicode_escape_seq<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, char> {
    token(i, b'\\')
        .then(unicode_escape_seq)
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-Hex4Digits
fn hex_4_digits<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, String> {
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
    let i = InputPosition::new(&b"adad"[..], CurrentPosition::new());
    match hex_4_digits(i).into_inner().1 {
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
    Identifier(Identifier),
    Yield
}

#[inline]
fn yield_keyword<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, I::Buffer> {
    on_error(
        i,
        |i| string(i, b"yield"),
        |_err, i| {
            let reason = format!("Expected yield keyword.");
            ParseError::Expected(i.position(), reason)
        }
    )
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierReference
fn identifier_reference<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, IdentifierReference> {

    if !params.contains(&Parameter::Yield) {

        let result = either(i,
            // left
            yield_keyword,
            // right
            identifier
        )
        .bind(|i, result| {
            match result {
                Either::Left(_) => {
                    // TODO: fix
                    i.ret(IdentifierReference::Yield)
                },
                Either::Right(ident) => {
                    i.ret(IdentifierReference::Identifier(ident))
                }
            }
        });

        return result;
    }

    if params.len() >= 2 {
        panic!("misuse of identifier_reference");
    }

    identifier(i).map(|ident| {
        IdentifierReference::Identifier(ident)
    })

}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BindingIdentifier
fn binding_identifier<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, ()> {

    if !params.contains(&Parameter::Yield) {

        let result = either(i,
            // left
            |i| parse!{i;

                yield_keyword();

                // TODO: token
                ret {()}
            },
            // right
            identifier
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

    identifier(i).map(|_| ())

}

struct Identifier(String);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Identifier
fn identifier<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Identifier> {
    either(i,
        |i| reserved_word(i),  // left
        |i| identifier_name(i) // right
    )
    .bind(|i, result| {
        match result {
            Either::Left(_) => {
                let loc = i.position();
                let reason = format!("Reserved keyword may not be used as an identifier.");
                i.err(ParseError::Expected(loc, reason))
            },
            Either::Right(name) => {
                let IdentifierName(name) = name;
                i.ret(Identifier(name))
            }
        }
    })
}

// == 12.2 Primary Expression ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-primary-expression

enum PrimaryExpression {
    This,
    IdentifierReference(IdentifierReference),
    Literal(Literal),
    ArrayLiteral(ArrayLiteral)
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-PrimaryExpression
fn primary_expression<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, PrimaryExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of primary_expression");
    }

    parse!{i;

        let result =

            on_error(
                |i| string(i, b"this").map(|_| PrimaryExpression::This),
            |_err, i| {
                let reason = format!("Expected this keyword.");
                ParseError::Expected(i.position(), reason)
            })

            <|>

            (i -> identifier_reference(i, &params)
                .map(|ident_ref| PrimaryExpression::IdentifierReference(ident_ref)))

            <|>

            (i -> literal(i).map(|literal| PrimaryExpression::Literal(literal)))

            <|>

            (i -> array_literal(i, &params).map(|arr_literal| PrimaryExpression::ArrayLiteral(arr_literal)));

        ret result
    }

}

// == 12.2.4 Literals ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-primary-expression-literals

enum Literal {
    Null,
    Boolean(Bool),
    Numeric(NumericLiteral),
    String(StringLiteral)
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Literal
fn literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Literal> {
    parse!{i;
        let literal_result =
        (i -> null_literal(i).map(|_| Literal::Null)) <|>
        (i -> boolean_literal(i).map(|b| Literal::Boolean(b))) <|>
        (i -> numeric_literal(i).map(|n| Literal::Numeric(n))) <|>
        (i -> string_literal(i).map(|s| Literal::String(s)));
        ret literal_result
    }
}

// == 12.2.5 Array Initializer ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-array-initializer

struct ArrayLiteral(/* [ (left bracket) */ Vec<CommonDelim>, ArrayLiteralContents, Vec<CommonDelim> /* ] (right bracket) */);

enum ArrayLiteralContents {
    Empty(Option<Elision>),
    List(ElementList),
    ListWithElision(ElementList, Vec<CommonDelim>, Elision)
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ArrayLiteral
fn array_literal<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, ArrayLiteral> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::Yield)) {
        panic!("misuse of array_literal");
    }

    #[inline]
    fn array_literal_contents<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, ArrayLiteralContents> {
        parse!{i;

            // [ElementList_[?Yield]]
            // [ElementList_[?Yield] , Elision_opt]

            let list = element_list(&params);

            let maybe_end = option(|i| parse!{i;

                on_error(
                    |i| token(i, b','),
                    |_err, i| {
                        let loc = i.position();
                        // TODO: proper err message?
                        ParseError::Expected(loc, "Expected , delimeter here.".to_string())
                    }
                );

                let delim = common_delim();
                let elision = elision();

                ret Some((delim, elision))

            }, None);

            ret {
                match maybe_end {
                    None => ArrayLiteralContents::List(list),
                    Some((delim, elision)) => ArrayLiteralContents::ListWithElision(list, delim, elision),
                }
            }
        }
    }

    parse!{i;

        token(b'[');
        let delim_left = common_delim();

        let contents = option(|i| elision(i).map(|x| ArrayLiteralContents::Empty(Some(x))),
            ArrayLiteralContents::Empty(None)) <|>
            array_literal_contents(&params);

        let delim_right = common_delim();
        token(b']');

        ret ArrayLiteral(delim_left, contents, delim_right)
    }
}

struct ElementList(Vec<ElementListItem>);

enum ElementListItem {
    Delim(Vec<CommonDelim>, /* , (comma) */ Vec<CommonDelim>),
    ItemExpression(()),
    ItemSpread(()),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ElementList
fn element_list<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, ElementList> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::Yield)) {
        panic!("misuse of element_list");
    }

    type Accumulator = Rc<RefCell<Vec<ElementListItem>>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            on_error(
                |i| token(i, b','),
                |_err, i| {
                    let loc = i.position();
                    // TODO: proper err message?
                    ParseError::Expected(loc, "Expected , delimeter for array.".to_string())
                }
            );

            let delim_2 = common_delim();

            ret {
                accumulator.borrow_mut().push(ElementListItem::Delim(delim_1, delim_2));
                ()
            }
        }
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;

            let l = option(|i| elision(i).map(|x| Some(x)), None);

            let item = (i -> {

                let mut params = params.clone();
                params.insert(Parameter::In);

                assignment_expression(i, &params).map(|x| ElementListItem::ItemExpression(x))
            }) <|>
            (i -> spread_element(i, &params).map(|x| {
                let SpreadElement(x) = x;
                ElementListItem::ItemSpread(x)
            }));

            ret {
                accumulator.borrow_mut().push(item);
                ()
            }
        }
    };

    parse!{i;

        let list = parse_list(
            delimiter,
            reducer
        );

        ret ElementList(list)
    }

}

struct Elision(Vec<ElisionItem>);

enum ElisionItem {
    CommonDelim(Vec<CommonDelim>),
    Comma
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Elision
fn elision<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Elision> {
    parse!{i;

        token(b',');

        let list: Vec<ElisionItem> = many(|i| parse!{i;
            let l = (i -> common_delim(i).map(|c| ElisionItem::CommonDelim(c))) <|>
            (i -> token(i, b',').map(|_| ElisionItem::Comma));
            ret l
        });

        ret Elision(list)
    }
}

struct SpreadElement(());

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-SpreadElement
fn spread_element<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, SpreadElement> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::Yield)) {
        panic!("misuse of spread_element");
    }

    parse!{i;

        // spread operator
        (i -> string(i, b"...").map_err(|_| ParseError::Error));

        common_delim();

        let expr = (i -> {
            let mut params = params.clone();
            params.insert(Parameter::In);
            assignment_expression(i, &params)
        });

        ret SpreadElement(expr)
    }
}

// == 12.2.6 Object Initializer ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-object-initializer

// TODO: complete
struct ObjectLiteral(/* { (left curly bracket) */ Vec<CommonDelim>, ObjectLiteralContents,
    Vec<CommonDelim> /* } (right curly bracket) */);

enum ObjectLiteralContents {
    FooBar
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ObjectLiteral
fn object_literal<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, ObjectLiteral> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::Yield)) {
        panic!("misuse of object_literal");
    }

    parse!{i;

        token(b'{');
        let delim_left = common_delim();

        // TODO: contents

        let delim_right = common_delim();
        token(b'}');

        ret ObjectLiteral(delim_left, ObjectLiteralContents::FooBar, delim_right)
    }
}

// TODO: complete
// http://www.ecma-international.org/ecma-262/7.0/#prod-PropertyDefinitionList

// TODO: complete
// http://www.ecma-international.org/ecma-262/7.0/#prod-PropertyName

// TODO: complete
// http://www.ecma-international.org/ecma-262/7.0/#prod-LiteralPropertyName

// TODO: complete

struct ComputedPropertyName(Vec<CommonDelim>, (), Vec<CommonDelim>);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ComputedPropertyName
fn computed_property_name<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, ComputedPropertyName> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::Yield)) {
        panic!("misuse of computed_property_name");
    }

    let mut params = params.clone();
    params.insert(Parameter::In);

    parse!{i;

        token(b'[');
        let delim_left = common_delim();

        let expr = assignment_expression(&params);

        let delim_right = common_delim();
        token(b']');

        ret ComputedPropertyName(delim_left, expr, delim_right)
    }
}

struct CoverInitializedName(IdentifierReference, Vec<CommonDelim>, Initializer);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-CoverInitializedName
fn cover_initialized_name<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, CoverInitializedName> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::Yield)) {
        panic!("misuse of cover_initialized_name");
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

struct Initializer(Vec<CommonDelim>, ());

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Initializer
fn initializer<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, Initializer> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::In) ||
        params.contains(&Parameter::Yield)) {
        panic!("misuse of initializer");
    }

    parse!{i;

        token(b'=');

        let delim = common_delim();

        let expr = assignment_expression(params);

        ret Initializer(delim, expr)
    }
}

// == 12.14 Conditional Operator ( ? : ) ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-conditional-operator

// TODO: test
fn conditional_expression<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, ()> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::In) ||
        params.contains(&Parameter::Yield)) {
        panic!("misuse of conditional_expression");
    }

    either(i,
        // left
        |i| -> ESParseResult<I, ()> {parse!{i;

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

        }},
        // right
        |i| -> ESParseResult<I, ()> {parse!{i;

            logical_or_expression(&params);

            // TODO: token
            ret {()}
        }}
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
fn logical_and_expression<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, ()> {

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
        Vec<CommonDelim>, // common_delim
        /* || */
        Vec<CommonDelim>, // common_delim
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
    fn add_delim(&mut self, delim_1: Vec<CommonDelim>, delim_2: Vec<CommonDelim>) {

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
fn logical_or_expression<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>)
    -> ESParseResult<I, LogicOrExpression> {

    // validation
    if !(params.is_empty() ||
        params.contains(&Parameter::In) ||
        params.contains(&Parameter::Yield)) {
        panic!("misuse of logical_or_expression");
    }

    type Accumulator = Rc<RefCell<LogicOrExpression>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;
            let delim_1 = common_delim();
            let _or = on_error(
                |i| string(i, b"||"),
                |_err, i| {
                    let loc = i.position();
                    ParseError::Expected(loc, "Expected || operator.".to_string())
                }
            );
            let delim_2 = common_delim();
            ret {
                accumulator.borrow_mut().add_delim(delim_1, delim_2);
                ()
            }
        }
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
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

    // TODO: fix with actual test case
    let i = InputPosition::new(&b"a||a ||    a"[..], CurrentPosition::new());
    match logical_or_expression(i, &EnumSet::new()).into_inner().1 {
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
fn assignment_expression<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, ()> {

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
fn variable_statement<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
    parse!{i;

        let _var = on_error(
            |i| string(i, b"var"),
            |_err, i| {
                let loc = i.position();
                ParseError::Expected(loc, "Expected var keyword.".to_string())
            }
        );

        let delim_1 = common_delim_required();

        // TODO: var declaration list
        // sep_by(decimal, |i| token(i, b';'))

        semicolon();

        ret {()}
    }
}


// http://www.ecma-international.org/ecma-262/7.0/#prod-VariableDeclaration
fn variable_declaration<I: U8Input>(i: ESInput<I>, maybe_params: &Option<Parameter>) -> ESParseResult<I, ()> {
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
fn semicolon<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
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
