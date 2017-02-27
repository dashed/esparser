#![recursion_limit="1000"]
#![feature(unicode)]
// == crates ==
#[macro_use]
extern crate chomp;
extern crate enum_set;

// == rust std imports ==

use std::mem;
use std::rc::Rc;
use std::cell::RefCell;

// == 3rd-party imports ==

use chomp::run_parser;
use chomp::parsers::{SimpleResult, scan, take_till, satisfy, take_while1};
use chomp::combinators::{option, look_ahead, many_till, many1, many, or, either};
use chomp::types::{Buffer, Input, ParseResult, U8Input};
use chomp::parse_only;
use chomp::parsers::Error as ChompError;
use chomp::primitives::Primitives;
use chomp::prelude::Either;
use chomp::types::numbering::{InputPosition, LineNumber, Numbering};
use chomp::primitives::IntoInner;

use enum_set::{EnumSet, CLike};

// TODO: remove this comment after stable implementation
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
type ESParseResult<I, T> = ParseResult<ESInput<I>, T, ErrorChain>;

type U8Error = ChompError<u8>;

// == errors ==

#[derive(Debug)]
struct ErrorChain {
    current: Box<::std::error::Error>,
    next: Option<Box<ErrorChain>>,
}

impl ErrorChain {
    fn new<T>(err_to_wrap: T) -> Self
        where ErrorChain: std::convert::From<T>
    {

        let error_to_chain = ErrorChain::from(err_to_wrap);

        ErrorChain {
            current: error_to_chain.current,
            next: None,
        }
    }

    fn chain_err<T>(self, error_to_chain: T) -> Self
        where ErrorChain: std::convert::From<T>
    {

        let error_to_chain = ErrorChain::from(error_to_chain);

        ErrorChain {
            current: error_to_chain.current,
            next: Some(Box::new(self)),
        }
    }

    fn iter(&self) -> ErrorChainIter {
        ErrorChainIter(Some(self))
    }
}

impl ::std::error::Error for ErrorChain {
    fn description(&self) -> &str {
        self.current.description()
    }

    fn cause(&self) -> Option<&::std::error::Error> {
        match self.next {
            Some(ref c) => Some(&**c),
            None => self.current.cause(),
        }
    }
}

impl ::std::fmt::Display for ErrorChain {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> Result<(), ::std::fmt::Error> {
        self.current.fmt(f)
    }
}

macro_rules! error_chain_for {
    ($err_type: ident) => {
        impl ::std::convert::From<$err_type> for ErrorChain {
            fn from(err: $err_type) -> Self {
                ErrorChain {
                    current: Box::new(err),
                    next: None
                }
            }
        }
    }
}

error_chain_for!(ErrorLocation);
error_chain_for!(U8Error);

#[derive(Debug)]
struct ErrorMsg(String);

impl ::std::error::Error for ErrorMsg {
    fn description(&self) -> &str {
        &self.0
    }
}

impl ::std::fmt::Display for ErrorMsg {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> Result<(), ::std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl<'a> ::std::convert::From<&'a str> for ErrorChain {
    fn from(err: &str) -> Self {
        ErrorChain {
            current: Box::new(ErrorMsg(format!("{}", err))),
            next: None,
        }
    }
}

impl ::std::convert::From<String> for ErrorChain {
    fn from(err: String) -> Self {
        ErrorChain {
            current: Box::new(ErrorMsg(err)),
            next: None,
        }
    }
}

struct ErrorChainIter<'a>(pub Option<&'a ::std::error::Error>);

impl<'a> Iterator for ErrorChainIter<'a> {
    type Item = &'a ::std::error::Error;

    fn next<'b>(&'b mut self) -> Option<&'a ::std::error::Error> {
        match self.0.take() {
            Some(e) => {
                self.0 = e.cause();
                Some(e)
            }
            None => None,
        }
    }
}

#[derive(Debug)]
struct ErrorLocation {
    location: CurrentPosition,
    description: String,
}

impl ErrorLocation {
    fn new(location: CurrentPosition, description: String) -> Self {
        ErrorLocation {
            location: location,
            description: description,
        }
    }
}

impl ::std::error::Error for ErrorLocation {
    fn description(&self) -> &str {
        &self.description
    }
}

impl ::std::fmt::Display for ErrorLocation {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> Result<(), ::std::fmt::Error> {
        write!(f,
               "Line {}, Column {}: {}",
               self.location.line(),
               self.location.col(),
               self.description)
    }
}

// == helpers ==

// like ParseResult::map_err, but this higher-order helper passes &Input to
// error mapping/transform function
#[inline]
fn on_error<I: Input, T, E: ::std::error::Error + 'static, F, V: ::std::error::Error + 'static, G>
    (i: I,
     f: F,
     g: G)
     -> ParseResult<I, T, ErrorChain>
    where F: FnOnce(I) -> ParseResult<I, T, E>,
          G: FnOnce(&I) -> V,
          ErrorChain: std::convert::From<E>,
          ErrorChain: std::convert::From<V>
{

    match f(i).into_inner() {
        (i, Ok(t)) => i.ret(t),
        (i, Err(e)) => {
            let err_val = g(&i);

            let foo = ErrorChain::new(e);
            let wrapped_err = foo.chain_err(err_val);

            // let wrapped_err = ErrorChain::new(e).chain_err(err_val);
            i.err(wrapped_err)
        }
    }
}

// TODO: old; remove
// #[inline]
// fn on_error<I: Input, T, E, F, V, G>(i: I, f: F, g: G) -> ParseResult<I, T, V>
//     where F: FnOnce(I) -> ParseResult<I, T, E>,
//           G: FnOnce(E, &I) -> V {

//     match f(i).into_inner() {
//         (i, Ok(t))  => i.ret(t),
//         (i, Err(e)) => {
//             let err_val = g(e, &i);
//             i.err(err_val)
//         }
//     }
// }

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct CurrentPosition(// The current line, zero-indexed.
                           u64,
                           // The current col, zero-indexed.
                           u64);

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
    type Token = u8;

    fn update<'a, B>(&mut self, b: &'a B)
        where B: Buffer<Token = Self::Token>
    {
        b.iterate(|c| {
            // TODO: refactor from fn source_character
            if c == b'\n' {
                self.0 += 1; // line num
                self.1 = 0;  // col num
            } else {
                self.1 += 1; // col num
            }
        });
    }

    fn add(&mut self, t: Self::Token) {
        // TODO: refactor from fn source_character
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
fn parse_list<I: U8Input, D, Delim, A, R, Reduced, E>(input: I,
                                                      delimiter: D,
                                                      reducer: R)
                                                      -> ParseResult<I, A, E>
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
                   |i| i.ret(()))
        })
        .map(|_| {
            Rc::try_unwrap(initial_accumulator)
                .ok()
                .unwrap()
                .into_inner()
        })
}

#[inline]
fn parse_list_rest<I: U8Input, D, Delim, A, R, Reduced, E>(input: I,
                                                           delimiter: D,
                                                           accumulator: Rc<RefCell<A>>,
                                                           reducer: R)
                                                           -> ParseResult<I, (), E>
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
        parse_result = parse_result.then(|i| {
                either(i,
                       // left
                       |i| {
                           delimiter(i, accumulator.clone())
                               .then(|i| reducer(i, accumulator.clone()))
                               .map(|_| ())
                       },
                       // right
                       |i| i.ret(()))
            })
            .bind(|i, result| {
                match result {
                    Either::Left(_) => {
                        // continue while loop
                    }
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

        // beginning of string
        i -> chomp::parsers::token(i, b'\'');

        // string contents
        let line: Vec<u8> = parse_list(
            // delimiter
            |i, _| chomp::parsers::string(i, br#"\'"#),
            // reducer
            parse_single_quote_string_reducer

        );

        // end of string
        i -> chomp::parsers::token(i, b'\'');

        ret {
            let line = String::from_utf8_lossy(line.as_slice()).into_owned();
            line
        }
    }
}

#[inline]
fn parse_single_quote_string_reducer<I: U8Input>(input: I,
                                                 accumulator: Rc<RefCell<Vec<u8>>>)
                                                 -> SimpleResult<I, ()> {
    parse!{input;

        let line: Vec<u8> = many_till(chomp::parsers::any, parse_single_quote_string_look_ahead);

        let has_quote = option(
            |i| look_ahead(i, |i| chomp::parsers::string(i, br#"\'"#)).map(|_| true),
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
            // stop still single quote escape
            |i| chomp::parsers::string(i, br#"\'"#).map(|_| ()),
            // or single quote
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

    match parse_only(parse_single_quote_string, br#"''"#) {
        Ok(result) => {
            assert_eq!(result, r#""#.to_owned());
        }
        Err(_) => {
            assert!(false);
        }
    }

    match parse_only(parse_single_quote_string, br#"'foo'"#) {
        Ok(result) => {
            assert_eq!(result, r#"foo"#.to_owned());
        }
        Err(_) => {
            assert!(false);
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

// Helper macro to generate the following:
//
// $root_name := $inner_parser $rest_name*
// $rest_name := $delim_name $inner_parser
//
macro_rules! generate_list_parser {
    ($root_name: ident; $rest_name: ident; $state_name: ident; $delim_name: ident; $inner_parser: ident) => {

        enum $state_name {
            Initial,
            WellFormed($root_name),
            // state after the delimiter; but before item is consumed
            PostDelim($root_name, $delim_name),
        }

        impl Default for $state_name {
            fn default() -> Self {
                $state_name::Initial
            }
        }

        impl $state_name {

            // TODO: document this
            fn unwrap(self) -> $root_name {
                match self {
                    $state_name::WellFormed(expr) => expr,
                    _ => panic!("incorrect state"),
                }
            }

            fn is_initial(&self) -> bool {
                match *self {
                    $state_name::Initial => true,
                    _ => false
                }
            }

            fn add_delim(&mut self, operator_delim: $delim_name) {

                let prev_state = mem::replace(self, $state_name::Initial);

                let next_state = match prev_state {
                    $state_name::Initial => {
                        panic!("incorrect state");
                    }
                    $state_name::WellFormed(expr) => {
                        $state_name::PostDelim(expr, operator_delim)
                    }
                    $state_name::PostDelim(_, _) => {
                        panic!("incorrect state");
                    }
                };

                mem::replace(self, next_state);
            }

            fn add_item(&mut self, rhs_val: $inner_parser) {

                let prev_state = mem::replace(self, $state_name::Initial);

                let next_state = match prev_state {
                    $state_name::Initial => {

                        let expr = $root_name::new(rhs_val);
                        $state_name::WellFormed(expr)

                    }
                    $state_name::WellFormed(_) => {
                        panic!("incorrect state");
                    }
                    $state_name::PostDelim(prev_expr, operator_delim) => {

                        let next_expr = prev_expr.add_item(operator_delim, rhs_val);

                        $state_name::WellFormed(next_expr)
                    }
                };

                mem::replace(self, next_state);
            }
        }

    }
}

// == parser helpers ==

// TODO: better function? refactor this
#[inline]
fn string_to_unicode_char(s: &str) -> Option<char> {
    // TODO: asset str len
    u32::from_str_radix(s, 16)
        .ok()
        .and_then(std::char::from_u32)
}

// TODO: fix this
// TODO: test for ASI behaviour
#[inline]
fn semicolon<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
    parse!{i;
        // TODO: ASI rule
        token(b';');
        ret {()}
    }
}

#[inline]
fn token<I: U8Input>(i: ESInput<I>, tok: I::Token) -> ESParseResult<I, I::Token> {
    on_error(i, |i| chomp::parsers::token(i, tok), |i| {
        let reason = format!("Expected: {}", String::from_utf8_lossy(&[tok]));
        ErrorLocation::new(i.position(), reason)
    })
}

#[inline]
fn string<I: U8Input>(i: ESInput<I>, str_match: &[u8]) -> ESParseResult<I, I::Buffer> {
    on_error(i, |i| chomp::parsers::string(i, str_match), |i| {
        let reason = format!("Expected: {}", String::from_utf8_lossy(str_match));
        ErrorLocation::new(i.position(), reason)
    })
}

// TODO: test
#[inline]
fn string_till<I: U8Input, F>(input: ESInput<I>, mut stop_at: F) -> ESParseResult<I, String>
    where F: Fn(ESInput<I>) -> ESParseResult<I, ()>
{
    parse!{input;
        let line: Vec<char> = many_till(parse_utf8_char, |i| look_ahead(i, &mut stop_at));

        ret {
            line.into_iter().collect()
        }
    }
}

#[inline]
fn token_as_char<I: U8Input>(i: ESInput<I>, c: u8) -> ESParseResult<I, char> {
    token(i, c).bind(|i, c| i.ret(c as char))
}

// TODO: test
#[inline]
fn parse_utf8_char_of_bytes<I: U8Input>(i: ESInput<I>, needle: &[u8]) -> ESParseResult<I, char> {
    // TODO: refactor this
    on_error(i,
             |i| look_ahead(i, |i| string(i, needle)).then(parse_utf8_char),
             |i| {
                 let loc = i.position();
                 let reason = "Expected utf8 character.".to_string();
                 ErrorLocation::new(loc, reason)
             })
}

// TODO: this is old; remove
#[inline]
fn ___parse_utf8_char<I: U8Input>(mut i: ESInput<I>) -> ESParseResult<I, char> {

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
                }
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
    return i.err(ErrorLocation::new(loc, reason).into());

}

// TODO: refactor this out; since source text is interpeted as u8; refactor this out
// #[inline]
// fn __string_not_utf8<I: U8Input>(i: ESInput<I>, needle: &[u8]) -> ESParseResult<I, I::Buffer> {

//     let mark = i.mark();
//     let mut current_needle = needle;
//     let mut should_continue = true;

//     let mut parse_result = either(i,
//                                   // left
//                                   escaped_unicode_escape_seq,
//                                   // right
//                                   parse_utf8_char)
//         .map_err(|e| {
//             should_continue = false;
//             e
//         });

//     while should_continue {

//         parse_result = parse_result.bind(|i, result| {
//                 match result {
//                     Either::Left(c) => {
//                         // NOTE: Reserved keyword must not contain escaped characters.
//                         i.err("Reserved keyword must not contain escaped characters.".into())
//                     }
//                     Either::Right(c) => {

//                         let mut buf = String::with_capacity(1);
//                         buf.push(c);
//                         let bytes = buf.as_bytes();

//                         if current_needle.starts_with(bytes) {
//                             current_needle = current_needle.split_at(bytes.len()).1;
//                             i.ret(Either::Right(c))
//                         } else {
//                             i.err(format!("Does not start with: {:?}", bytes).into())
//                         }
//                     }
//                 }
//             })
//             .map_err(|e| {
//                 should_continue = false;
//                 e
//             });

//         if current_needle.len() <= 0 || !should_continue {
//             should_continue = false;
//             break;
//         }

//         parse_result = parse_result.then(|i| {
//                 either(i,
//                        // left
//                        escaped_unicode_escape_seq,
//                        // right
//                        parse_utf8_char)
//             })
//             .map_err(|e| {
//                 should_continue = false;
//                 e
//             });
//     }

//     parse_result.then(|i| {
//         on_error(i,
//                  |mut i| -> ESParseResult<I, I::Buffer> {
//                      let res = (&mut i).consume_from(mark);
//                      i.ret(res)
//                  },
//                  |i| {
//                      let reason = format!("Expected keyword: {}.",
//                                           std::str::from_utf8(needle).unwrap());
//                      ErrorLocation::new(i.position(), reason)
//                  })
//     })


// }

// == Tokens ==

#[derive(Debug)]
enum CommonDelim {
    WhiteSpace(char),
    LineTerminator(char),
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
        return on_error(i,
                        |i| -> ESParseResult<I, CommonDelim> {
            parse!{i;
                let delim =
                    (i -> whitespace(i).map(|w| {
                        let WhiteSpace(w) = w;
                        CommonDelim::WhiteSpace(w)
                    })) <|>
                    // TODO: remove
                    // (i -> line_terminator(i).map(|w| {
                    //     let LineTerminator(w) = w;
                    //     CommonDelim::LineTerminator(w)
                    // })) <|>
                    (i -> comment(i).map(|c| CommonDelim::Comment(c)));
                ret delim
            }
        },
                        |i| {
                            let loc = i.position();
                            let reason = "Expected whitespace, or comment.".to_string();
                            ErrorLocation::new(loc, reason)
                        });
    }

    on_error(i,
             |i| -> ESParseResult<I, CommonDelim> {
        parse!{i;
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
        }
    },
             |i| {
                 let loc = i.position();
                 let reason = "Expected whitespace, line terminator, or comment.".to_string();
                 ErrorLocation::new(loc, reason)
             })
}

#[inline]
fn common_delim<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Vec<CommonDelim>> {
    many(i, |i| __common_delim(i, true))
}

#[inline]
fn common_delim_required<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Vec<CommonDelim>> {
    many1(i, |i| __common_delim(i, true))
}

// parse common delimeters but not line terminators
#[inline]
fn common_delim_no_line_term<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Vec<CommonDelim>> {
    many(i, |i| __common_delim(i, false))
}

// == Parameters ==
// Based on: http://www.ecma-international.org/ecma-262/7.0/#sec-grammar-notation
#[repr(u32)]
#[derive(Clone)]
enum Parameter {
    In,
    Yield,
    Return,
    Default,
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

// == 10 ECMAScript Language: Source Code ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-source-code

// == 10.1 Source Text ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-source-text

struct SourceCharacter(char);

// http://www.ecma-international.org/ecma-262/7.0/#prod-SourceCharacter
fn source_character<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, SourceCharacter> {
    // (from spec)
    // Regardless of the external source text encoding, a conforming ECMAScript implementation
    // processes the source text as if it was an equivalent sequence of SourceCharacter values,
    // each SourceCharacter being a Unicode code point.
    //
    // NOTE: For this implementation, enforce source text input to be UTF-8.
    parse_utf8_char(i).map(SourceCharacter)
}

#[test]
fn source_character_test() {
    parse_utf8_char_test();
}

fn parse_utf8_char<I: U8Input>(mut i: ESInput<I>) -> ESParseResult<I, char> {

    // NOTE: rust `char` type represents a Unicode Scalar Value.
    // see: http://www.unicode.org/glossary/#unicode_scalar_value
    // contrast with: http://www.unicode.org/glossary/#code_point
    //
    // scalar value := 0x0 to 0xD7FF (inclusive), and 0xE000 to 0x10FFFF (inclusive)

    // TODO: clean up refs
    // ref: http://www.fileformat.info/info/unicode/utf8.htm
    // ref: https://developer.apple.com/library/content/documentation/Swift/Conceptual/Swift_Programming_Language/StringsAndCharacters.html

    enum Unicode {
        UTF8_1Byte,
        UTF8_2Bytes,
        UTF8_3Bytes,
        UTF8_4Bytes,
    }

    let mut pattern = Unicode::UTF8_1Byte;

    let mut internal_buf = vec![];

    let mut result: Option<char> = None;

    let _buffer = i.consume_while(|c: u8| {

        if internal_buf.len() <= 0 && c < 0x80 {
            // first and only byte of a sequence

            result = Some(c as char);

            // break from consume_while
            return false;
        }

        if internal_buf.len() <= 0 {
            // c is the first byte of a potential unicode code point.
            // This byte determines the number of bytes expected in the UTF8 character.
            let first_byte = c;

            internal_buf.push(first_byte);

            pattern = if 0xC2 <= first_byte && first_byte <= 0xDF {
                Unicode::UTF8_2Bytes
            } else if 0xE0 <= first_byte && first_byte <= 0xEF {
                Unicode::UTF8_3Bytes
            } else if 0xF0 <= first_byte && first_byte <= 0xFF {
                Unicode::UTF8_4Bytes
            } else {
                // invalid first byte
                result = None;
                // break from consume_while
                return false;
            };

            // continue consume_while
            return true;
        }

        // invariant: internal_buf.len() >= 1
        // invariant: pattern != Unicode::UTF8_1Byte

        let next_byte = c;

        if !(0x80 <= next_byte && next_byte <= 0xBF) {
            // invalid continuing byte in a multi-byte sequence.
            result = None;
            // break from consume_while
            return false;
        }

        internal_buf.push(next_byte);

        // invariant: internal_buf.len() >= 2

        match pattern {
            Unicode::UTF8_1Byte => {
                // invariant violation
                result = None;
                // break from consume_while
                return false;
            }
            Unicode::UTF8_2Bytes => {
                // no-op
            }
            Unicode::UTF8_3Bytes => {
                if internal_buf.len() < 3 {
                    // continue consume_while
                    return true;
                }
            }
            Unicode::UTF8_4Bytes => {
                if internal_buf.len() < 4 {
                    // continue consume_while
                    return true;
                }
            }
        }

        // invariant: internal_buf contains at least 2 bytes and at most 4 bytes that compose a valid utf8 character

        match std::str::from_utf8(&internal_buf) {
            Err(_) => {
                // not valid_utf8
                result = None;
                // break from consume_while
                return false;
            }
            Ok(__result) => {
                let __result = __result.chars().collect::<Vec<_>>();

                if __result.len() == 1 {
                    result = Some(__result[0]);
                    // break from consume_while
                    return false;
                } else {
                    result = None;
                    // break from consume_while
                    return false;
                }
            }
        }

        unreachable!();

    });

    match result {
        None => {

            // TODO: user configuration to allow invalid utf-8 characters to be coerced to replacement character;
            // TODO: delegate this to a wrapping function
            // i.ret('\u{FFFD}');

            let loc = i.position();
            let reason = "Expected utf8 character.".to_string();
            return i.err(ErrorLocation::new(loc, reason).into());

        }
        Some(c) => {
            return i.ret(c);
        }
    }

}

#[test]
fn parse_utf8_char_test() {

    {
        let v: &[u8] = b"v";

        let i = InputPosition::new(v, CurrentPosition::new());
        match parse_utf8_char(i).into_inner().1 {
            Ok(result) => {
                assert_eq!(result, 'v');
            }
            Err(_) => {
                assert!(false);
            }
        }
    };

    {

        // case: invalid first byte sequence

        for first_byte in 0x80..0xC1 {

            // 0x80 to 0xBF are continuing byte markers
            // 0xC0 and 0xC1 re used for an invalid "overlong encoding" of ASCII characters

            let input: &[u8] = &[first_byte];

            let i = InputPosition::new(input, CurrentPosition::new());
            match parse_utf8_char(i).into_inner().1 {
                Ok(_) => {
                    assert!(false);
                }
                Err(_) => {
                    assert!(true);
                }
            }
        }


    };

    {

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

        // case: only one sparkle heart is parsed

        let sparkle_heart_and_smile = vec![// http://graphemica.com/%F0%9F%92%96
                                           240,
                                           159,
                                           146,
                                           150,
                                           // http://graphemica.com/%F0%9F%98%80
                                           240,
                                           159,
                                           152,
                                           128];

        let i = InputPosition::new(sparkle_heart_and_smile.as_slice(), CurrentPosition::new());
        match parse_utf8_char(i).into_inner().1 {
            Ok(result) => {
                assert_eq!(result, '\u{1f496}');
            }
            Err(_) => {
                assert!(false);
            }
        }

    };

    {
        // case: valid two byte sequence

        // TODO: complete
    };

    {

        // case: invalid two byte sequence (2nd byte is invalid)

        let input: &[u8] = &[0xD8, 0x00];

        let i = InputPosition::new(input, CurrentPosition::new());
        match parse_utf8_char(i).into_inner().1 {
            Ok(_) => {
                assert!(false);
            }
            Err(_) => {
                assert!(true);
            }
        }
    };

    {
        // case: valid three byte sequence

        // TODO: complete
    };

    {

        // case: invalid three byte sequence (2nd byte is invalid)

        let input: &[u8] = &[0xE0, 0x00, 0x80];

        let i = InputPosition::new(input, CurrentPosition::new());
        match parse_utf8_char(i).into_inner().1 {
            Ok(_) => {
                assert!(false);
            }
            Err(_) => {
                assert!(true);
            }
        }
    };

    {

        // case: invalid three byte sequence (3rd byte is invalid)

        let input: &[u8] = &[0xE0, 0x80, 0x00];

        let i = InputPosition::new(input, CurrentPosition::new());
        match parse_utf8_char(i).into_inner().1 {
            Ok(_) => {
                assert!(false);
            }
            Err(_) => {
                assert!(true);
            }
        }
    };

    {
        // case: valid four byte sequence

        // TODO: complete
    };

    // TODO: cases of invalid four byte sequences
}

// TODO: test
// parse surrogate pairs and covert to unicode scalar value (char type)
fn parse_utf16_surrogate_pairs<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, char> {

    // TODO: big endian was assumed

    #[inline]
    fn parse_u16<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, u16> {
        let any = chomp::parsers::any;
        parse!{i;
            let first = any();
            let second = any();

            ret {
                let first: u16 = (first as u16) << 8;
                let second: u16 = second as u16;
                let result: u16 = first | second;

                result
            }
        }
    }

    parse_u16(i)
        .bind(|i, high_surrogate| {
            parse_u16(i)
                .map(|low_surrogate| {
                    (high_surrogate, low_surrogate)
                })
        })
        .bind(|i, (high_surrogate, low_surrogate)| {

        // high: 0xD800 to 0xDBFF (u16)
        // low:  0xDC00 to 0xDFFF (u16)
        if 0xD800 <= high_surrogate && high_surrogate <= 0xDBFF {
            if 0xDC00 <= low_surrogate && low_surrogate <= 0xDFFF {

                let v = &[high_surrogate, low_surrogate];

                let result = match String::from_utf16(v) {
                    Err(_) => {
                        return i.err("Unable to convert utf-16 surrogate pair to a single character.".into());
                    },
                    Ok(result) => result.chars().collect::<Vec<_>>()
                };

                if result.len() == 1 {
                    return i.ret(result[0]);
                } else {
                    return i.err("Unable to convert utf-16 surrogate pair to a single character.".into());
                }
            }
        }

        return i.err("Invalid utf-16 surrogate pair.".into());
    })
}

// == 11.2 White Space ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-white-space

struct WhiteSpace(char);

// http://www.ecma-international.org/ecma-262/7.0/#prod-WhiteSpace
fn whitespace<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, WhiteSpace> {

    #[inline]
    fn other_whitespace<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, char> {
        parse_utf8_char(i).bind(|i, c: char| {
            if c.is_whitespace() {
                i.ret(c)
            } else {
                let loc = i.position();
                let reason = "Expected whitespace.".to_string();
                i.err(ErrorLocation::new(loc, reason).into())
            }
        })
    }

    on_error(i,
             |i| -> ESParseResult<I, WhiteSpace> {
        parse!{i;

            let whitespace_char =
                parse_utf8_char_of_bytes(b"\x0009") <|> // <TAB>; CHARACTER TABULATION
                parse_utf8_char_of_bytes(b"\x000B") <|> // <VT>; LINE TABULATION
                parse_utf8_char_of_bytes(b"\x000C") <|> // <FF>; FORM FEED (FF)
                parse_utf8_char_of_bytes(b"\x0020") <|> // <SP>; SPACE
                parse_utf8_char_of_bytes(b"\x00A0") <|> // <NBSP>; NO-BREAK SPACE
                parse_utf8_char_of_bytes(b"\xFEFF") <|> // <ZWNBSP>; ZERO WIDTH NO-BREAK SPACE
                other_whitespace(); // Any other Unicode "Separator, space" code point

            ret WhiteSpace(whitespace_char)
        }
    },
             |i| ErrorLocation::new(i.position(), "Expected whitespace.".to_string()))


}

// == 11.3 Line Terminators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-line-terminators

struct LineTerminator(char);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LineTerminator
fn line_terminator<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, LineTerminator> {
    on_error(i,
             |i| -> ESParseResult<I, LineTerminator> {
        parse!{i;

            let line_terminator_char =
                parse_utf8_char_of_bytes(b"\x000A") <|> // <LF>; LINE FEED (LF)
                parse_utf8_char_of_bytes(b"\x000D") <|> // <CR>; CARRIAGE RETURN (CR)
                parse_utf8_char_of_bytes(b"\x2028") <|> // <LS>; LINE SEPARATOR
                parse_utf8_char_of_bytes(b"\x2029");    // <PS>; PARAGRAPH SEPARATOR

            ret LineTerminator(line_terminator_char)
        }
    },
             |i| {
                 let loc = i.position();
                 let reason = "Expected utf8 character.".to_string();
                 ErrorLocation::new(loc, reason)
             })
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
             |i| -> ESParseResult<I, LineTerminatorSequence> {
        parse!{i;

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
        }
    },
             |i| {
                 let loc = i.position();
                 let reason = "Expected linte terminator sequence.".to_string();
                 ErrorLocation::new(loc, reason)
             })
}

// == 11.4 Comments ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-comments

#[derive(Debug)]
enum Comment {
    MultiLineComment(String),
    SingleLineComment(String),
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
            on_error(i, |i| string(i, END).map(|_| ()), |i| {
                let loc = i.position();
                ErrorLocation::new(loc, "Expected */.".to_string())
            })
        }

        // TODO: verify production rule satisfaction
        // http://www.ecma-international.org/ecma-262/7.0/#prod-MultiLineCommentChars

        parse!{i;
            on_error(
                |i| string(i, b"/*"),
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected /* for multi-line comment.".to_string())
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
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected // for single-line comment.".to_string())
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

struct IdentifierName(IdentifierStart, Vec<IdentifierStart>, Vec<IdentifierPart>);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierName
fn identifier_name<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, IdentifierName> {

    on_error(i,
             |i| -> ESParseResult<I, IdentifierName> {
        parse!{i;

                let start = identifier_start();
                let more_start: Vec<IdentifierStart> = many(identifier_start);
                let rest: Vec<IdentifierPart> = many(identifier_part);

                ret {
                    IdentifierName(start, more_start, rest)
                }
            }
    },
             |i| {
                 let reason = format!("Invalid identifier.");
                 ErrorLocation::new(i.position(), reason)
             })


}

enum IdentifierStart {
    UnicodeIDStart(UnicodeIDStart),
    DollarSign,
    Underscore,
    UnicodeEscapeSequence(UnicodeEscapeSequence),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierStart
fn identifier_start<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, IdentifierStart> {

    #[inline]
    fn escaped_unicode_escape_seq<I: U8Input>(i: ESInput<I>)
                                              -> ESParseResult<I, UnicodeEscapeSequence> {
        token(i, b'\\').then(unicode_escape_sequence)
    }

    parse!{i;

        let start =
        (i -> unicode_id_start(i).map(|x| IdentifierStart::UnicodeIDStart(x))) <|>
        (i -> token_as_char(i, b'$').map(|_| IdentifierStart::DollarSign)) <|>
        (i -> token_as_char(i, b'_').map(|_| IdentifierStart::Underscore)) <|>
        (i -> escaped_unicode_escape_seq(i).map(|x| IdentifierStart::UnicodeEscapeSequence(x)));

        ret start
    }
}

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
        (i -> token_as_char(i, b'$').map(|_| IdentifierPart::DollarSign)) <|>
        (i -> token_as_char(i, b'_').map(|_| IdentifierPart::Underscore)) <|>
        (i -> escaped_unicode_escape_seq(i).map(|x| IdentifierPart::UnicodeEscapeSequence(x))) <|>
        // <ZWNJ> (i.e. Zero-width non-joiner)
        (i -> parse_utf8_char_of_bytes(i, b"\x200C").map(|x| IdentifierPart::ZeroWidthNonJoiner)) <|>
        // <ZWJ> (i.e. Zero-width joiner)
        (i -> parse_utf8_char_of_bytes(i, b"\x200D").map(|x| IdentifierPart::ZeroWidthJoiner));

        ret part
    }
}

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
            let reason = format!("Invalid utf8 character.");
            i.err(ErrorLocation::new(loc, reason).into())
        }
    })
}

#[test]
fn unicode_id_start_test() {

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
            let reason = format!("Invalid utf8 character: `{}`", c);
            i.err(ErrorLocation::new(loc, reason).into())
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

// == 11.6.2 Reserved Words ==

// TODO: enum Keyword type

// TODO: review this
// http://www.ecma-international.org/ecma-262/7.0/#sec-reserved-words
fn reserved_word<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, I::Buffer> {

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
            // string_not_utf8(b"let") <|>
            // string_not_utf8(b"static") <|>

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

    let fails = vec![r"\u0076\u0061\u0072",
                     r"\u0076\u{0061}\u0072",
                     r"v\u0061\u0072",
                     r"\u0076a\u0072",
                     r"\u0076\u0061r"];

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
    on_error(i, |i| string(i, b"null").map(|_| Null), |i| {
        let loc = i.position();
        ErrorLocation::new(loc, "Expected null keyword.".to_string())
    })
}

// == 11.8.2 Boolean Literals ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-boolean-literals

enum Bool {
    True,
    False,
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BooleanLiteral
#[inline]
fn boolean_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Bool> {
    on_error(i,
             |i| {
                 or(i,
                    |i| string(i, b"true").map(|_| Bool::True),
                    |i| string(i, b"false").map(|_| Bool::False))
             },
             |i| {
                 let loc = i.position();
                 ErrorLocation::new(loc, "Expected boolean literal.".to_string())
             })
}

// == 11.8.3 Numeric Literals ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-literals-numeric-literals

enum NumericLiteral {
    Decimal(DecimalLiteral),
    BinaryInteger(BinaryDigits),
    OctalInteger(OctalDigits),
    HexInteger(HexDigits),
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
    WholeFractionDecimal(DecimalIntegerLiteral,
                         /* . */
                         Option<DecimalDigits>,
                         Option<ExponentPart>),
    FractionDecimal(/* . */
                    DecimalDigits,
                    Option<ExponentPart>),
    WholeDecimal(DecimalIntegerLiteral, Option<ExponentPart>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-DecimalLiteral
fn decimal_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, DecimalLiteral> {
    or(i,
       |i| {
        parse!{i;

            let whole = decimal_integer_literal();
            token(b'.');
            let fraction = option(|i| decimal_digits(i).map(|c| Some(c)), None);
            let exp_part = option(|i| exponent_part(i).map(|c| Some(c)), None);

            ret DecimalLiteral::WholeFractionDecimal(whole, fraction, exp_part)
        }
    },
       |i| {
        or(i,
           |i| {
            parse!{i;

                token(b'.');
                let fraction = decimal_digits();
                let exp_part = option(|i| exponent_part(i).map(|c| Some(c)), None);

                ret DecimalLiteral::FractionDecimal(fraction, exp_part)
            }
        },
           |i| {
            parse!{i;

                let whole = decimal_integer_literal();
                let exp_part = option(|i| exponent_part(i).map(|c| Some(c)), None);

                ret DecimalLiteral::WholeDecimal(whole, exp_part)
            }
        })
    })
}

enum DecimalIntegerLiteral {
    Zero,
    NonZero(NonZeroDigit, Option<DecimalDigits>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-DecimalIntegerLiteral
fn decimal_integer_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, DecimalIntegerLiteral> {
    or(i,
       |i| token(i, b'0').map(|_| DecimalIntegerLiteral::Zero),
       |i| {
        parse!{i;

            let prefix = non_zero_digit();
            let suffix = option(|i| decimal_digits(i).map(Some), None);

            ret {
                DecimalIntegerLiteral::NonZero(prefix, suffix)
            }
        }
    })
}

struct DecimalDigits(Vec<DecimalDigit>);

impl DecimalDigits {
    fn as_string(&self) -> String {
        self.0.clone().into_iter().map(|DecimalDigit(c)| c).collect()
    }
}

impl MathematicalValue for DecimalDigits {
    // TODO: test
    fn mathematical_value(&self) -> i64 {
        i64::from_str_radix(&self.as_string(), 10).unwrap()
    }
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-DecimalDigits
fn decimal_digits<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, DecimalDigits> {
    on_error(i,
             |i| -> ESParseResult<I, DecimalDigits> {
                 many1(i, decimal_digit).bind(|i, buf: Vec<DecimalDigit>| i.ret(DecimalDigits(buf)))
             },
             |i| {
                 let loc = i.position();
                 ErrorLocation::new(loc, "Expected decimal digit (0 or 9).".to_string())
             })
}

#[derive(Clone)]
struct DecimalDigit(char);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-DecimalDigit
fn decimal_digit<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, DecimalDigit> {

    #[inline]
    fn is_decimal_digit(c: u8) -> bool {
        (b'0' <= c && c <= b'9')
    }

    on_error(i, |i| satisfy(i, is_decimal_digit), |i| {
            let loc = i.position();
            ErrorLocation::new(loc, "Expected decimal digit (0 to 9).".to_string())
        })
        .map(|c| DecimalDigit(c as char))
}

struct NonZeroDigit(char);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-NonZeroDigit
fn non_zero_digit<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, NonZeroDigit> {

    #[inline]
    fn is_non_zero_digit(c: u8) -> bool {
        (b'1' <= c && c <= b'9')
    }

    on_error(i, |i| satisfy(i, is_non_zero_digit), |i| {
            let loc = i.position();
            ErrorLocation::new(loc, "Expected non-zero digit (1 to 9).".to_string())
        })
        .map(|c| NonZeroDigit(c as char))
}

struct ExponentPart(SignedInteger);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ExponentPart
fn exponent_part<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ExponentPart> {
    parse!{i;
        exponent_indicator();
        let result = signed_integer();
        ret ExponentPart(result)
    }
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ExponentIndicator
fn exponent_indicator<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
    or(i, |i| token(i, b'e'), |i| token(i, b'E')).map(|_| ())
}

enum SignedInteger {
    Unsigned(DecimalDigits),
    Positive(DecimalDigits),
    Negative(DecimalDigits),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-SignedInteger
fn signed_integer<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, SignedInteger> {

    enum Signed {
        Unsigned,
        Positive,
        Negative,
    }

    parse!{i;

        let prefix = option(|i| -> ESParseResult<I, Signed> {
            parse!{i;
                let signed = (i -> token(i, b'+').map(|_| Signed::Positive)) <|>
                (i -> token(i, b'-').map(|_| Signed::Negative));
                ret signed
            }
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

struct BinaryDigits(Vec<BinaryDigit>);

impl BinaryDigits {
    fn as_string(&self) -> String {
        self.0.clone().into_iter().map(|BinaryDigit(c)| c).collect()
    }
}

impl MathematicalValue for BinaryDigits {
    // TODO: test
    fn mathematical_value(&self) -> i64 {
        i64::from_str_radix(&self.as_string(), 2).unwrap()
    }
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BinaryDigits
fn binary_digits<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, BinaryDigits> {
    on_error(i,
             |i| -> ESParseResult<I, BinaryDigits> {
                 many1(i, binary_digit).bind(|i, buf: Vec<BinaryDigit>| i.ret(BinaryDigits(buf)))
             },
             |i| {
                 let loc = i.position();
                 ErrorLocation::new(loc, "Expected binary digit (0 or 1).".to_string())
             })
}

#[derive(Clone)]
struct BinaryDigit(char);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BinaryDigit
#[inline]
fn binary_digit<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, BinaryDigit> {

    #[inline]
    fn is_binary_digit(c: u8) -> bool {
        (b'0' <= c && c <= b'1')
    }

    on_error(i, |i| satisfy(i, is_binary_digit), |i| {
            let loc = i.position();
            ErrorLocation::new(loc, "Expected binary digit (0 or 1).".to_string())
        })
        .map(|c| BinaryDigit(c as char))
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

struct OctalDigits(Vec<OctalDigit>);

impl OctalDigits {
    fn as_string(&self) -> String {
        self.0.clone().into_iter().map(|OctalDigit(c)| c).collect()
    }
}

impl MathematicalValue for OctalDigits {
    // TODO: test
    fn mathematical_value(&self) -> i64 {
        i64::from_str_radix(&self.as_string(), 8).unwrap()
    }
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-OctalDigits
fn octal_digits<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, OctalDigits> {
    on_error(i,
             |i| -> ESParseResult<I, OctalDigits> {
                 many1(i, octal_digit).bind(|i, buf: Vec<OctalDigit>| i.ret(OctalDigits(buf)))
             },
             |i| {
                 let loc = i.position();
                 ErrorLocation::new(loc, "Expected octal digit (0 to 7).".to_string())
             })
}

#[derive(Clone)]
struct OctalDigit(char);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-OctalDigit
#[inline]
fn octal_digit<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, OctalDigit> {

    #[inline]
    fn is_octal_digit(c: u8) -> bool {
        (b'0' <= c && c <= b'7')
    }

    on_error(i, |i| satisfy(i, is_octal_digit), |i| {
            let loc = i.position();
            ErrorLocation::new(loc, "Expected octal digit (0 to 7).".to_string())
        })
        .map(|c| OctalDigit(c as char))

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

#[derive(PartialEq, Debug)]
struct HexDigits(Vec<HexDigit>);

impl HexDigits {
    fn as_string(&self) -> String {
        self.0.clone().into_iter().map(|HexDigit(c)| c).collect()
    }
}

impl MathematicalValue for HexDigits {
    // TODO: test
    fn mathematical_value(&self) -> i64 {
        i64::from_str_radix(&self.as_string(), 16).unwrap()
    }
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-HexDigits
fn hex_digits<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, HexDigits> {
    on_error(i,
             |i| -> ESParseResult<I, HexDigits> {
                 many1(i, hex_digit).bind(|i, buf: Vec<HexDigit>| i.ret(HexDigits(buf)))
             },
             |i| {
                 let loc = i.position();
                 ErrorLocation::new(loc, "Expected hex digit.".to_string())
             })
}

#[test]
fn hex_digits_test() {

    let i = InputPosition::new(&b"e"[..], CurrentPosition::new());
    match hex_digits(i).into_inner().1 {
        Ok(result) => {
            assert_eq!(result, HexDigits(vec![HexDigit('e')]));
        }
        Err(_) => {
            assert!(false);
        }
    }

    let i = InputPosition::new(&b"ad"[..], CurrentPosition::new());
    match hex_digits(i).into_inner().1 {
        Ok(result) => {
            assert_eq!(result, HexDigits(vec![HexDigit('a'), HexDigit('d')]));
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

// TODO: remove
// enum Hex {
//     Zero,
//     One,
//     Two,
//     Three,
//     Four,
//     Five,
//     Six,
//     Seven,
//     Eight,
//     Nine,
//     A,
//     B,
//     C,
//     D,
//     E,
//     F
// }

// impl Hex {
//     fn new(c: u8) -> Self {
//         match c {
//             b'0' => Hex::Zero,
//             b'1' => Hex::One,
//             b'2' => Hex::Two,
//             b'3' => Hex::Three,
//             b'4' => Hex::Four,
//             b'5' => Hex::Five,
//             b'6' => Hex::Six,
//             b'7' => Hex::Seven,
//             b'8' => Hex::Eight,
//             b'9' => Hex::Nine,
//             b'A' | b'a' => Hex::A,
//             b'B' | b'b' => Hex::B,
//             b'C' | b'c' => Hex::C,
//             b'D' | b'd' => Hex::D,
//             b'E' | b'e' => Hex::E,
//             b'F' | b'f' => Hex::F,
//         }
//     }
// }

#[derive(PartialEq, Debug, Clone)]
struct HexDigit(char);

// http://www.ecma-international.org/ecma-262/7.0/#prod-HexDigit
#[inline]
fn hex_digit<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, HexDigit> {

    #[inline]
    fn is_hex_digit(c: u8) -> bool {
        (b'0' <= c && c <= b'9') || (b'a' <= c && c <= b'f') || (b'A' <= c && c <= b'F')
    }

    on_error(i, |i| satisfy(i, is_hex_digit), |i| {
            let loc = i.position();
            ErrorLocation::new(loc, "Expected hex digit (0 to F).".to_string())
        })
        .map(|x| HexDigit(x as char))
}

// == 11.8.3.1 Static Semantics: MV ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-static-semantics-mv

trait MathematicalValue {
    fn mathematical_value(&self) -> i64;
}

// == 11.8.4 String Literals ==

enum StringLiteral {
    SingleQuoted(Option<SingleStringCharacters>),
    DoubleQuoted(Option<DoubleStringCharacters>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-StringLiteral
fn string_literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, StringLiteral> {
    or(i,
       |i| {
        parse!{i;
                token(b'"');

                let string = option(|i| double_string_characters(i).map(Some), None);

                token(b'"');

                ret StringLiteral::DoubleQuoted(string)
            }
    },
       |i| {
        parse!{i;
                token(b'\'');

                let string = option(|i| single_string_characters(i).map(Some), None);

                token(b'\'');

                ret StringLiteral::SingleQuoted(string)
            }
    })
}

// NOTE: This isn't Vec<DoubleStringCharacter> since DoubleStringCharactersItem::String is better than
//       DoubleStringCharacter::SourceCharacter
struct DoubleStringCharacters(Vec<DoubleStringCharactersItem>);

enum DoubleStringCharactersItem {
    // many DoubleStringCharacter::SourceCharacter merged together
    String(String),
    EscapeSequence(EscapeSequence),
    LineContinuation(LineContinuation),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-DoubleStringCharacters
fn double_string_characters<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, DoubleStringCharacters> {

    many1(i, double_string_character).bind(|i, chars: Vec<DoubleStringCharacter>| {

        let mut result: Vec<DoubleStringCharactersItem> = vec![];

        let mut string_buf = String::new();

        for c in chars.into_iter() {

            match c {
                DoubleStringCharacter::SourceCharacter(c) => {
                    let SourceCharacter(c) = c;
                    string_buf.push(c);
                    continue;
                }
                _ => {
                    string_buf.shrink_to_fit();
                    if string_buf.len() >= 1 {
                        let moved_string_buf = mem::replace(&mut string_buf, String::new());
                        result.push(DoubleStringCharactersItem::String(moved_string_buf));
                    }
                }
            }

            match c {
                DoubleStringCharacter::SourceCharacter(_) => {
                    unreachable!();
                }
                DoubleStringCharacter::EscapeSequence(e) => {
                    result.push(DoubleStringCharactersItem::EscapeSequence(e))
                }
                DoubleStringCharacter::LineContinuation(l) => {
                    result.push(DoubleStringCharactersItem::LineContinuation(l))
                }
            }
        }

        string_buf.shrink_to_fit();
        if string_buf.len() >= 1 {
            result.push(DoubleStringCharactersItem::String(string_buf));
        }

        i.ret(DoubleStringCharacters(result))
    })
}

// NOTE: This isn't Vec<SingleStringCharacter> since SingleStringCharactersItem::String is better than
//       SingleStringCharacter::SourceCharacter
struct SingleStringCharacters(Vec<SingleStringCharactersItem>);

enum SingleStringCharactersItem {
    // many SingleStringCharacter::SourceCharacter merged together
    String(String),
    EscapeSequence(EscapeSequence),
    LineContinuation(LineContinuation),
}

// TODO: test case: empty input
// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-SingleStringCharacters
fn single_string_characters<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, SingleStringCharacters> {

    many1(i, single_string_character).bind(|i, chars: Vec<SingleStringCharacter>| {

        let mut result: Vec<SingleStringCharactersItem> = vec![];

        let mut string_buf = String::new();

        for c in chars.into_iter() {

            match c {
                SingleStringCharacter::SourceCharacter(c) => {
                    let SourceCharacter(c) = c;
                    string_buf.push(c);
                    continue;
                }
                _ => {
                    string_buf.shrink_to_fit();
                    if string_buf.len() >= 1 {
                        let moved_string_buf = mem::replace(&mut string_buf, String::new());
                        result.push(SingleStringCharactersItem::String(moved_string_buf));
                    }
                }
            }

            match c {
                SingleStringCharacter::SourceCharacter(_) => {
                    unreachable!();
                }
                SingleStringCharacter::EscapeSequence(e) => {
                    result.push(SingleStringCharactersItem::EscapeSequence(e))
                }
                SingleStringCharacter::LineContinuation(l) => {
                    result.push(SingleStringCharactersItem::LineContinuation(l))
                }
            }
        }

        string_buf.shrink_to_fit();
        if string_buf.len() >= 1 {
            result.push(SingleStringCharactersItem::String(string_buf));
        }

        i.ret(SingleStringCharacters(result))
    })
}

enum DoubleStringCharacter {
    SourceCharacter(SourceCharacter),
    EscapeSequence(EscapeSequence),
    LineContinuation(LineContinuation),
}

// TODO: test case: empty input
// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-DoubleStringCharacter
fn double_string_character<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, DoubleStringCharacter> {

    #[inline]
    fn char_match<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, DoubleStringCharacter> {
        either(i,
               |i| {
            parse!{i;
                    (i -> token(i, b'"').map(|_| ())) <|>
                    (i -> token(i, b'\\').map(|_| ())) <|>
                    (i -> line_terminator(i).map(|_| ()));

                    ret {()}
                }
        },
               source_character)
            .bind(|i, result| {
                match result {
                    Either::Left(_) => {
                        // TODO: err message
                        i.err("Non-legal character.".into())
                    }
                    Either::Right(c) => i.ret(DoubleStringCharacter::SourceCharacter(c)),
                }
            })
    }

    parse!{i;
        let result = char_match() <|>
        (i -> token(i, b'\\').then(escape_sequence).map(DoubleStringCharacter::EscapeSequence)) <|>
        (i -> line_continuation(i).map(DoubleStringCharacter::LineContinuation));

        ret result
    }
}

enum SingleStringCharacter {
    SourceCharacter(SourceCharacter),
    EscapeSequence(EscapeSequence),
    LineContinuation(LineContinuation),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-SingleStringCharacter
fn single_string_character<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, SingleStringCharacter> {

    #[inline]
    fn char_match<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, SingleStringCharacter> {
        either(i,
               |i| {
            parse!{i;
                    (i -> token(i, b'\'').map(|_| ())) <|>
                    (i -> token(i, b'\\').map(|_| ())) <|>
                    (i -> line_terminator(i).map(|_| ()));

                    ret {()}
                }
        },
               source_character)
            .bind(|i, result| {
                match result {
                    Either::Left(_) => {
                        // TODO: err message
                        i.err("Non-legal character.".into())
                    }
                    Either::Right(c) => i.ret(SingleStringCharacter::SourceCharacter(c)),
                }
            })
    }

    parse!{i;
        let result = char_match() <|>
        (i -> token(i, b'\\').then(escape_sequence).map(SingleStringCharacter::EscapeSequence)) <|>
        (i -> line_continuation(i).map(SingleStringCharacter::LineContinuation));

        ret result
    }
}

struct LineContinuation(LineTerminatorSequence);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LineContinuation
fn line_continuation<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, LineContinuation> {
    token(i, b'\\').then(line_terminator_seq).map(|x| LineContinuation(x))
}

enum EscapeSequence {
    CharacterEscapeSequence(CharacterEscapeSequence),
    Zero,
    HexEscapeSequence(HexEscapeSequence),
    UnicodeEscapeSequence(UnicodeEscapeSequence),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-EscapeSequence
fn escape_sequence<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, EscapeSequence> {
    parse!{i;

        let result =
            (i -> character_escape_sequence(i).map(|x| EscapeSequence::CharacterEscapeSequence(x))) <|>
            (i -> token(i, b'0').map(|_| EscapeSequence::Zero)) <|>
            (i -> hex_escape_sequence(i).map(|x| EscapeSequence::HexEscapeSequence(x))) <|>
            (i -> unicode_escape_sequence(i).map(|x| EscapeSequence::UnicodeEscapeSequence(x)));

        ret result
    }
}

enum CharacterEscapeSequence {
    SingleEscapeCharacter(SingleEscapeCharacter),
    NonEscapeCharacter(NonEscapeCharacter),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-CharacterEscapeSequence
fn character_escape_sequence<I: U8Input>(i: ESInput<I>)
                                         -> ESParseResult<I, CharacterEscapeSequence> {
    or(i,
       |i| single_escape_character(i).map(|x| CharacterEscapeSequence::SingleEscapeCharacter(x)),
       |i| non_escape_character(i).map(|x| CharacterEscapeSequence::NonEscapeCharacter(x)))
}

// TODO: enum SingleEscapeCharacterItem { ... }
struct SingleEscapeCharacter(char);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-SingleEscapeCharacter
fn single_escape_character<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, SingleEscapeCharacter> {
    parse!{i;

        let t = token(b'\'') <|>
            token(b'"') <|>
            token(b'\\') <|>
            token(b'b') <|>
            token(b'f') <|>
            token(b'n') <|>
            token(b'r') <|>
            token(b't') <|>
            token(b'v');

        ret {
            SingleEscapeCharacter(t as char)
        }
    }
}

struct NonEscapeCharacter(char);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-NonEscapeCharacter
fn non_escape_character<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, NonEscapeCharacter> {
    either(i,
           |i| or(i, escape_character, |i| line_terminator(i).map(|_| ())),
           source_character)
        .bind(|i, result| {
            match result {
                Either::Left(_left) => {
                    // TODO: fix error
                    i.err("Reason TBA.".into())
                }
                Either::Right(c) => {
                    let SourceCharacter(c) = c;
                    i.ret(NonEscapeCharacter(c))
                }
            }
        })
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-EscapeCharacter
fn escape_character<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {
    parse!{i;
        (i -> single_escape_character(i).map(|_| ())) <|>
        (i -> decimal_digit(i).map(|_| ())) <|>
        (i -> token(i, b'x').map(|_| ())) <|>
        (i -> token(i, b'u').map(|_| ()));

        ret {
            // NOTE: satisfied results are not used
            ()
        }
    }
}

struct HexEscapeSequence(HexDigit, HexDigit);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-HexEscapeSequence
fn hex_escape_sequence<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, HexEscapeSequence> {
    parse!{i;

        token(b'x');

        let digit_1 = hex_digit();
        let digit_2 = hex_digit();

        ret {
            HexEscapeSequence(digit_1, digit_2)
            // TODO: remove
            // let mut result = String::with_capacity(2);
            // result.push(digit_1 as char);
            // result.push(digit_2 as char);
            // string_to_unicode_char(&result).unwrap()
        }
    }
}

enum UnicodeEscapeSequence {
    HexDigits(HexDigits),
    Hex4Digits(Hex4Digits),
}

// TODO: remove
// impl UnicodeEscapeSequence {
//     fn as_char(&self) -> char {
//         match *self {
//             UnicodeEscapeSequence::HexDigits(ref sequence) => {
//                 let &HexDigits(ref sequence) = sequence;
//                 string_to_unicode_char(sequence).unwrap()
//             }
//             UnicodeEscapeSequence::Hex4Digits(ref sequence) => {
//                 string_to_unicode_char(&sequence.as_string()).unwrap()
//             }
//         }
//     }
// }

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
    .bind(|i, result| {
        match result {
            Either::Left(sequence) => {

                // == 11.8.4.1 Static Semantics: Early Errors ==
                //
                // http://www.ecma-international.org/ecma-262/7.0/#sec-string-literals-static-semantics-early-errors
                if (
                        sequence.0[0] != HexDigit('0') &&
                        sequence.0.len() > 6) ||
                    sequence.mathematical_value() > 1114111 /* 10ffff */ {

                    let err_val = ErrorLocation::new(i.position(),
                        "Invalid unicode escape sequence. Expect to be less or equal to 10ffff.".to_string());

                    i.err(err_val.into())
                } else {
                    // TODO: remove
                    // let HexDigits(sequence) = sequence;
                    // let c = string_to_unicode_char(&sequence).unwrap();
                    i.ret(UnicodeEscapeSequence::HexDigits(sequence))
                }
            },
            Either::Right(c) => {
                i.ret(c)
            }
        }
    })
}

#[derive(PartialEq, Debug)]
struct Hex4Digits(HexDigit, HexDigit, HexDigit, HexDigit);

// impl Hex4Digits {
//     fn as_string(&self) -> String {
//         format!("{}{}{}{}", self.0, self.1, self.2, self.3)
//     }
// }

// http://www.ecma-international.org/ecma-262/7.0/#prod-Hex4Digits
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


enum TemplateSubstitutionTail {
    TemplateMiddle(TemplateMiddle),
    TemplateTail(TemplateTail)
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-TemplateSubstitutionTail
fn template_substitution_tail<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, TemplateSubstitutionTail> {
    or(i,
        |i| template_middle(i).map(|x| TemplateSubstitutionTail::TemplateMiddle),
        |i| template_tail(i).map(|x| TemplateSubstitutionTail::TemplateTail))
}

struct TemplateMiddle(/* } */
                      Option<TemplateCharacters> /* ${ */);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-TemplateMiddle
fn template_middle<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, TemplateMiddle> {
    parse!{i;
        token(b'}');

        let template_chars = option(|i| template_characters(i).map(Some), None);

        string(b"${");

        ret TemplateMiddle(template_chars)
    }
}

struct TemplateTail(/* } */
                    Option<TemplateCharacters> /* ` */);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-TemplateTail
fn template_tail<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, TemplateTail> {
    parse!{i;
        token(b'{');

        let template_chars = option(|i| template_characters(i).map(Some), None);

        token(b'`');

        ret TemplateTail(template_chars)
    }
}

struct TemplateCharacters(Vec<TemplateCharactersItem>);

enum TemplateCharactersItem {
    // many TemplateCharacter::SourceCharacter merged together
    String(String),
    DollarSign,
    EscapeSequence(EscapeSequence),
    LineContinuation(LineContinuation),
    LineTerminatorSequence(LineTerminatorSequence),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-TemplateCharacters
fn template_characters<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, TemplateCharacters> {

    many1(i, template_character).bind(|i, chars: Vec<TemplateCharacter>| {

        let mut result: Vec<TemplateCharactersItem> = vec![];

        let mut string_buf = String::new();

        for c in chars.into_iter() {

            match c {
                TemplateCharacter::SourceCharacter(c) => {
                    let SourceCharacter(c) = c;
                    string_buf.push(c);
                    continue;
                }
                _ => {
                    string_buf.shrink_to_fit();
                    if string_buf.len() >= 1 {
                        let moved_string_buf = mem::replace(&mut string_buf, String::new());
                        result.push(TemplateCharactersItem::String(moved_string_buf));
                    }
                }
            }

            match c {
                TemplateCharacter::SourceCharacter(_) => {
                    unreachable!();
                }
                TemplateCharacter::DollarSign => result.push(TemplateCharactersItem::DollarSign),
                TemplateCharacter::EscapeSequence(e) => {
                    result.push(TemplateCharactersItem::EscapeSequence(e))
                }
                TemplateCharacter::LineContinuation(l) => {
                    result.push(TemplateCharactersItem::LineContinuation(l))
                }
                TemplateCharacter::LineTerminatorSequence(l) => {
                    result.push(TemplateCharactersItem::LineTerminatorSequence(l))
                }
            }
        }

        string_buf.shrink_to_fit();
        if string_buf.len() >= 1 {
            result.push(TemplateCharactersItem::String(string_buf));
        }

        i.ret(TemplateCharacters(result))
    })
}

enum TemplateCharacter {
    SourceCharacter(SourceCharacter),
    DollarSign,
    EscapeSequence(EscapeSequence),
    LineContinuation(LineContinuation),
    LineTerminatorSequence(LineTerminatorSequence),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-TemplateCharacter
fn template_character<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, TemplateCharacter> {

    #[inline]
    fn dollar_sign<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, TemplateCharacter> {
        either(i,
               |i| token(i, b'$').then(|i| token(i, b'{')),
               |i| token(i, b'$'))
            .bind(|i, result| {
                match result {
                    // TODO: err message
                    Either::Left(_) => i.err("Found ${ which is not legal.".into()),
                    Either::Right(_) => i.ret(TemplateCharacter::DollarSign),
                }
            })
    }

    #[inline]
    fn source_char_match<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, TemplateCharacter> {
        either(i,
               |i| {
            parse!{i;
                    (i -> token(i, b'`').map(|_| ())) <|>
                    (i -> token(i, b'\\').map(|_| ())) <|>
                    (i -> line_terminator(i).map(|_| ()));

                    ret {()}
                }
        },
               source_character)
            .bind(|i, result| {
                match result {
                    Either::Left(_) => {
                        // TODO: err message
                        i.err("Non-legal character.".into())
                    }
                    Either::Right(c) => i.ret(TemplateCharacter::SourceCharacter(c)),
                }
            })
    }

    parse!{i;

        let result = dollar_sign() <|>
            (i -> token(i, b'\\').then(escape_sequence).map(TemplateCharacter::EscapeSequence)) <|>
            (i -> line_continuation(i).map(TemplateCharacter::LineContinuation)) <|>
            (i -> line_terminator_seq(i).map(TemplateCharacter::LineTerminatorSequence)) <|>
            source_char_match();

        ret result
    }
}

// == 12.1 Identifiers ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-identifiers

enum IdentifierReference {
    Identifier(Identifier),
    Yield,
}

#[inline]
fn yield_keyword<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, I::Buffer> {
    on_error(i, |i| string(i, b"yield"), |i| {
        let reason = format!("Expected yield keyword.");
        ErrorLocation::new(i.position(), reason)
    })
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IdentifierReference
fn identifier_reference<I: U8Input>(i: ESInput<I>,
                                    params: &EnumSet<Parameter>)
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

    if params.len() >= 2 {
        panic!("misuse of identifier_reference");
    }

    identifier(i).map(|ident| IdentifierReference::Identifier(ident))

}

enum BindingIdentifier {
    Identifier(Identifier),
    Yield,
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BindingIdentifier
fn binding_identifier<I: U8Input>(i: ESInput<I>,
                                  params: &EnumSet<Parameter>)
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

    if params.len() >= 2 {
        panic!("misuse of binding_identifier");
    }

    identifier(i).map(|ident| BindingIdentifier::Identifier(ident))

}

enum LabelIdentifier {
    Identifier(Identifier),
    Yield,
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LabelIdentifier
fn label_identifier<I: U8Input>(i: ESInput<I>,
                                params: &EnumSet<Parameter>)
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

struct Identifier(IdentifierName);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Identifier
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

// == 12.2 Primary Expression ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-primary-expression

enum PrimaryExpression {
    This,
    IdentifierReference(IdentifierReference),
    Literal(Literal),
    ArrayLiteral(ArrayLiteral),
    ObjectLiteral(ObjectLiteral),
    FunctionExpression(FunctionExpression), // TODO: other types
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-PrimaryExpression
fn primary_expression<I: U8Input>(i: ESInput<I>,
                                  params: &EnumSet<Parameter>)
                                  -> ESParseResult<I, PrimaryExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of primary_expression");
    }

    parse!{i;

        let result =

            on_error(
                |i| string(i, b"this").map(|_| PrimaryExpression::This),
            |i| {
                let reason = format!("Expected this keyword.");
                ErrorLocation::new(i.position(), reason)
            })

            <|>

            (i -> identifier_reference(i, &params)
                .map(|ident_ref| PrimaryExpression::IdentifierReference(ident_ref)))

            <|>
            (i -> literal(i).map(|literal| PrimaryExpression::Literal(literal)))
            <|>
            (i -> array_literal(i, &params).map(|arr_literal| PrimaryExpression::ArrayLiteral(arr_literal)))
            <|>
            (i -> object_literal(i, &params).map(|obj_literal| PrimaryExpression::ObjectLiteral(obj_literal)))
            <|>
            (i -> function_expression(i).map(|fn_expr| PrimaryExpression::FunctionExpression(fn_expr)));

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
    String(StringLiteral),
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

struct ArrayLiteral(/* [ (left bracket) */
                    Vec<CommonDelim>,
                    ArrayLiteralContents,
                    Vec<CommonDelim> /* ] (right bracket) */);

enum ArrayLiteralContents {
    Empty(Option<Elision>),
    List(ElementList),
    ListWithElision(ElementList,
                    Vec<CommonDelim>,
                    /* , (comma) */
                    Vec<CommonDelim>,
                    Elision),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ArrayLiteral
fn array_literal<I: U8Input>(i: ESInput<I>,
                             params: &EnumSet<Parameter>)
                             -> ESParseResult<I, ArrayLiteral> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of array_literal");
    }

    #[inline]
    fn array_literal_contents<I: U8Input>(i: ESInput<I>,
                                          params: &EnumSet<Parameter>)
                                          -> ESParseResult<I, ArrayLiteralContents> {
        parse!{i;

            // [ElementList_[?Yield]]
            // [ElementList_[?Yield] , Elision_opt]

            let list = element_list(&params);

            let maybe_end = option(|i| -> ESParseResult<I, Option<(_, _, _)>> {
                parse!{i;

                    let delim_1 = common_delim();

                    on_error(
                        |i| token(i, b','),
                        |i| {
                            let loc = i.position();
                            // TODO: proper err message?
                            ErrorLocation::new(loc, "Expected , delimeter here.".to_string())
                        }
                    );

                    let delim_2 = common_delim();
                    let elision = elision();

                    ret Some((delim_1, delim_2, elision))
                }
            }, None);

            ret {
                match maybe_end {
                    None => ArrayLiteralContents::List(list),
                    Some((delim_1, delim_2, elision)) => ArrayLiteralContents::ListWithElision(list, delim_1, delim_2, elision),
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
    Delim(Vec<CommonDelim>,
          /* , (comma) */
          Vec<CommonDelim>),
    ItemExpression(Option<Elision>, AssignmentExpression),
    ItemSpread(Option<Elision>, SpreadElement),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ElementList
fn element_list<I: U8Input>(i: ESInput<I>,
                            params: &EnumSet<Parameter>)
                            -> ESParseResult<I, ElementList> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of element_list");
    }

    type Accumulator = Rc<RefCell<Vec<ElementListItem>>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            on_error(
                |i| token(i, b','),
                |i| {
                    let loc = i.position();
                    // TODO: proper err message?
                    ErrorLocation::new(loc, "Expected , delimeter for array.".to_string())
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

            let elision_prefix = option(|i| elision(i).map(|x| Some(x)), None);

            let item = either(
                |i| {

                    let mut params = params.clone();
                    params.insert(Parameter::In);

                    assignment_expression(i, &params)
                },
                |i| {
                    spread_element(i, &params)
                }
            );

            ret {

                let item = match item {
                    Either::Left(x) => {
                        ElementListItem::ItemExpression(elision_prefix, x)
                    }
                    Either::Right(x) => {
                        ElementListItem::ItemSpread(elision_prefix, x)
                    }
                };

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
    Comma,
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Elision
fn elision<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Elision> {
    parse!{i;

        token(b',');

        let list: Vec<ElisionItem> = many(|i| -> ESParseResult<I, ElisionItem> {
            parse!{i;
                let l = (i -> common_delim(i).map(|c| ElisionItem::CommonDelim(c))) <|>
                (i -> token(i, b',').map(|_| ElisionItem::Comma));
                ret l
            }
        });

        ret Elision(list)
    }
}

struct SpreadElement(AssignmentExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-SpreadElement
fn spread_element<I: U8Input>(i: ESInput<I>,
                              params: &EnumSet<Parameter>)
                              -> ESParseResult<I, SpreadElement> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of spread_element");
    }

    parse!{i;

        // spread operator
        (i -> string(i, b"...").map_err(|_| ErrorChain::from("Expected spread operator.")));

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
struct ObjectLiteral(/* { (left curly bracket) */
                     Vec<CommonDelim>,
                     ObjectLiteralContents,
                     Vec<CommonDelim> /* } (right curly bracket) */);

enum ObjectLiteralContents {
    Empty,
    PropertyDefinitionList(PropertyDefinitionList),
    PropertyDefinitionListTrailingComma(PropertyDefinitionList, Vec<CommonDelim>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ObjectLiteral
fn object_literal<I: U8Input>(i: ESInput<I>,
                              params: &EnumSet<Parameter>)
                              -> ESParseResult<I, ObjectLiteral> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of object_literal");
    }

    #[inline]
    fn object_literal_contents<I: U8Input>(i: ESInput<I>,
                                           params: &EnumSet<Parameter>)
                                           -> ESParseResult<I, ObjectLiteralContents> {
        parse!{i;

            let list = property_definition_list(&params);

            let trailing_comma = option(|i| -> ESParseResult<I, _> {
                parse!{i;
                    let delim = common_delim();
                    token(b',');

                    ret Some(delim)
                }
            }, None);

            ret {
                match trailing_comma {
                    None => ObjectLiteralContents::PropertyDefinitionList(list),
                    Some(delim) => ObjectLiteralContents::PropertyDefinitionListTrailingComma(list, delim)
                }
            }
        }
    }

    parse!{i;

        token(b'{');
        let delim_left = common_delim();

        let contents = option(|i| object_literal_contents(i, &params), ObjectLiteralContents::Empty);

        let delim_right = common_delim();
        token(b'}');

        ret ObjectLiteral(delim_left, contents, delim_right)
    }
}

struct PropertyDefinitionList(Vec<PropertyDefinitionListItem>);

enum PropertyDefinitionListItem {
    Delim(Vec<CommonDelim>,
          /* , (comma) */
          Vec<CommonDelim>),
    PropertyDefinition(PropertyDefinition),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-PropertyDefinitionList
fn property_definition_list<I: U8Input>(i: ESInput<I>,
                                        params: &EnumSet<Parameter>)
                                        -> ESParseResult<I, PropertyDefinitionList> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of property_definition_list");
    }

    type Accumulator = Rc<RefCell<Vec<PropertyDefinitionListItem>>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            on_error(
                |i| token(i, b','),
                |i| {
                    let loc = i.position();
                    // TODO: proper err message?
                    ErrorLocation::new(loc, "Expected , here.".to_string())
                }
            );

            let delim_2 = common_delim();

            ret {
                accumulator.borrow_mut().push(PropertyDefinitionListItem::Delim(delim_1, delim_2));
                ()
            }
        }
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;

            let item = property_definition(&params);

            ret {
                accumulator.borrow_mut().push(PropertyDefinitionListItem::PropertyDefinition(item));
                ()
            }
        }
    };

    parse!{i;

        let list = parse_list(
            delimiter,
            reducer
        );

        ret PropertyDefinitionList(list)
    }
}


enum PropertyDefinition {
    IdentifierReference(IdentifierReference),
    CoverInitializedName(CoverInitializedName),
    PropertyName(PropertyName,
                 Vec<CommonDelim>,
                 /* : */
                 Vec<CommonDelim>,
                 AssignmentExpression),
    MethodDefinition(MethodDefinition),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-PropertyDefinition
fn property_definition<I: U8Input>(i: ESInput<I>,
                                   params: &EnumSet<Parameter>)
                                   -> ESParseResult<I, PropertyDefinition> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of property_definition");
    }

    #[inline]
    fn prop_name<I: U8Input>(i: ESInput<I>,
                             params: &EnumSet<Parameter>)
                             -> ESParseResult<I, PropertyDefinition> {

        let mut expr_params = params.clone();
        expr_params.insert(Parameter::In);
        let expr_params = expr_params;

        parse!{i;

            let name = property_name(&params);

            let delim_1 = common_delim();
            token(b':');
            let delim_2 = common_delim();

            let expr = assignment_expression(&expr_params);

            ret PropertyDefinition::PropertyName(name, delim_1, delim_2, expr)
        }
    }

    parse!{i;

        let prop_def =
            (i -> identifier_reference(i, &params).map(|x| PropertyDefinition::IdentifierReference(x)))
            <|>
            (i -> cover_initialized_name(i, &params).map(|x| PropertyDefinition::CoverInitializedName(x)))
            <|>
            prop_name(&params)
            <|>
            (i -> method_definition(i, &params).map(|x| PropertyDefinition::MethodDefinition(x)));

        ret prop_def
    }
}

enum PropertyName {
    LiteralPropertyName(LiteralPropertyName),
    ComputedPropertyName(ComputedPropertyName),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-PropertyName
fn property_name<I: U8Input>(i: ESInput<I>,
                             params: &EnumSet<Parameter>)
                             -> ESParseResult<I, PropertyName> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of property_name");
    }

    parse!{i;

        let prop_name = (i -> literal_property_name(i).map(|x| PropertyName::LiteralPropertyName(x)))
        <|>
        (i -> computed_property_name(i, &params).map(|x| PropertyName::ComputedPropertyName(x)));

        ret prop_name
    }
}

enum LiteralPropertyName {
    IdentifierName(IdentifierName),
    StringLiteral(StringLiteral),
    NumericLiteral(NumericLiteral),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LiteralPropertyName
fn literal_property_name<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, LiteralPropertyName> {
    parse!{i;

        let literal_prop_name =
            (i -> identifier_name(i).map(|x| LiteralPropertyName::IdentifierName(x)))
            <|>
            (i -> string_literal(i).map(|x| LiteralPropertyName::StringLiteral(x)))
            <|>
            (i -> numeric_literal(i).map(|x| LiteralPropertyName::NumericLiteral(x)));

        ret literal_prop_name
    }
}

struct ComputedPropertyName(/* [ */
                            Vec<CommonDelim>,
                            AssignmentExpression,
                            Vec<CommonDelim> /* ] */);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ComputedPropertyName
fn computed_property_name<I: U8Input>(i: ESInput<I>,
                                      params: &EnumSet<Parameter>)
                                      -> ESParseResult<I, ComputedPropertyName> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of computed_property_name");
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

struct CoverInitializedName(IdentifierReference, Vec<CommonDelim>, Initializer);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-CoverInitializedName
fn cover_initialized_name<I: U8Input>(i: ESInput<I>,
                                      params: &EnumSet<Parameter>)
                                      -> ESParseResult<I, CoverInitializedName> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
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

struct Initializer(/* = */
                   Vec<CommonDelim>,
                   AssignmentExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Initializer
fn initializer<I: U8Input>(i: ESInput<I>,
                           params: &EnumSet<Parameter>)
                           -> ESParseResult<I, Initializer> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::In) ||
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

// TODO: test
// TODO: http://www.ecma-international.org/ecma-262/7.0/#sec-template-literals

// == 12.3 Left-Hand-Side Expressions ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-left-hand-side-expressions

struct MemberExpression;

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-MemberExpression
fn member_expression<I: U8Input>(i: ESInput<I>,
                                 params: &EnumSet<Parameter>)
                                 -> ESParseResult<I, MemberExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of member_expression");
    }

    // TODO: complete

    i.ret(MemberExpression)
}

// TODO: test
// TODO: http://www.ecma-international.org/ecma-262/7.0/#prod-SuperProperty

struct MetaProperty(NewTarget);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-MetaProperty
fn meta_property<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, MetaProperty> {
    new_target(i).map(|x| MetaProperty(x))
}

struct NewTarget(/* new */
                 Vec<CommonDelim>,
                 /* . (dot) */
                 Vec<CommonDelim> /* target */);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-NewTarget
fn new_target<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, NewTarget> {
    parse!{i;

        string(b"new");

        let delim_1 = common_delim();

        string(b".");

        let delim_2 = common_delim();

        string(b"target");


        ret {
            NewTarget(delim_1, delim_2)
        }
    }
}

enum NewExpression {
    MemberExpression(MemberExpression),
    NewExpression(/* new */
                  Vec<CommonDelim>,
                  Box<NewExpression>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-NewExpression
fn new_expression<I: U8Input>(i: ESInput<I>,
                              params: &EnumSet<Parameter>)
                              -> ESParseResult<I, NewExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of new_expression");
    }

    or(i,
       |i| {
        parse!{i;
                (i -> string(i, b"new"));

                let delim = common_delim();

                let new_expr = new_expression(&params);

                ret {
                    NewExpression::NewExpression(delim, Box::new(new_expr))
                }
            }
    },
       |i| member_expression(i, &params).map(|x| NewExpression::MemberExpression(x)))
}

enum CallExpressionHead {
    FunctionCall(MemberExpression, Vec<CommonDelim>, Arguments),
    SuperCall(SuperCall),
}

struct CallExpression(CallExpressionHead, Vec<CallExpressionRest>);

impl CallExpression {
    fn new(rhs_val: CallExpressionItem) -> Self {
        match rhs_val {
            CallExpressionItem::HeadItem(head) => CallExpression(head, vec![]),
            CallExpressionItem::RestItem(_) => panic!("invariant violation"),
        }
    }

    fn add_item(self, operator_delim: CallExpressionDelim, rhs_val: CallExpressionItem) -> Self {

        let CallExpression(head, rest) = self;
        let mut rest = rest;

        let CallExpressionDelim(delim) = operator_delim;

        let rest_item = match rhs_val {
            CallExpressionItem::HeadItem(_head) => panic!("invariant violation"),
            CallExpressionItem::RestItem(rest_item) => rest_item,
        };

        let rhs = CallExpressionRest(delim, rest_item);

        rest.push(rhs);

        CallExpression(head, rest)
    }
}

enum CallExpressionRestItem {
    FunctionCall(Arguments),
    PropertyAccessorBracket(/* [] */ Vec<CommonDelim>, ExpressionList, Vec<CommonDelim> /* ] */),
    PropertyAccessorDot(/* . */ Vec<CommonDelim>, IdentifierName),
    // TODO: complete
    // TaggedTemplate(TemplateLiteral)
}

struct CallExpressionRest(Vec<CommonDelim>, CallExpressionRestItem);

struct CallExpressionDelim(Vec<CommonDelim>);

enum CallExpressionItem {
    HeadItem(CallExpressionHead),
    RestItem(CallExpressionRestItem),
}

generate_list_parser!(
    CallExpression;
    CallExpressionRest;
    CallExpressionState;
    CallExpressionDelim;
    CallExpressionItem);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-CallExpression
fn call_expression<I: U8Input>(i: ESInput<I>,
                               params: &EnumSet<Parameter>)
                               -> ESParseResult<I, CallExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of call_expression");
    }

    type Accumulator = Rc<RefCell<CallExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim = common_delim();

            ret {
                let delim = CallExpressionDelim(delim);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    let mut expr_params = params.clone();
    expr_params.insert(Parameter::In);
    let expr_params = expr_params;

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {

        let is_initial = {
            accumulator.borrow().is_initial()
        };

        if is_initial {
            parse!{i;

                let head = or(
                    |i| super_call(i, &params).map(|x| CallExpressionHead::SuperCall(x)),
                    |i| {
                        parse!{i;
                            let member = member_expression(&params);
                            let delim = common_delim();
                            let args = arguments(&params);

                            ret CallExpressionHead::FunctionCall(member, delim, args)
                        }
                    });

                ret {
                    let rhs = CallExpressionItem::HeadItem(head);
                    accumulator.borrow_mut().add_item(rhs);
                    ()
                }
            }
        } else {
            parse!{i;

                let rest_item =
                    (i -> {
                        arguments(i, &params)
                            .map(|x| CallExpressionRestItem::FunctionCall(x))
                    }) <|>
                    (i -> {
                        parse!{i;

                            string(b"[");
                            let delim_left = common_delim();

                            let expr = expression(&expr_params);

                            let delim_right = common_delim();
                            string(b"]");

                            ret CallExpressionRestItem::PropertyAccessorBracket(delim_left, expr, delim_right)
                        }
                    }) <|>
                    (i -> {
                        parse!{i;
                            string(b".");
                            let delim_left = common_delim();
                            let ident = identifier_name();

                            ret CallExpressionRestItem::PropertyAccessorDot(delim_left, ident)
                        }
                    });
                    // TODO: tagged template

                ret {
                    let rhs = CallExpressionItem::RestItem(rest_item);
                    accumulator.borrow_mut().add_item(rhs);
                    ()
                }
            }
        }

    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

struct SuperCall(/* super */
                 Vec<CommonDelim>,
                 Arguments);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-SuperCall
fn super_call<I: U8Input>(i: ESInput<I>,
                          params: &EnumSet<Parameter>)
                          -> ESParseResult<I, SuperCall> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of super_call");
    }

    parse!{i;

        string(b"super");

        let delim = common_delim();

        let args = arguments(params);

        ret SuperCall(delim, args)
    }
}

enum Arguments {
    NoArguments(Vec<CommonDelim>),
    Arguments(Vec<CommonDelim>, ArgumentList, Vec<CommonDelim>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Arguments
fn arguments<I: U8Input>(i: ESInput<I>,
                         params: &EnumSet<Parameter>)
                         -> ESParseResult<I, Arguments> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of arguments");
    }

    or(i,
       |i| {
        parse!{i;

                string(b"(");
                let delim = common_delim();
                string(b")");

                ret Arguments::NoArguments(delim)
            }
    },
       |i| {
        parse!{i;

                string(b"(");
                let delim_1 = common_delim();

                let args_list = arguments_list(&params);

                let delim_2 = common_delim();
                string(b")");

                ret Arguments::Arguments(delim_1, args_list, delim_2)
            }
    })
}

enum ArgumentListItem {
    AssignmentExpression(AssignmentExpression),
    RestAssignmentExpression(/* ... */
                             Vec<CommonDelim>,
                             AssignmentExpression),
}

struct ArgumentList(ArgumentListItem, Vec<ArgumentListRest>);

impl ArgumentList {
    fn new(rhs_val: ArgumentListItem) -> Self {
        ArgumentList(rhs_val, vec![])
    }

    fn add_item(self, operator_delim: ArgumentListDelim, rhs_val: ArgumentListItem) -> Self {

        let ArgumentList(head, rest) = self;
        let mut rest = rest;

        let ArgumentListDelim(delim_1, delim_2) = operator_delim;

        let rhs = ArgumentListRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        ArgumentList(head, rest)
    }
}

struct ArgumentListRest(Vec<CommonDelim>,
                        /* , (comma) */
                        Vec<CommonDelim>,
                        ArgumentListItem);

struct ArgumentListDelim(Vec<CommonDelim>,
                         /* , (comma) */
                         Vec<CommonDelim>);

generate_list_parser!(
    ArgumentList;
    ArgumentListRest;
    ArgumentListState;
    ArgumentListDelim;
    ArgumentListItem);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ArgumentList
fn arguments_list<I: U8Input>(i: ESInput<I>,
                              params: &EnumSet<Parameter>)
                              -> ESParseResult<I, ArgumentList> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of arguments_list");
    }

    type Accumulator = Rc<RefCell<ArgumentListState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            on_error(
                |i| token(i, b','),
                |i| {
                    let loc = i.position();
                    // TODO: proper err message?
                    ErrorLocation::new(loc, "Expected , here.".to_string())
                }
            );

            let delim_2 = common_delim();

            ret {
                let delim = ArgumentListDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {

        let mut params = params.clone();
        params.insert(Parameter::In);

        option(i,
               |i| {
                   string(i, b"...")
                       .then(common_delim)
                       .map(|x| Some(x))
               },
               None)
            .bind(|i, delim| assignment_expression(i, &params).map(|x| (delim, x)))
            .bind(|i, (rest_op, assignment_expression)| -> ESParseResult<I, ()> {
                let rhs = if let Some(delim) = rest_op {
                    ArgumentListItem::RestAssignmentExpression(delim, assignment_expression)
                } else {
                    ArgumentListItem::AssignmentExpression(assignment_expression)
                };

                accumulator.borrow_mut().add_item(rhs);
                i.ret(())
            })
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

enum LeftHandSideExpression {
    NewExpression(NewExpression),
    CallExpression(CallExpression),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LeftHandSideExpression
fn left_hand_side_expression<I: U8Input>(i: ESInput<I>,
                                         params: &EnumSet<Parameter>)
                                         -> ESParseResult<I, LeftHandSideExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of left_hand_side_expression");
    }

    or(i,
       |i| new_expression(i, &params).map(|x| LeftHandSideExpression::NewExpression(x)),
       |i| call_expression(i, &params).map(|x| LeftHandSideExpression::CallExpression(x)))
}

// == 12.4 Update Expressions ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-update-expressions

enum UpdateExpression {
    LeftHandSideExpression(LeftHandSideExpression),
    PostIncrement(LeftHandSideExpression,
                  /* ++ */
                  Vec<CommonDelim>),
    PostDecrement(LeftHandSideExpression,
                  /* -- */
                  Vec<CommonDelim>),
    PreIncrement(Vec<CommonDelim>,
                 /* ++ */
                 UnaryExpression),
    PreDecrement(Vec<CommonDelim>,
                 /* -- */
                 UnaryExpression),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-UpdateExpression
fn update_expression<I: U8Input>(i: ESInput<I>,
                                 params: &EnumSet<Parameter>)
                                 -> ESParseResult<I, UpdateExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of update_expression");
    }

    enum PreOperator {
        PreIncrement,
        PreDecrement,
    }

    enum PostOperator {
        PostIncrement(Vec<CommonDelim>),
        PostDecrement(Vec<CommonDelim>),
        None,
    }

    or(i,
       |i| {
        parse!{i;

                let operator = (i -> string(i, b"++").map(|_| PreOperator::PreIncrement)) <|>
                    (i -> string(i, b"--").map(|_| PreOperator::PreDecrement));

                let delim = common_delim();

                let unary_expr = unary_expression(&params);

                ret {
                    match operator {
                        PreOperator::PreIncrement => UpdateExpression::PreIncrement(delim, unary_expr),
                        PreOperator::PreDecrement => UpdateExpression::PreDecrement(delim, unary_expr),
                    }
                }
            }
    },
       |i| {
        parse!{i;

                let lhs_expr = left_hand_side_expression(&params);

                let operator = (i -> {
                    // TODO: test this case
                    common_delim_no_line_term(i)
                        .bind(|i, delim| {
                            string(i, b"++")
                                .map(|_| PostOperator::PostIncrement(delim))
                        })
                }) <|>
                (i -> {
                    // TODO: test this case
                    common_delim_no_line_term(i)
                        .bind(|i, delim| {
                            string(i, b"--")
                                .map(|_| PostOperator::PostDecrement(delim))
                        })
                }) <|>
                (i -> i.ret(PostOperator::None));

                ret {
                    match operator {
                        PostOperator::PostIncrement(delim) => UpdateExpression::PostIncrement(lhs_expr, delim),
                        PostOperator::PostDecrement(delim) => UpdateExpression::PostDecrement(lhs_expr, delim),
                        PostOperator::None => UpdateExpression::LeftHandSideExpression(lhs_expr),
                    }
                }
            }
    })
}

// == 12.5 Unary Operator ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-unary-operators

enum UnaryExpression {
    UpdateExpression(Box<UpdateExpression>),
    Delete(Vec<CommonDelim>, Box<UnaryExpression>),
    Void(Vec<CommonDelim>, Box<UnaryExpression>),
    TypeOf(Vec<CommonDelim>, Box<UnaryExpression>),
    Plus(Vec<CommonDelim>, Box<UnaryExpression>),
    Minus(Vec<CommonDelim>, Box<UnaryExpression>),
    Tilde(Vec<CommonDelim>, Box<UnaryExpression>),
    ExclamationMark(Vec<CommonDelim>, Box<UnaryExpression>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-UnaryExpression
fn unary_expression<I: U8Input>(i: ESInput<I>,
                                params: &EnumSet<Parameter>)
                                -> ESParseResult<I, UnaryExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of unary_expression");
    }

    enum UnaryExpressionOperator {
        Delete, // delete
        Void, // void
        TypeOf, // typeof
        Plus, // +
        Minus, // -
        Tilde, // ~
        ExclamationMark, // !
    }

    or(i,
       |i| {
        parse!{i;

                let operator = (i -> string(i, b"delete").map(|_| UnaryExpressionOperator::Delete)) <|>
                    (i -> string(i, b"void").map(|_| UnaryExpressionOperator::Void)) <|>
                    (i -> string(i, b"typeof").map(|_| UnaryExpressionOperator::TypeOf)) <|>
                    (i -> string(i, b"+").map(|_| UnaryExpressionOperator::Plus)) <|>
                    (i -> string(i, b"-").map(|_| UnaryExpressionOperator::Minus)) <|>
                    (i -> string(i, b"~").map(|_| UnaryExpressionOperator::Tilde)) <|>
                    (i -> string(i, b"!").map(|_| UnaryExpressionOperator::ExclamationMark));

                let delim = common_delim();

                let unary_expr = unary_expression(&params);

                ret {
                    match operator {
                        UnaryExpressionOperator::Delete => UnaryExpression::Delete(delim, Box::new(unary_expr)),
                        UnaryExpressionOperator::Void => UnaryExpression::Void(delim, Box::new(unary_expr)),
                        UnaryExpressionOperator::TypeOf => UnaryExpression::TypeOf(delim, Box::new(unary_expr)),
                        UnaryExpressionOperator::Plus => UnaryExpression::Plus(delim, Box::new(unary_expr)),
                        UnaryExpressionOperator::Minus => UnaryExpression::Minus(delim, Box::new(unary_expr)),
                        UnaryExpressionOperator::Tilde => UnaryExpression::Tilde(delim, Box::new(unary_expr)),
                        UnaryExpressionOperator::ExclamationMark => UnaryExpression::ExclamationMark(delim, Box::new(unary_expr)),
                    }
                }
            }
    },
       |i| update_expression(i, &params).map(|x| UnaryExpression::UpdateExpression(Box::new(x))))
}

// == 12.6 Exponentiation Operator ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-exp-operator

enum ExponentiationExpression {
    UnaryExpression(UnaryExpression),
    UpdateExpression(UpdateExpression,
                     Vec<CommonDelim>,
                     Vec<CommonDelim>,
                     Box<ExponentiationExpression>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ExponentiationExpression
fn exponentiation_expression<I: U8Input>(i: ESInput<I>,
                                         params: &EnumSet<Parameter>)
                                         -> ESParseResult<I, ExponentiationExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of exponentiation_expression");
    }

    or(i,
       |i| unary_expression(i, &params).map(|x| ExponentiationExpression::UnaryExpression(x)),
       |i| {
        parse!{i;

                let update_expr = update_expression(&params);

                let delim_1 = common_delim();
                let _exp_op = string(b"**");
                let delim_2 = common_delim();

                let exp_expr = exponentiation_expression(&params);

                ret {
                    ExponentiationExpression::UpdateExpression(update_expr, delim_1, delim_2, Box::new(exp_expr))
                }
            }
    })
}

// == 12.7 Multiplicative Operators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-multiplicative-operators

struct MultiplicativeExpression(ExponentiationExpression, Vec<MultiplicativeExpressionRest>);

impl MultiplicativeExpression {
    fn new(rhs_val: ExponentiationExpression) -> Self {
        MultiplicativeExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: MultiplicativeExpressionDelim,
                rhs_val: ExponentiationExpression)
                -> Self {

        let MultiplicativeExpression(head, rest) = self;
        let mut rest = rest;

        let MultiplicativeExpressionDelim(delim_1, operator, delim_2) = operator_delim;

        let rhs = MultiplicativeExpressionRest(delim_1, operator, delim_2, rhs_val);

        rest.push(rhs);

        MultiplicativeExpression(head, rest)
    }
}

struct MultiplicativeExpressionRest(Vec<CommonDelim>,
                                    MultiplicativeExpressionOperator,
                                    Vec<CommonDelim>,
                                    ExponentiationExpression);

enum MultiplicativeExpressionOperator {
    Multiplication, // *
    Division, // /
    Remainder, // %
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-MultiplicativeOperator
#[inline]
fn multiplicative_operator<I: U8Input>(i: ESInput<I>)
                                       -> ESParseResult<I, MultiplicativeExpressionOperator> {
    parse!{i;

        let operator = (i -> string(i, b"*").map(|_| MultiplicativeExpressionOperator::Multiplication)) <|>
            (i -> string(i, b"/").map(|_| MultiplicativeExpressionOperator::Division)) <|>
            (i -> string(i, b"%").map(|_| MultiplicativeExpressionOperator::Remainder));

        ret operator
    }
}

struct MultiplicativeExpressionDelim(Vec<CommonDelim>,
                                     MultiplicativeExpressionOperator,
                                     Vec<CommonDelim>);

generate_list_parser!(
    MultiplicativeExpression;
    MultiplicativeExpressionRest;
    MultiplicativeExpressionState;
    MultiplicativeExpressionDelim;
    ExponentiationExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-MultiplicativeExpression
fn multiplicative_expression<I: U8Input>(i: ESInput<I>,
                                         params: &EnumSet<Parameter>)
                                         -> ESParseResult<I, MultiplicativeExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of multiplicative_expression");
    }

    type Accumulator = Rc<RefCell<MultiplicativeExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            let multiplicative_operator = on_error(
                multiplicative_operator,
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected one of these operators: *, /, or %.".to_string())
                }
            );
            let delim_2 = common_delim();
            ret {
                let delim = MultiplicativeExpressionDelim(delim_1, multiplicative_operator, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = exponentiation_expression(&params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// == 12.8 Additive Operators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-additive-operators

struct AdditiveExpression(MultiplicativeExpression, Vec<AdditiveExpressionRest>);

impl AdditiveExpression {
    fn new(rhs_val: MultiplicativeExpression) -> Self {
        AdditiveExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: AdditiveExpressionDelim,
                rhs_val: MultiplicativeExpression)
                -> Self {

        let AdditiveExpression(head, rest) = self;
        let mut rest = rest;

        let AdditiveExpressionDelim(delim_1, operator, delim_2) = operator_delim;

        let rhs = AdditiveExpressionRest(delim_1, operator, delim_2, rhs_val);

        rest.push(rhs);

        AdditiveExpression(head, rest)
    }
}

struct AdditiveExpressionRest(Vec<CommonDelim>,
                              AdditiveExpressionOperator,
                              Vec<CommonDelim>,
                              MultiplicativeExpression);

enum AdditiveExpressionOperator {
    Add,
    Subtract,
}

struct AdditiveExpressionDelim(Vec<CommonDelim>, AdditiveExpressionOperator, Vec<CommonDelim>);

generate_list_parser!(
    AdditiveExpression;
    AdditiveExpressionRest;
    AdditiveExpressionState;
    AdditiveExpressionDelim;
    MultiplicativeExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-AdditiveExpression
fn additive_expression<I: U8Input>(i: ESInput<I>,
                                   params: &EnumSet<Parameter>)
                                   -> ESParseResult<I, AdditiveExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of additive_expression");
    }

    type Accumulator = Rc<RefCell<AdditiveExpressionState>>;

    #[inline]
    fn additive_operator<I: U8Input>(i: ESInput<I>)
                                     -> ESParseResult<I, AdditiveExpressionOperator> {
        parse!{i;

            let operator = (i -> string(i, b"+").map(|_| AdditiveExpressionOperator::Add)) <|>
                (i -> string(i, b"-").map(|_| AdditiveExpressionOperator::Subtract));

            ret operator
        }
    }

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            let additive_operator = on_error(
                additive_operator,
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected one of these operators: +, or -.".to_string())
                }
            );
            let delim_2 = common_delim();
            ret {
                let delim = AdditiveExpressionDelim(delim_1, additive_operator, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = multiplicative_expression(&params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// == 12.9 Bitwise Shift Operators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-bitwise-shift-operators

struct ShiftExpression(AdditiveExpression, Vec<ShiftExpressionRest>);

impl ShiftExpression {
    fn new(rhs_val: AdditiveExpression) -> Self {
        ShiftExpression(rhs_val, vec![])
    }

    fn add_item(self, operator_delim: ShiftExpressionDelim, rhs_val: AdditiveExpression) -> Self {

        let ShiftExpression(head, rest) = self;
        let mut rest = rest;

        let ShiftExpressionDelim(delim_1, operator, delim_2) = operator_delim;

        let rhs = ShiftExpressionRest(delim_1, operator, delim_2, rhs_val);

        rest.push(rhs);

        ShiftExpression(head, rest)
    }
}

struct ShiftExpressionRest(Vec<CommonDelim>,
                           ShiftExpressionOperator,
                           Vec<CommonDelim>,
                           AdditiveExpression);

enum ShiftExpressionOperator {
    // TODO: better semantic names
    Left, // <<
    SignRight, // >>
    Right, // >>>
}

struct ShiftExpressionDelim(Vec<CommonDelim>, ShiftExpressionOperator, Vec<CommonDelim>);

generate_list_parser!(
    ShiftExpression;
    ShiftExpressionRest;
    ShiftExpressionState;
    ShiftExpressionDelim;
    AdditiveExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ShiftExpression
fn shift_expression<I: U8Input>(i: ESInput<I>,
                                params: &EnumSet<Parameter>)
                                -> ESParseResult<I, ShiftExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of shift_expression");
    }

    type Accumulator = Rc<RefCell<ShiftExpressionState>>;

    #[inline]
    fn bitwise_operator<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ShiftExpressionOperator> {
        parse!{i;

            let operator = (i -> string(i, b"<<").map(|_| ShiftExpressionOperator::Left)) <|>
                (i -> string(i, b">>>").map(|_| ShiftExpressionOperator::Right)) <|>
                (i -> string(i, b">>").map(|_| ShiftExpressionOperator::SignRight));

            ret operator
        }
    }

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            let bitwise_operator = on_error(
                bitwise_operator,
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected one of these operators: <<, >>, or >>>.".to_string())
                }
            );
            let delim_2 = common_delim();
            ret {
                let delim = ShiftExpressionDelim(delim_1, bitwise_operator, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = additive_expression(&params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// == 12.10 Relational Operators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-relational-operators

struct RelationalExpression(ShiftExpression, Vec<RelationalExpressionRest>);

impl RelationalExpression {
    fn new(rhs_val: ShiftExpression) -> Self {
        RelationalExpression(rhs_val, vec![])
    }

    fn add_item(self, operator_delim: RelationalExpressionDelim, rhs_val: ShiftExpression) -> Self {

        let RelationalExpression(head, rest) = self;
        let mut rest = rest;

        let RelationalExpressionDelim(delim_1, operator, delim_2) = operator_delim;

        let rhs = RelationalExpressionRest(delim_1, operator, delim_2, rhs_val);

        rest.push(rhs);

        RelationalExpression(head, rest)
    }
}

struct RelationalExpressionRest(Vec<CommonDelim>,
                                RelationalExpressionOperator,
                                Vec<CommonDelim>,
                                ShiftExpression);

enum RelationalExpressionOperator {
    Less,
    Greater,
    LessOrEqual,
    GreaterOrEqual,
    InstanceOf,
    In,
}

struct RelationalExpressionDelim(Vec<CommonDelim>, RelationalExpressionOperator, Vec<CommonDelim>);

generate_list_parser!(
    RelationalExpression;
    RelationalExpressionRest;
    RelationalExpressionState;
    RelationalExpressionDelim;
    ShiftExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-RelationalExpression
fn relational_expression<I: U8Input>(i: ESInput<I>,
                                     params: &EnumSet<Parameter>)
                                     -> ESParseResult<I, RelationalExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::In) ||
         params.contains(&Parameter::Yield)) {
        panic!("misuse of relational_expression");
    }

    let has_in = params.contains(&Parameter::In);

    let shift_params = {
        let mut params = EnumSet::new();
        if params.contains(&Parameter::Yield) {
            params.insert(Parameter::Yield);
        }
        params
    };

    type Accumulator = Rc<RefCell<RelationalExpressionState>>;

    #[inline]
    fn relational_operator<I: U8Input>(i: ESInput<I>,
                                       has_in: bool)
                                       -> ESParseResult<I, RelationalExpressionOperator> {
        parse!{i;

            let operator = (i -> string(i, b"<=").map(|_| RelationalExpressionOperator::LessOrEqual)) <|>
                (i -> string(i, b">=").map(|_| RelationalExpressionOperator::GreaterOrEqual)) <|>
                (i -> string(i, b"instanceof").map(|_| RelationalExpressionOperator::GreaterOrEqual)) <|>
                (i -> {
                    if has_in {
                        string(i, b"in").map(|_| RelationalExpressionOperator::GreaterOrEqual)
                    } else {
                        i.err(ErrorChain::new(""))
                    }
                }) <|>
                (i -> string(i, b">").map(|_| RelationalExpressionOperator::Greater)) <|>
                (i -> string(i, b"<").map(|_| RelationalExpressionOperator::Less));

            ret operator
        }
    };

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>,
                             accumulator: Accumulator,
                             has_in: bool)
                             -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            let relational_operator = on_error(
                |i| relational_operator(i, has_in),
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected one of these operators: <, >, <=, >=, instanceof, or in.".to_string())
                }
            );
            let delim_2 = common_delim();
            ret {
                let delim = RelationalExpressionDelim(delim_1, relational_operator, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = shift_expression(&shift_params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, |i, acc| delimiter(i, acc, has_in), reducer).map(|x| x.unwrap())
}

// == 12.11 Equality Operators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-equality-operators

struct EqualityExpression(RelationalExpression, Vec<EqualityExpressionRest>);

impl EqualityExpression {
    fn new(rhs_val: RelationalExpression) -> Self {
        EqualityExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: EqualityExpressionDelim,
                rhs_val: RelationalExpression)
                -> Self {

        let EqualityExpression(head, rest) = self;
        let mut rest = rest;

        let EqualityExpressionDelim(delim_1, operator, delim_2) = operator_delim;

        let rhs = EqualityExpressionRest(delim_1, operator, delim_2, rhs_val);

        rest.push(rhs);

        EqualityExpression(head, rest)
    }
}

struct EqualityExpressionRest(Vec<CommonDelim>,
                              EqualityExpressionOperator,
                              Vec<CommonDelim>,
                              RelationalExpression);

enum EqualityExpressionOperator {
    Equality,
    Inequality,
    StrictEquality,
    StrictInequality,
}

struct EqualityExpressionDelim(Vec<CommonDelim>, EqualityExpressionOperator, Vec<CommonDelim>);

generate_list_parser!(
    EqualityExpression;
    EqualityExpressionRest;
    EqualityExpressionState;
    EqualityExpressionDelim;
    RelationalExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-EqualityExpression
fn equality_expression<I: U8Input>(i: ESInput<I>,
                                   params: &EnumSet<Parameter>)
                                   -> ESParseResult<I, EqualityExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::In) ||
         params.contains(&Parameter::Yield)) {
        panic!("misuse of equality_expression");
    }

    type Accumulator = Rc<RefCell<EqualityExpressionState>>;

    #[inline]
    fn equality_operator<I: U8Input>(i: ESInput<I>)
                                     -> ESParseResult<I, EqualityExpressionOperator> {
        parse!{i;

            let operator = (i -> string(i, b"===").map(|_| EqualityExpressionOperator::StrictEquality)) <|>
            (i -> string(i, b"==").map(|_| EqualityExpressionOperator::Equality)) <|>
            (i -> string(i, b"!==").map(|_| EqualityExpressionOperator::StrictInequality)) <|>
            (i -> string(i, b"!=").map(|_| EqualityExpressionOperator::Inequality));

            ret operator
        }
    }

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            let equality_operator = on_error(
                equality_operator,
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected one of these operators: ==, ===, !==, or !=.".to_string())
                }
            );
            let delim_2 = common_delim();
            ret {
                let delim = EqualityExpressionDelim(delim_1, equality_operator, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = relational_expression(params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// == 12.12 Binary Bitwise Operators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-binary-bitwise-operators

// BitwiseANDExpression := EqualityExpression BitwiseANDExpressionRest*
// BitwiseANDExpressionRest := Delim ^ Delim EqualityExpression

struct BitwiseANDExpression(EqualityExpression, Vec<BitwiseANDExpressionRest>);

impl BitwiseANDExpression {
    fn new(rhs_val: EqualityExpression) -> Self {
        BitwiseANDExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: BitwiseANDExpressionDelim,
                rhs_val: EqualityExpression)
                -> Self {

        let BitwiseANDExpression(head, rest) = self;
        let mut rest = rest;

        let BitwiseANDExpressionDelim(delim_1, delim_2) = operator_delim;

        let rhs = BitwiseANDExpressionRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        BitwiseANDExpression(head, rest)
    }
}

struct BitwiseANDExpressionRest(Vec<CommonDelim>, Vec<CommonDelim>, EqualityExpression);

struct BitwiseANDExpressionDelim(Vec<CommonDelim>, Vec<CommonDelim>);

generate_list_parser!(
    BitwiseANDExpression;
    BitwiseANDExpressionRest;
    BitwiseANDExpressionState;
    BitwiseANDExpressionDelim;
    EqualityExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BitwiseANDExpression
fn bitwise_and_expression<I: U8Input>(i: ESInput<I>,
                                      params: &EnumSet<Parameter>)
                                      -> ESParseResult<I, BitwiseANDExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::In) ||
         params.contains(&Parameter::Yield)) {
        panic!("misuse of bitwise_and_expression");
    }

    type Accumulator = Rc<RefCell<BitwiseANDExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;
            let delim_1 = common_delim();
            let _or = on_error(
                |i| string(i, b"&"),
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected & operator.".to_string())
                }
            );
            let delim_2 = common_delim();
            ret {

                let delim = BitwiseANDExpressionDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = equality_expression(params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())

}

// BitwiseXORExpression := BitwiseANDExpression BitwiseXORExpressionRest*
// BitwiseXORExpressionRest := Delim ^ Delim BitwiseANDExpression

struct BitwiseXORExpression(BitwiseANDExpression, Vec<BitwiseXORExpressionRest>);

impl BitwiseXORExpression {
    fn new(rhs_val: BitwiseANDExpression) -> Self {
        BitwiseXORExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: BitwiseXORExpressionDelim,
                rhs_val: BitwiseANDExpression)
                -> Self {

        let BitwiseXORExpression(head, rest) = self;
        let mut rest = rest;

        let BitwiseXORExpressionDelim(delim_1, delim_2) = operator_delim;

        let rhs = BitwiseXORExpressionRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        BitwiseXORExpression(head, rest)
    }
}

struct BitwiseXORExpressionRest(Vec<CommonDelim>, Vec<CommonDelim>, BitwiseANDExpression);

struct BitwiseXORExpressionDelim(Vec<CommonDelim>, Vec<CommonDelim>);

generate_list_parser!(
    BitwiseXORExpression;
    BitwiseXORExpressionRest;
    BitwiseXORExpressionState;
    BitwiseXORExpressionDelim;
    BitwiseANDExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BitwiseXORExpression
fn bitwise_xor_expression<I: U8Input>(i: ESInput<I>,
                                      params: &EnumSet<Parameter>)
                                      -> ESParseResult<I, BitwiseXORExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::In) ||
         params.contains(&Parameter::Yield)) {
        panic!("misuse of bitwise_xor_expression");
    }

    type Accumulator = Rc<RefCell<BitwiseXORExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();
            let _or = on_error(
                |i| string(i, b"^"),
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected ^ operator.".to_string())
                }
            );
            let delim_2 = common_delim();

            ret {
                let delim = BitwiseXORExpressionDelim(delim_1, delim_2);
                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = bitwise_and_expression(params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())

}

// BitwiseORExpression := BitwiseXORExpression BitwiseORExpressionRest*
// BitwiseORExpressionRest := Delim | Delim BitwiseXORExpression

struct BitwiseORExpression(BitwiseXORExpression, Vec<BitwiseORExpressionRest>);

impl BitwiseORExpression {
    fn new(rhs_val: BitwiseXORExpression) -> Self {
        BitwiseORExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: BitwiseORExpressionDelim,
                rhs_val: BitwiseXORExpression)
                -> Self {

        let BitwiseORExpression(head, rest) = self;
        let mut rest = rest;

        let BitwiseORExpressionDelim(delim_1, delim_2) = operator_delim;

        let rhs = BitwiseORExpressionRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        BitwiseORExpression(head, rest)
    }
}

struct BitwiseORExpressionRest(Vec<CommonDelim>, Vec<CommonDelim>, BitwiseXORExpression);

struct BitwiseORExpressionDelim(Vec<CommonDelim>, Vec<CommonDelim>);

generate_list_parser!(
    BitwiseORExpression;
    BitwiseORExpressionRest;
    BitwiseORExpressionState;
    BitwiseORExpressionDelim;
    BitwiseXORExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BitwiseORExpression
fn bitwise_or_expression<I: U8Input>(i: ESInput<I>,
                                     params: &EnumSet<Parameter>)
                                     -> ESParseResult<I, BitwiseORExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::In) ||
         params.contains(&Parameter::Yield)) {
        panic!("misuse of bitwise_or_expression");
    }

    type Accumulator = Rc<RefCell<BitwiseORExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;
            let delim_1 = common_delim();
            let _or = on_error(
                |i| string(i, b"|"),
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected | operator.".to_string())
                }
            );
            let delim_2 = common_delim();
            ret {
                let delim = BitwiseORExpressionDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = bitwise_xor_expression(params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// == 12.13 Binary Logical Operators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-binary-logical-operators

// LogicalAndExpression := BitwiseORExpression LogicalAndExpressionRest*
// LogicalAndExpressionRest := Delim && Delim BitwiseORExpression

struct LogicalAndExpression(BitwiseORExpression, Vec<LogicalAndExpressionRest>);

impl LogicalAndExpression {
    fn new(rhs_val: BitwiseORExpression) -> Self {
        LogicalAndExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: LogicalAndExpressionDelim,
                rhs_val: BitwiseORExpression)
                -> Self {

        let LogicalAndExpression(head, rest) = self;
        let mut rest = rest;

        let LogicalAndExpressionDelim(delim_1, delim_2) = operator_delim;

        let rhs = LogicalAndExpressionRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        LogicalAndExpression(head, rest)
    }
}

struct LogicalAndExpressionRest(Vec<CommonDelim>, Vec<CommonDelim>, BitwiseORExpression);

struct LogicalAndExpressionDelim(Vec<CommonDelim>, Vec<CommonDelim>);

generate_list_parser!(
    LogicalAndExpression;
    LogicalAndExpressionRest;
    LogicalAndExpressionState;
    LogicalAndExpressionDelim;
    BitwiseORExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LogicalANDExpression
fn logical_and_expression<I: U8Input>(i: ESInput<I>,
                                      params: &EnumSet<Parameter>)
                                      -> ESParseResult<I, LogicalAndExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::In) ||
         params.contains(&Parameter::Yield)) {
        panic!("misuse of logical_and_expression");
    }

    type Accumulator = Rc<RefCell<LogicalAndExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;
            let delim_1 = common_delim();
            let _or = on_error(
                |i| string(i, b"&&"),
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected && operator.".to_string())
                }
            );
            let delim_2 = common_delim();
            ret {
                let delim = LogicalAndExpressionDelim(delim_1, delim_2);
                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = bitwise_or_expression(params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())

}

// LogicOrExpression := LogicalAndExpression LogicOrExpressionRest*
// LogicOrExpressionRest := Delim || Delim LogicalAndExpression

struct LogicOrExpression(LogicalAndExpression, Vec<LogicOrExpressionRest>);

impl LogicOrExpression {
    fn new(rhs_val: LogicalAndExpression) -> Self {
        LogicOrExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: LogicOrExpressionDelim,
                rhs_val: LogicalAndExpression)
                -> Self {

        let LogicOrExpression(head, rest) = self;
        let mut rest = rest;

        let LogicOrExpressionDelim(delim_1, delim_2) = operator_delim;

        let rhs = LogicOrExpressionRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        LogicOrExpression(head, rest)
    }
}

struct LogicOrExpressionRest(Vec<CommonDelim>, Vec<CommonDelim>, LogicalAndExpression);

struct LogicOrExpressionDelim(Vec<CommonDelim>, Vec<CommonDelim>);

generate_list_parser!(
    LogicOrExpression;
    LogicOrExpressionRest;
    LogicOrExpressionState;
    LogicOrExpressionDelim;
    LogicalAndExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LogicalORExpression
fn logical_or_expression<I: U8Input>(i: ESInput<I>,
                                     params: &EnumSet<Parameter>)
                                     -> ESParseResult<I, LogicOrExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::In) ||
         params.contains(&Parameter::Yield)) {
        panic!("misuse of logical_or_expression");
    }

    type Accumulator = Rc<RefCell<LogicOrExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;
            let delim_1 = common_delim();
            let _or = on_error(
                |i| string(i, b"||"),
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected || operator.".to_string())
                }
            );
            let delim_2 = common_delim();
            ret {

                let delim = LogicOrExpressionDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = logical_and_expression(params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

#[test]
fn logical_or_expression_test() {

    // TODO: fix with actual test case
    let i = InputPosition::new(&b"a||a ||    a"[..], CurrentPosition::new());
    match logical_or_expression(i, &EnumSet::new()).into_inner().1 {
        Ok(result) => {
            assert!(true);
        }
        Err(_) => {
            assert!(true);
        }
    }
}

// == 12.14 Conditional Operator ( ? : ) ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-conditional-operator

enum ConditionalExpression {
    Conditional(LogicOrExpression,
                Vec<CommonDelim>,
                Vec<CommonDelim>,
                AssignmentExpression,
                Vec<CommonDelim>,
                Vec<CommonDelim>,
                AssignmentExpression),
    LogicOrExpression(LogicOrExpression),
}

// TODO: test
fn conditional_expression<I: U8Input>(i: ESInput<I>,
                                      params: &EnumSet<Parameter>)
                                      -> ESParseResult<I, ConditionalExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::In) ||
         params.contains(&Parameter::Yield)) {
        panic!("misuse of conditional_expression");
    }

    #[inline]
    fn conditional<I: U8Input>(i: ESInput<I>,
                               params: &EnumSet<Parameter>)
                               -> ESParseResult<I,
                                                (Vec<CommonDelim>,
                                                 Vec<CommonDelim>,
                                                 AssignmentExpression,
                                                 Vec<CommonDelim>,
                                                 Vec<CommonDelim>,
                                                 AssignmentExpression)> {

        parse!{i;

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

            ret {
                (delim_1, delim_2, consequent, delim_3, delim_4, alternative)
            }
        }
    }

    parse!{i;

        let logical_or_expression = logical_or_expression(&params);

        let conditional = option(|i| conditional(i, &params).map(|x| Some(x)),
            None);

        ret {
            match conditional {
                Some((delim_1, delim_2, consequent, delim_3, delim_4, alternative)) => {
                    ConditionalExpression::Conditional(
                        logical_or_expression, delim_1, delim_2, consequent, delim_3, delim_4, alternative)
                }
                None => {
                    ConditionalExpression::LogicOrExpression(logical_or_expression)
                }
            }
        }
    }
}

// == 12.15 Assignment Operators ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-assignment-operators

enum AssignmentExpression {
    ConditionalExpression(Box<ConditionalExpression>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-AssignmentExpression
fn assignment_expression<I: U8Input>(i: ESInput<I>,
                                     params: &EnumSet<Parameter>)
                                     -> ESParseResult<I, AssignmentExpression> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::In) ||
         params.contains(&Parameter::Yield)) {
        panic!("misuse of assignment_expression");
    }

    parse!{i;

        let result = (i -> conditional_expression(i, params)
            .map(|x| AssignmentExpression::ConditionalExpression(Box::new(x))));

        // TODO: complete

        ret {
            result
        }
    }
}

// == 12.16 Comma Operator ( , ) ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-comma-operator

struct ExpressionList(Vec<ExpressionListItem>);

enum ExpressionListItem {
    Delim(Vec<CommonDelim>,
          /* , (comma) */
          Vec<CommonDelim>),
    AssignmentExpression(AssignmentExpression),
}

// http://www.ecma-international.org/ecma-262/7.0/#prod-Expression
fn expression<I: U8Input>(i: ESInput<I>,
                          params: &EnumSet<Parameter>)
                          -> ESParseResult<I, ExpressionList> {

    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::In)) {
        panic!("misuse of expression");
    }

    type Accumulator = Rc<RefCell<Vec<ExpressionListItem>>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            on_error(
                |i| token(i, b','),
                |i| {
                    let loc = i.position();
                    // TODO: proper err message?
                    ErrorLocation::new(loc, "Expected , here.".to_string())
                }
            );

            let delim_2 = common_delim();

            ret {
                accumulator.borrow_mut().push(ExpressionListItem::Delim(delim_1, delim_2));
                ()
            }
        }
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;

            let item = assignment_expression(&params);

            ret {
                accumulator.borrow_mut().push(ExpressionListItem::AssignmentExpression(item));
                ()
            }
        }
    };

    parse!{i;

        let list = parse_list(
            delimiter,
            reducer
        );

        ret ExpressionList(list)
    }

}

// == 13 ECMAScript Language: Statements and Declarations ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-statements-and-declarations

enum Statement {
    BlockStatement(BlockStatement),
    VariableStatement(VariableStatement),
    EmptyStatement(EmptyStatement),
    ExpressionStatement(ExpressionStatement),
    IfStatement(Box<IfStatement>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Statement
fn statement<I: U8Input>(i: ESInput<I>,
                         params: &EnumSet<Parameter>)
                         -> ESParseResult<I, Statement> {

    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::Return)) {
        panic!("misuse of statement");
    }

    let mut yield_params = params.clone();
    yield_params.remove(&Parameter::Yield);
    let yield_params = yield_params;

    parse!{i;

        let x =
        (i -> block_statement(i, &params).map(|x| Statement::BlockStatement(x)))
        <|>
        (i -> variable_statement(i, &yield_params).map(|x| Statement::VariableStatement(x)))
        <|>
        (i -> empty_statement(i).map(|x| Statement::EmptyStatement(x)))
        <|>
        (i -> expression_statement(i, &params).map(|x| Statement::ExpressionStatement(x)))
        <|>
        (i -> if_statement(i, &params).map(|x| Statement::IfStatement(Box::new(x))));

        // TODO: more statements

        ret x
    }
}

enum Declaration {
    // TODO: complete
    Foo,
}

// TODO: test
// TODO: http://www.ecma-international.org/ecma-262/7.0/#prod-Declaration
fn declaration<I: U8Input>(i: ESInput<I>,
                           params: &EnumSet<Parameter>)
                           -> ESParseResult<I, Declaration> {

    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of declaration");
    }

    parse!{i;



        // TODO: complete

        ret {
            Declaration::Foo
        }
    }
}

// TODO: http://www.ecma-international.org/ecma-262/7.0/#prod-HoistableDeclaration

enum BreakableStatement {
    IterationStatement,
    SwitchStatement,
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BreakableStatement
fn breakable_statement<I: U8Input>(i: ESInput<I>,
                                   params: &EnumSet<Parameter>)
                                   -> ESParseResult<I, BreakableStatement> {

    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::Return)) {
        panic!("misuse of breakable_statement");
    }

    parse!{i;

        // TODO: complete

        ret BreakableStatement::IterationStatement
    }
}

// == 13.2 Block ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-block

struct BlockStatement(Block);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BlockStatement
fn block_statement<I: U8Input>(i: ESInput<I>,
                               params: &EnumSet<Parameter>)
                               -> ESParseResult<I, BlockStatement> {

    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::Return)) {
        panic!("misuse of block_statement");
    }

    block(i, params).map(|x| BlockStatement(x))
}

struct Block(Vec<CommonDelim>, Option<StatementList>, Vec<CommonDelim>);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#sec-block
fn block<I: U8Input>(i: ESInput<I>, params: &EnumSet<Parameter>) -> ESParseResult<I, Block> {

    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::Return)) {
        panic!("misuse of block");
    }

    parse!{i;

        token(b'{');
        let delim_left = common_delim();

        let contents = option(|i| statement_list(i, params).map(|x| Some(x)), None);

        let delim_right = common_delim();
        token(b'}');

        ret Block(delim_left, contents, delim_right)
    }
}

struct StatementList(Vec<StatementListItemWrap>);

enum StatementListItemWrap {
    Delim(Vec<CommonDelim>,
          /* , (comma) */
          Vec<CommonDelim>),
    StatementListItem(StatementListItem),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-StatementList
fn statement_list<I: U8Input>(i: ESInput<I>,
                              params: &EnumSet<Parameter>)
                              -> ESParseResult<I, StatementList> {

    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::Return)) {
        panic!("misuse of statement_list");
    }

    type Accumulator = Rc<RefCell<Vec<StatementListItemWrap>>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            on_error(
                |i| token(i, b','),
                |i| {
                    let loc = i.position();
                    // TODO: proper err message?
                    ErrorLocation::new(loc, "Expected , here.".to_string())
                }
            );

            let delim_2 = common_delim();

            ret {
                accumulator.borrow_mut().push(StatementListItemWrap::Delim(delim_1, delim_2));
                ()
            }
        }
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;

            let item = statement_list_item(&params);

            ret {
                accumulator.borrow_mut().push(StatementListItemWrap::StatementListItem(item));
                ()
            }
        }
    };

    parse!{i;

        let list = parse_list(
            delimiter,
            reducer
        );

        ret StatementList(list)
    }
}

enum StatementListItem {
    Statement(Statement),
    Declaration(Declaration),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-StatementListItem
fn statement_list_item<I: U8Input>(i: ESInput<I>,
                                   params: &EnumSet<Parameter>)
                                   -> ESParseResult<I, StatementListItem> {

    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::Return)) {
        panic!("misuse of statement_list_item");
    }

    let mut yield_params = params.clone();
    yield_params.remove(&Parameter::Yield);
    let yield_params = yield_params;

    parse!{i;

        let item = (i -> statement(i, &params).map(|x| StatementListItem::Statement(x))) <|>
        (i -> declaration(i, &yield_params).map(|x| StatementListItem::Declaration(x)));

        ret item
    }
}


// == 13.3 Declarations and the Variable Statement ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-declarations-and-the-variable-statement

// == 13.3.1 Let and Const Declarations ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-let-and-const-declarations

enum LexicalDeclaration {
    Let(Vec<CommonDelim>, BindingList, Vec<CommonDelim>),
    Const(Vec<CommonDelim>, BindingList, Vec<CommonDelim>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LexicalDeclaration
fn lexical_declaration<I: U8Input>(i: ESInput<I>,
                                   params: &EnumSet<Parameter>)
                                   -> ESParseResult<I, LexicalDeclaration> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::In)) {
        panic!("misuse of lexical_declaration");
    }

    let_or_const(i).bind(|i, result| {
        parse!{i;
            let delim_1 = common_delim_required();
            let list = binding_list(&params);
            let delim_2 = common_delim();
            semicolon();
            ret {
                match result {
                    LetOrConst::Let => {
                        LexicalDeclaration::Let(delim_1, list, delim_2)
                    },
                    LetOrConst::Const => {
                        LexicalDeclaration::Const(delim_1, list, delim_2)
                    }
                }
            }
        }
    })

}

enum LetOrConst {
    Let,
    Const,
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LetOrConst
fn let_or_const<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, LetOrConst> {

    on_error(i,
             |i| -> ESParseResult<I, LetOrConst> {
                 or(i,
                    |i| string(i, b"let").then(|i| i.ret(LetOrConst::Let)),
                    |i| string(i, b"const").then(|i| i.ret(LetOrConst::Const)))
             },
             |i| {
                 let reason = "Expected either 'let' or 'const'.".to_string();
                 ErrorLocation::new(i.position(), reason)
             })
}

struct BindingList(Vec<BindingListItem>);

enum BindingListItem {
    Delim(Vec<CommonDelim>,
          /* , (comma) */
          Vec<CommonDelim>),
    LexicalBinding(LexicalBinding),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BindingList
fn binding_list<I: U8Input>(i: ESInput<I>,
                            params: &EnumSet<Parameter>)
                            -> ESParseResult<I, BindingList> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::In)) {
        panic!("misuse of binding_list");
    }

    type Accumulator = Rc<RefCell<Vec<BindingListItem>>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            on_error(
                |i| token(i, b','),
                |i| {
                    let loc = i.position();
                    // TODO: proper err message?
                    ErrorLocation::new(loc, "Expected , here.".to_string())
                }
            );

            let delim_2 = common_delim();

            ret {
                accumulator.borrow_mut().push(BindingListItem::Delim(delim_1, delim_2));
                ()
            }
        }
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;

            let item = lexical_binding(&params);

            ret {
                accumulator.borrow_mut().push(BindingListItem::LexicalBinding(item));
                ()
            }
        }
    };

    parse!{i;

        let list = parse_list(
            delimiter,
            reducer
        );

        ret BindingList(list)
    }
}

enum LexicalBinding {
    BindingIdentifier(BindingIdentifier, Vec<CommonDelim>, Option<Initializer>),
    BindingPattern(BindingPattern, Vec<CommonDelim>, Initializer),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LexicalBinding
fn lexical_binding<I: U8Input>(i: ESInput<I>,
                               params: &EnumSet<Parameter>)
                               -> ESParseResult<I, LexicalBinding> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::In)) {
        panic!("misuse of lexical_binding");
    }

    let mut binding_params = params.clone();
    binding_params.remove(&Parameter::In);
    let binding_params = binding_params;

    either(i,
           |i| binding_identifier(i, &binding_params), // left
           |i| binding_pattern(i, &binding_params) /* right */)
        .bind(|i, result| {
            match result {
                Either::Left(binding_identifier) => {
                    parse!{i;

                    // TODO: tie this to be optional with initializer (below)?
                    let delim = common_delim();

                    let init = option(|i| initializer(i, &params).map(|x| Some(x)), None);
                    ret LexicalBinding::BindingIdentifier(binding_identifier, delim, init)
                }
                }
                Either::Right(binding_pattern) => {
                    parse!{i;
                    let delim = common_delim();
                    let init = initializer(&params);
                    ret LexicalBinding::BindingPattern(binding_pattern, delim, init)
                }
                }
            }
        })
}

// == 13.3.2 Variable Statement ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-variable-statement

struct VariableStatement(/* var */
                         Vec<CommonDelim>,
                         VariableDeclarationList,
                         Vec<CommonDelim>);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-VariableStatement
fn variable_statement<I: U8Input>(i: ESInput<I>,
                                  params: &EnumSet<Parameter>)
                                  -> ESParseResult<I, VariableStatement> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of variable_statement");
    }

    let mut params = params.clone();
    params.insert(Parameter::In);
    let params = params;

    parse!{i;

        on_error(
            |i| string(i, b"var"),
            |i| {
                let loc = i.position();
                ErrorLocation::new(loc, "Expected 'var' keyword.".to_string())
            }
        );

        let delim_1 = common_delim_required();
        let list = variable_declaration_list(&params);
        let delim_2 = common_delim();

        // TODO: ASI rule
        semicolon();

        ret VariableStatement(delim_1, list, delim_2)
    }
}

struct VariableDeclarationList(Vec<VariableDeclarationListItem>);

enum VariableDeclarationListItem {
    Delim(Vec<CommonDelim>,
          /* , (comma) */
          Vec<CommonDelim>),
    VariableDeclaration(VariableDeclaration),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-VariableDeclarationList
fn variable_declaration_list<I: U8Input>(i: ESInput<I>,
                                         params: &EnumSet<Parameter>)
                                         -> ESParseResult<I, VariableDeclarationList> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::In)) {
        panic!("misuse of variable_declaration_list");
    }

    type Accumulator = Rc<RefCell<Vec<VariableDeclarationListItem>>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            on_error(
                |i| token(i, b','),
                |i| {
                    let loc = i.position();
                    // TODO: proper err message?
                    ErrorLocation::new(loc, "Expected , here.".to_string())
                }
            );

            let delim_2 = common_delim();

            ret {
                accumulator.borrow_mut().push(VariableDeclarationListItem::Delim(delim_1, delim_2));
                ()
            }
        }
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;

            let item = variable_declaration(&params);

            ret {
                accumulator.borrow_mut().push(VariableDeclarationListItem::VariableDeclaration(item));
                ()
            }
        }
    };

    parse!{i;

        let list = parse_list(
            delimiter,
            reducer
        );

        ret VariableDeclarationList(list)
    }
}

enum VariableDeclaration {
    BindingIdentifier(BindingIdentifier, Vec<CommonDelim>, Option<Initializer>),
    BindingPattern(BindingPattern, Vec<CommonDelim>, Initializer),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-VariableDeclaration
fn variable_declaration<I: U8Input>(i: ESInput<I>,
                                    params: &EnumSet<Parameter>)
                                    -> ESParseResult<I, VariableDeclaration> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::In)) {
        panic!("misuse of variable_declaration");
    }

    let mut binding_params = params.clone();
    binding_params.remove(&Parameter::In);
    let binding_params = binding_params;

    either(i,
           |i| binding_identifier(i, &binding_params), // left
           |i| binding_pattern(i, &binding_params) /* right */)
        .bind(|i, result| {
            match result {
                Either::Left(binding_identifier) => {
                    parse!{i;

                    // TODO: tie this to be optional with initializer (below)?
                    let delim = common_delim();

                    let init = option(|i| initializer(i, &params).map(|x| Some(x)), None);
                    ret VariableDeclaration::BindingIdentifier(binding_identifier, delim, init)
                }
                }
                Either::Right(binding_pattern) => {
                    parse!{i;
                    let delim = common_delim();
                    let init = initializer(&params);
                    ret VariableDeclaration::BindingPattern(binding_pattern, delim, init)
                }
                }
            }
        })
}

// == 13.3.3 Destructuring Binding Patterns ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-destructuring-binding-patterns

enum BindingPattern {
    ObjectBindingPattern(ObjectBindingPattern),
    ArrayBindingPattern(Box<ArrayBindingPattern>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BindingPattern
fn binding_pattern<I: U8Input>(i: ESInput<I>,
                               params: &EnumSet<Parameter>)
                               -> ESParseResult<I, BindingPattern> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of binding_pattern");
    }

    or(i,
       |i| object_binding_pattern(i, &params).map(|x| BindingPattern::ObjectBindingPattern(x)),
       |i| {
           array_binding_pattern(i, &params)
               .map(|x| BindingPattern::ArrayBindingPattern(Box::new(x)))
       })
}

enum ObjectBindingPattern {
    Empty(Vec<CommonDelim>, Vec<CommonDelim>),
    BindingPropertyList(BindingPropertyList),
    BindingPropertyListTrailingComma(BindingPropertyList,
                                     /* , (comma) */
                                     Vec<CommonDelim>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ObjectBindingPattern
fn object_binding_pattern<I: U8Input>(i: ESInput<I>,
                                      params: &EnumSet<Parameter>)
                                      -> ESParseResult<I, ObjectBindingPattern> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of object_binding_pattern");
    }

    #[inline]
    fn contents<I: U8Input>(i: ESInput<I>,
                            params: &EnumSet<Parameter>)
                            -> ESParseResult<I, ObjectBindingPattern> {
        parse!{i;

            let list = binding_property_list(params);

            let trailing_comma = option(|i| -> ESParseResult<I, _> {
                parse!{i;
                    let delim = common_delim();
                    token(b',');
                    ret Some(delim)
                }
            }, None);

            ret {
                match trailing_comma {
                    None => ObjectBindingPattern::BindingPropertyList(list),
                    Some(delims) => ObjectBindingPattern::BindingPropertyListTrailingComma(list, delims)
                }
            }
        }
    }

    parse!{i;

        token(b'{');
        let left_delim = common_delim();

        let contents = option(|i| contents(i, &params).map(|x| Some(x)),
            None);

        let right_delim = common_delim();
        token(b'}');

        ret {
            if contents.is_none() {
                ObjectBindingPattern::Empty(left_delim, right_delim)
            } else {
                contents.unwrap()
            }
        }
    }
}

struct ArrayBindingPattern(/* [ (left bracket) */
                           Vec<CommonDelim>,
                           ArrayBindingPatternContents,
                           Vec<CommonDelim> /* ] (right bracket) */);

enum ArrayBindingPatternContents {
    Rest(Option<Elision>, Vec<CommonDelim>, Option<BindingRestElement>),
    List(BindingElementList),
    ListWithRest(BindingElementList,
                 Vec<CommonDelim>, /* , (comma) */
                 Vec<CommonDelim>,
                 Option<Elision>,
                 Vec<CommonDelim>,
                 Option<BindingRestElement>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ArrayBindingPattern
fn array_binding_pattern<I: U8Input>(i: ESInput<I>,
                                     params: &EnumSet<Parameter>)
                                     -> ESParseResult<I, ArrayBindingPattern> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of array_binding_pattern");
    }

    #[inline]
    fn array_binding_pattern_rest<I: U8Input>
        (i: ESInput<I>,
         params: &EnumSet<Parameter>)
         -> ESParseResult<I, (Option<Elision>, Vec<CommonDelim>, Option<BindingRestElement>)> {
        parse!{i;

            let elision = option(|i| elision(i).map(|x| Some(x)),
                None);
            let delim = common_delim();

            let rest = option(|i| binding_rest_element(i, &params).map(|x| Some(x)),
                None);

            ret (elision, delim, rest)
        }
    }

    #[inline]
    fn array_binding_pattern_contents<I: U8Input>
        (i: ESInput<I>,
         params: &EnumSet<Parameter>)
         -> ESParseResult<I, ArrayBindingPatternContents> {
        parse!{i;

            // [BindingElementList_[?Yield]]
            // [BindingElementList_[?Yield] , Elision_opt BindingRestElement_[?Yield]_opt]

            let list = binding_element_list(&params);

            let maybe_end = option(|i| -> ESParseResult<I, _> {
                parse!{i;

                    let delim_1 = common_delim();

                    on_error(
                        |i| token(i, b','),
                        |i| {
                            let loc = i.position();
                            // TODO: proper err message?
                            ErrorLocation::new(loc, "Expected , delimeter here.".to_string())
                        }
                    );

                    let delim_2 = common_delim();

                    let (elision, delim_3, rest) = array_binding_pattern_rest(&params);

                    ret Some((delim_1, delim_2, elision, delim_3, rest))
                }
            }, None);

            ret {
                match maybe_end {
                    None => ArrayBindingPatternContents::List(list),
                    Some((delim_1, delim_2, elision, delim_3, rest)) =>
                        ArrayBindingPatternContents::ListWithRest(list, delim_1, delim_2, elision, delim_3, rest),
                }
            }
        }
    }

    parse!{i;

        token(b'[');
        let delim_left = common_delim();

        let contents = array_binding_pattern_contents(&params)
            <|>
            (i -> array_binding_pattern_rest(i, &params).map(|(elision, delim, rest)| {
                ArrayBindingPatternContents::Rest(elision, delim, rest)
            }));

        let delim_right = common_delim();
        token(b']');

        ret ArrayBindingPattern(delim_left, contents, delim_right)
    }
}

struct BindingPropertyList(Vec<BindingPropertyListItem>);

enum BindingPropertyListItem {
    Delim(Vec<CommonDelim>,
          /* , (comma) */
          Vec<CommonDelim>),
    BindingProperty(BindingProperty),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BindingPropertyList
fn binding_property_list<I: U8Input>(i: ESInput<I>,
                                     params: &EnumSet<Parameter>)
                                     -> ESParseResult<I, BindingPropertyList> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of binding_property_list");
    }

    type Accumulator = Rc<RefCell<Vec<BindingPropertyListItem>>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            on_error(
                |i| token(i, b','),
                |i| {
                    let loc = i.position();
                    // TODO: proper err message?
                    ErrorLocation::new(loc, "Expected , here.".to_string())
                }
            );

            let delim_2 = common_delim();

            ret {
                accumulator.borrow_mut().push(BindingPropertyListItem::Delim(delim_1, delim_2));
                ()
            }
        }
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;

            let item = binding_property(&params);

            ret {
                accumulator.borrow_mut().push(BindingPropertyListItem::BindingProperty(item));
                ()
            }
        }
    };

    parse!{i;

        let list = parse_list(
            delimiter,
            reducer
        );

        ret BindingPropertyList(list)
    }
}

struct BindingElementList(Vec<BindingElementListItem>);

enum BindingElementListItem {
    Delim(Vec<CommonDelim>,
          /* , (comma) */
          Vec<CommonDelim>),
    BindingElisionElement(BindingElisionElement),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BindingElementList
fn binding_element_list<I: U8Input>(i: ESInput<I>,
                                    params: &EnumSet<Parameter>)
                                    -> ESParseResult<I, BindingElementList> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of binding_elision_list");
    }

    type Accumulator = Rc<RefCell<Vec<BindingElementListItem>>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            on_error(
                |i| token(i, b','),
                |i| {
                    let loc = i.position();
                    // TODO: proper err message?
                    ErrorLocation::new(loc, "Expected , here.".to_string())
                }
            );

            let delim_2 = common_delim();

            ret {
                accumulator.borrow_mut().push(BindingElementListItem::Delim(delim_1, delim_2));
                ()
            }
        }
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;

            let item = binding_elision_element(&params);

            ret {
                accumulator.borrow_mut().push(BindingElementListItem::BindingElisionElement(item));
                ()
            }
        }
    };

    parse!{i;

        let list = parse_list(
            delimiter,
            reducer
        );

        ret BindingElementList(list)
    }
}

struct BindingElisionElement(Option<Elision>, Vec<CommonDelim>, BindingElement);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BindingElisionElement
fn binding_elision_element<I: U8Input>(i: ESInput<I>,
                                       params: &EnumSet<Parameter>)
                                       -> ESParseResult<I, BindingElisionElement> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of binding_elision_element");
    }

    parse!{i;

        let e = option(|i| elision(i).map(|x| Some(x)),
            None);

        let delim = common_delim();

        let bind_elem = binding_element(&params);

        ret BindingElisionElement(e, delim, bind_elem)
    }
}

enum BindingProperty {
    SingleNameBinding(SingleNameBinding),
    PropertyName(PropertyName,
                 Vec<CommonDelim>,
                 /* : (colon) */
                 Vec<CommonDelim>,
                 BindingElement),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BindingProperty
fn binding_property<I: U8Input>(i: ESInput<I>,
                                params: &EnumSet<Parameter>)
                                -> ESParseResult<I, BindingProperty> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of binding_property");
    }

    #[inline]
    fn binding_property_property_name<I: U8Input>(i: ESInput<I>,
                                                  params: &EnumSet<Parameter>)
                                                  -> ESParseResult<I, BindingProperty> {

        let mut init_params = params.clone();
        init_params.insert(Parameter::In);

        parse!{i;
            let prop_name = property_name(&params);

            let delim_1 = common_delim();
            token(b':');
            let delim_2 = common_delim();

            let bind_elem = binding_element(&params);

            ret BindingProperty::PropertyName(prop_name, delim_1, delim_2, bind_elem)
        }
    }

    parse!{i;

        let binding =
            (i -> single_name_binding(i, &params).map(|x| BindingProperty::SingleNameBinding(x)))
            <|>
            binding_property_property_name(&params);

        ret binding
    }
}

enum BindingElement {
    SingleNameBinding(SingleNameBinding),
    BindingPattern(BindingPattern, Vec<CommonDelim>, Option<Initializer>),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BindingElement
fn binding_element<I: U8Input>(i: ESInput<I>,
                               params: &EnumSet<Parameter>)
                               -> ESParseResult<I, BindingElement> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of binding_element");
    }

    #[inline]
    fn binding_element_binding_pattern<I: U8Input>(i: ESInput<I>,
                                                   params: &EnumSet<Parameter>)
                                                   -> ESParseResult<I, BindingElement> {

        let mut init_params = params.clone();
        init_params.insert(Parameter::In);

        parse!{i;
            let bind_pat = binding_pattern(&params);

            let delim = common_delim();

            let init = option(|i| initializer(i, &init_params).map(|x| Some(x)),
                None);

            ret BindingElement::BindingPattern(bind_pat, delim, init)
        }
    }

    parse!{i;

        let binding =
            (i -> single_name_binding(i, &params).map(|x| BindingElement::SingleNameBinding(x)))
            <|>
            binding_element_binding_pattern(&params);

        ret binding
    }
}

struct SingleNameBinding(BindingIdentifier, Vec<CommonDelim>, Option<Initializer>);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-SingleNameBinding
fn single_name_binding<I: U8Input>(i: ESInput<I>,
                                   params: &EnumSet<Parameter>)
                                   -> ESParseResult<I, SingleNameBinding> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of single_name_binding");
    }

    let mut init_params = params.clone();
    init_params.insert(Parameter::In);

    parse!{i;

        let ident = binding_identifier(&params);

        let delim = common_delim();

        let init = option(|i| initializer(i, &init_params).map(|x| Some(x)),
            None);

        ret SingleNameBinding(ident, delim, init)
    }
}

enum BindingRestElement {
    BindingIdentifier(Vec<CommonDelim>, BindingIdentifier),
    BindingPattern(Vec<CommonDelim>, BindingPattern),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-BindingRestElement
fn binding_rest_element<I: U8Input>(i: ESInput<I>,
                                    params: &EnumSet<Parameter>)
                                    -> ESParseResult<I, BindingRestElement> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of binding_rest_element");
    }

    enum BindingRestElementContent {
        BindingIdentifier(BindingIdentifier),
        BindingPattern(BindingPattern),
    }

    parse!{i;

        on_error(
            |i| string(i, b"..."),
            |i| {
                let loc = i.position();
                // TODO: proper err message?
                ErrorLocation::new(loc, "Expected ... here.".to_string())
            }
        );

        let delim = common_delim();

        let contents = (i -> binding_identifier(i, &params).map(|x| BindingRestElementContent::BindingIdentifier(x)))
            <|>
            (i -> binding_pattern(i, &params).map(|x| BindingRestElementContent::BindingPattern(x)));

        ret {
            match contents {
                BindingRestElementContent::BindingIdentifier(x) => BindingRestElement::BindingIdentifier(delim, x),
                BindingRestElementContent::BindingPattern(x) => BindingRestElement::BindingPattern(delim, x)
            }
        }
    }
}

// == 13.4 Empty Statement ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-empty-statement

struct EmptyStatement;

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-EmptyStatement
fn empty_statement<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, EmptyStatement> {
    semicolon(i).map(|_| EmptyStatement)
}

// == 13.5 Expression Statement ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-expression-statement

struct ExpressionStatement(ExpressionList, Vec<CommonDelim>);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ExpressionStatement
fn expression_statement<I: U8Input>(i: ESInput<I>,
                                    params: &EnumSet<Parameter>)
                                    -> ESParseResult<I, ExpressionStatement> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of expression_statement");
    }

    #[inline]
    fn look_ahead_guard<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ()> {

        either(i,
               |i| {
            look_ahead(i, |i| -> ESParseResult<I, ()> {
                parse!{i;

                    let _ = (i -> token(i, b'{').map(|_| ())) <|>
                    (i -> string(i, b"function").map(|_| ())) <|>
                    (i -> string(i, b"class").map(|_| ())) <|>
                    (i -> string(i, b"let").map(|_| ())) <|>
                    (i -> token(i, b'[').map(|_| ()));

                    ret {()}
                }
            })
        },
               |i| i.ret(()))
            .bind(|i, result| {
                match result {
                    // TODO: improve error message to indicate token that should not be produced
                    Either::Left(_) => i.err("".into()),
                    Either::Right(_) => i.ret(()),
                }
            })
    }

    let mut in_params = params.clone();
    in_params.insert(Parameter::In);
    let in_params = in_params;

    parse!{i;

        look_ahead_guard();

        let expr = expression(&in_params);
        let delim = common_delim();

        // TODO: semicolon insertion rule
        semicolon();

        ret {
            ExpressionStatement(expr, delim)
        }
    }
}

// == 13.6 The `if` Statement ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-if-statement

enum IfStatement {
    OneBranch(/* if */
              Vec<CommonDelim>,
              /* ( */
              Vec<CommonDelim>,
              ExpressionList,
              Vec<CommonDelim>,
              /* ) */
              Vec<CommonDelim>,
              Statement),
    TwoBranch(/* if */
              Vec<CommonDelim>,
              /* ( */
              Vec<CommonDelim>,
              ExpressionList,
              Vec<CommonDelim>,
              /* ) */
              Vec<CommonDelim>,
              Statement,
              Vec<CommonDelim>,
              /* else */
              Vec<CommonDelim>,
              Statement),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-IfStatement
fn if_statement<I: U8Input>(i: ESInput<I>,
                            params: &EnumSet<Parameter>)
                            -> ESParseResult<I, IfStatement> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::Return)) {
        panic!("misuse of if_statement");
    }

    #[inline]
    fn optional_else<I: U8Input>
        (i: ESInput<I>,
         params: &EnumSet<Parameter>)
         -> ESParseResult<I, (Vec<CommonDelim>, Vec<CommonDelim>, Statement)> {

        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield) ||
             params.contains(&Parameter::Return)) {
            panic!("misuse of optional_else");
        }

        parse!{i;

            let delim_1 = common_delim();
            string(b"else");
            let delim_2 = common_delim();

            let stmt = statement(&params);

            ret {
                (delim_1, delim_2, stmt)
            }
        }
    }

    let mut test_condition_params = EnumSet::new();
    test_condition_params.insert(Parameter::In);

    if params.contains(&Parameter::Yield) {
        test_condition_params.insert(Parameter::Yield);
    }
    let test_condition_params = test_condition_params;

    parse!{i;

        string(b"if");

        let delim_1 = common_delim();
        token(b'(');
        let delim_2 = common_delim();

        let expr = expression(&test_condition_params);

        let delim_3 = common_delim();
        token(b')');
        let delim_4 = common_delim();

        let stmt = statement(&params);

        let else_branch = option(
            |i| optional_else(i, &params).map(|x| Some(x)),
            None);

        ret {
            match else_branch {
                Some((delim_5, delim_6, else_branch)) => {
                    IfStatement::TwoBranch(delim_1, delim_2, expr, delim_3, delim_4, stmt, delim_5, delim_6, else_branch)
                },
                None => {
                    IfStatement::OneBranch(delim_1, delim_2, expr, delim_3, delim_4, stmt)
                }
            }
        }
    }
}

// == 13.7 Iteration Statements ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-iteration-statements

enum IterationStatement {
    DoWhile,
    While, // TODO: other iteration variants
}

// TODO: test
// TODO: http://www.ecma-international.org/ecma-262/7.0/#prod-IterationStatement

struct ForDeclaration(LetOrConst, Vec<CommonDelim>, ForBinding);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ForDeclaration
fn for_declaration<I: U8Input>(i: ESInput<I>,
                               params: &EnumSet<Parameter>)
                               -> ESParseResult<I, ForDeclaration> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of for_declaration");
    }

    parse!{i;

        let let_or_const = let_or_const();

        let delim = common_delim();

        let binding = for_binding(&params);

        ret ForDeclaration(let_or_const, delim, binding)

    }

}

enum ForBinding {
    BindingIdentifier(BindingIdentifier),
    BindingPattern(BindingPattern),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ForBinding
fn for_binding<I: U8Input>(i: ESInput<I>,
                           params: &EnumSet<Parameter>)
                           -> ESParseResult<I, ForBinding> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of for_binding");
    }

    or(i,
       |i| binding_identifier(i, &params).map(|x| ForBinding::BindingIdentifier(x)),
       |i| binding_pattern(i, &params).map(|x| ForBinding::BindingPattern(x)))
}

// == 13.8 The continue Statement ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-continue-statement

// TODO: complete

// == 13.9 The break Statement ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-break-statement

// TODO: complete

// == 13.10 The return Statement ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-return-statement

// TODO: complete

// == 14 ECMAScript Language: Functions and Classes ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-functions-and-classes

// == 14.1 Function Definitions ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-function-definitions

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
// http://www.ecma-international.org/ecma-262/7.0/#prod-FunctionDeclaration
fn function_declaration<I: U8Input>(i: ESInput<I>,
                                    params: &EnumSet<Parameter>)
                                    -> ESParseResult<I, FunctionDeclaration> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::Default)) {
        panic!("misuse of function_declaration");
    }

    #[inline]
    fn function_name<I: U8Input>
        (i: ESInput<I>,
         params: &EnumSet<Parameter>)
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

enum FunctionExpression {
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
// http://www.ecma-international.org/ecma-262/7.0/#prod-FunctionExpression
fn function_expression<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, FunctionExpression> {

    // this is intentionally empty
    let params = EnumSet::new();
    assert!(params.len() <= 0);

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

struct StrictFormalParameters(FormalParameterList);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-StrictFormalParameters
fn strict_formal_parameters<I: U8Input>(i: ESInput<I>,
                                        params: &EnumSet<Parameter>)
                                        -> ESParseResult<I, StrictFormalParameters> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of strict_formal_parameters");
    }

    formal_parameter_list(i, params).map(|x| StrictFormalParameters(x))

}

enum FormalParameters {
    Empty,
    FormalParameterList(FormalParameterList),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-FormalParameters
fn formal_parameters<I: U8Input>(i: ESInput<I>,
                                 params: &EnumSet<Parameter>)
                                 -> ESParseResult<I, FormalParameters> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of formal_parameters");
    }

    option(i,
           |i| {
        parse!{i;

        let list = formal_parameter_list(params);

        ret {
            FormalParameters::FormalParameterList(list)
        }

    }
    },
           FormalParameters::Empty)
}

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
// http://www.ecma-international.org/ecma-262/7.0/#prod-FormalParameterList
fn formal_parameter_list<I: U8Input>(i: ESInput<I>,
                                     params: &EnumSet<Parameter>)
                                     -> ESParseResult<I, FormalParameterList> {
    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of formal_parameter_list");
    }

    or(i,
       |i| {
        parse!{i;
            let rest = function_rest_parameter(&params);

            ret {
                FormalParameterList::FunctionRestParameter(rest)
            }
        }
    },
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

struct FormalsList(Vec<FormalsListItem>);

enum FormalsListItem {
    Delim(Vec<CommonDelim>,
          /* , (comma) */
          Vec<CommonDelim>),
    FormalParameter(FormalParameter),
}

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-FormalsList
fn formals_list<I: U8Input>(i: ESInput<I>,
                            params: &EnumSet<Parameter>)
                            -> ESParseResult<I, FormalsList> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of formals_list");
    }

    type Accumulator = Rc<RefCell<Vec<FormalsListItem>>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            on_error(
                |i| token(i, b','),
                |i| {
                    let loc = i.position();
                    // TODO: proper err message?
                    ErrorLocation::new(loc, "Expected , delimeter.".to_string())
                }
            );

            let delim_2 = common_delim();

            ret {
                accumulator.borrow_mut().push(FormalsListItem::Delim(delim_1, delim_2));
                ()
            }
        }
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;

            let l = option(|i| elision(i).map(|x| Some(x)), None);

            let item = formal_parameter(&params);

            ret {
                accumulator.borrow_mut().push(FormalsListItem::FormalParameter(item));
                ()
            }
        }
    };

    parse!{i;

        let list = parse_list(
            delimiter,
            reducer
        );

        ret {

            // TODO: dev mode
            assert!(list.len() > 0);

            FormalsList(list)
        }
    }
}

type FunctionRestParameter = BindingRestElement;

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-FunctionRestParameter
fn function_rest_parameter<I: U8Input>(i: ESInput<I>,
                                       params: &EnumSet<Parameter>)
                                       -> ESParseResult<I, FunctionRestParameter> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of function_rest_parameter");
    }

    binding_rest_element(i, params)
}

type FormalParameter = BindingElement;

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-FormalParameter
fn formal_parameter<I: U8Input>(i: ESInput<I>,
                                params: &EnumSet<Parameter>)
                                -> ESParseResult<I, FormalParameter> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of formal_parameter");
    }

    binding_element(i, params)
}

struct FunctionBody(FunctionStatementList);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-FunctionBody
fn function_body<I: U8Input>(i: ESInput<I>,
                             params: &EnumSet<Parameter>)
                             -> ESParseResult<I, FunctionBody> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of function_body");
    }

    function_statement_list(i, params).map(|x| FunctionBody(x))
}

struct FunctionStatementList(Option<StatementList>);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-FunctionStatementList
fn function_statement_list<I: U8Input>(i: ESInput<I>,
                                       params: &EnumSet<Parameter>)
                                       -> ESParseResult<I, FunctionStatementList> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of function_statement_list");
    }

    let mut params = params.clone();
    params.insert(Parameter::Return);

    parse!{i;

        let maybe_list = option(|i| statement_list(i, &params).map(|x| Some(x)), None);

        ret FunctionStatementList(maybe_list)
    }
}

// == 14.2 Arrow Function Definitions ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-arrow-function-definitions

// TODO: complete

// == 14.3 Method Definitions ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-method-definitions

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

struct PropertySetParameterList(FormalParameter);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-MethodDefinition
fn method_definition<I: U8Input>(i: ESInput<I>,
                                 params: &EnumSet<Parameter>)
                                 -> ESParseResult<I, MethodDefinition> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of method_definition");
    }

    #[inline]
    fn method_definition<I: U8Input>(i: ESInput<I>,
                                     params: &EnumSet<Parameter>)
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
                                         params: &EnumSet<Parameter>)
                                         -> ESParseResult<I, MethodDefinition> {
        parse!{i;

            on_error(
                |i| string(i, b"get"),
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected 'get' keyword.".to_string())
                }
            );

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
                                         params: &EnumSet<Parameter>)
                                         -> ESParseResult<I, MethodDefinition> {
        parse!{i;

            on_error(
                |i| string(i, b"set"),
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected 'set' keyword.".to_string())
                }
            );

            let delim_1 = common_delim_required();
            let prop_name = property_name(&params);
            let delim_2 = common_delim();

            token(b'(');
            let delim_3 = common_delim();

            let list = property_set_parameter_list(&params);

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

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-PropertySetParameterList
fn property_set_parameter_list<I: U8Input>(i: ESInput<I>,
                                           params: &EnumSet<Parameter>)
                                           -> ESParseResult<I, PropertySetParameterList> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of property_set_parameter_list");
    }

    formal_parameter(i, params).map(|x| PropertySetParameterList(x))
}

// == 14.4 Generator Function Definitions ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-generator-function-definitions

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
// http://www.ecma-international.org/ecma-262/7.0/#prod-GeneratorMethod
fn generator_method<I: U8Input>(i: ESInput<I>,
                                params: &EnumSet<Parameter>)
                                -> ESParseResult<I, GeneratorMethod> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of generator_method");
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

struct GeneratorBody(FunctionBody);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-GeneratorBody
fn generator_body<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, GeneratorBody> {


    let mut params = EnumSet::new();
    params.insert(Parameter::Yield);

    function_body(i, &params).map(|x| GeneratorBody(x))
}

// TODO: YieldExpression

// == 14.5 Class Definitions ==
//
// http://www.ecma-international.org/ecma-262/7.0/#sec-class-definitions


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
//                 ErrorLocation::new(loc, "Expected var keyword.".to_string())
//             }
//         );

//         // let _var = (i -> {
//         //     string(i, b"var")
//         //         .map_err2(|_, i| {
//         //             let loc = i.position();
//         //             ErrorLocation::new(loc, "Expected var here.")
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
//                 ErrorLocation::new(loc, "Expected var here.".to_string())
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
