// macros

/// Override the or-combinator used by parse! macro in chomp
// TODO: document reason why?
macro_rules! __parse_internal_or {
    ($input:expr, $lhs:expr, $rhs:expr) => {
        $crate::parsers::or($input, $lhs, $rhs)
    };
}

// rust imports

use std::rc::Rc;
use std::cell::RefCell;
use std::iter::FromIterator;

// 3rd-party imports

use chomp;
use chomp::parsers::Error as ChompError;
use chomp::types::numbering::{InputPosition, LineNumber, Numbering};
use chomp::types::{Buffer, Input, ParseResult, U8Input};
use chomp::primitives::{Primitives, IntoInner};
use chomp::prelude::Either;

// local imports

pub mod current_position;
pub mod error_location;

use parsers::current_position::CurrentPosition;

// type aliases

// TODO: docs
type U8Error = ChompError<u8>;

pub type ESInput<I> = InputPosition<I, CurrentPosition>;
pub type ESParseResult<I, T> = ParseResult<ESInput<I>, T, ESParseError>;

// error types

#[derive(Debug)]
pub enum ESParseError {
    // Parse failure.
    // Backtracking allowed.
    Failure(ErrorChain),

    // No backtracking is done.
    Error(ESError),
}

impl ::std::error::Error for ESParseError {
    fn description(&self) -> &str {
        match *self {
            ESParseError::Failure(ref err) => err.description(),
            ESParseError::Error(ref err) => err.description(),
        }
    }

    fn cause(&self) -> Option<&::std::error::Error> {
        match *self {
            ESParseError::Failure(ref err) => err.cause(),
            ESParseError::Error(ref err) => err.cause(),
        }
    }
}

impl ::std::fmt::Display for ESParseError {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> Result<(), ::std::fmt::Error> {
        match *self {
            ESParseError::Failure(ref err) => err.fmt(f),
            ESParseError::Error(ref err) => err.fmt(f),
        }
    }
}

impl ::std::convert::From<ErrorChain> for ESParseError {
    fn from(err: ErrorChain) -> Self {
        ESParseError::Failure(err)
    }
}

impl ::std::convert::From<error_location::ErrorLocation> for ESParseError {
    fn from(err: error_location::ErrorLocation) -> Self {
        let error_chain = ErrorChain::new(err);
        ESParseError::Failure(error_chain)
    }
}

impl IntoParseError for ESParseError {
    #[inline]
    fn into_parse_error(&self) -> ParseError {
        match *self {
            ESParseError::Failure(_) => ParseError::Failure,
            ESParseError::Error(_) => ParseError::Error,
        }
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

error_chain_for!(U8Error);

#[derive(Debug)]
enum ESError {
    SyntaxError(SyntaxError),
}

impl ::std::error::Error for ESError {
    fn description(&self) -> &str {
        match *self {
            ESError::SyntaxError(ref syntax_error) => syntax_error.description(),
        }
    }

    fn cause(&self) -> Option<&::std::error::Error> {
        match *self {
            ESError::SyntaxError(ref syntax_error) => syntax_error.cause(),
        }
    }
}

impl ::std::fmt::Display for ESError {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> Result<(), ::std::fmt::Error> {
        match *self {
            ESError::SyntaxError(ref syntax_error) => syntax_error.fmt(f),
        }
    }
}

// TODO: inner is 'Reason' string.
#[derive(Debug)]
pub struct SyntaxError(String);

impl ::std::error::Error for SyntaxError {
    fn description(&self) -> &str {
        &self.0
    }
}

impl ::std::fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> Result<(), ::std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

// ErrorChain

#[derive(Debug)]
pub struct ErrorChain {
    current: Box<::std::error::Error>,
    next: Option<Box<ErrorChain>>,
}

impl ErrorChain {
    fn new<T>(err_to_wrap: T) -> Self
        where ErrorChain: ::std::convert::From<T>
    {

        let error_to_chain = ErrorChain::from(err_to_wrap);

        ErrorChain {
            current: error_to_chain.current,
            next: None,
        }
    }

    fn chain_err<T>(self, error_to_chain: T) -> Self
        where ErrorChain: ::std::convert::From<T>
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

impl ::std::convert::From<error_location::ErrorLocation> for ErrorChain {
    fn from(err: error_location::ErrorLocation) -> Self {
        ErrorChain {
            current: Box::new(err),
            next: None,
        }
    }
}

// ErrorChainIter

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

                use std::mem;

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

                use std::mem;

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
pub fn parse_list<I: U8Input, D, Delim, A, R, Reduced, E: IntoParseError>(input: I,
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
fn parse_list_rest<I: U8Input, D, Delim, A, R, Reduced, E: IntoParseError>
    (input: I,
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

// chomp overrides

// Mimic the Failure and Error semantics as detailed here:
// http://www.scala-lang.org/files/archive/api/current/scala-parser-combinators/scala/util/parsing/combinator/Parsers.html
pub enum ParseError {
    // Parser shall backtrack.
    Failure,

    // No backtracking is done.
    Error,
}

pub trait IntoParseError {
    #[inline]
    fn into_parse_error(&self) -> ParseError;
}

#[inline]
pub fn string<I: U8Input>(i: ESInput<I>, str_match: &[u8]) -> ESParseResult<I, I::Buffer> {
    chomp::parsers::string(i, str_match).map_err(|err| {
        let error_chain = ErrorChain::new(err);
        ESParseError::Failure(error_chain)
    })
}

#[inline]
pub fn token<I: U8Input>(i: ESInput<I>, tok: I::Token) -> ESParseResult<I, I::Token> {
    chomp::parsers::token(i, tok).map_err(|err| {
        let error_chain = ErrorChain::new(err);
        ESParseError::Failure(error_chain)
    })
}

#[inline]
pub fn option<I: Input, T, E: IntoParseError, F>(i: I, f: F, default: T) -> ParseResult<I, T, E>
    where F: FnOnce(I) -> ParseResult<I, T, E>
{
    let m = i.mark();

    match f(i).into_inner() {
        (b, Ok(d)) => b.ret(d),
        (b, Err(err)) => {
            match err.into_parse_error() {
                ParseError::Failure => b.restore(m).ret(default),
                ParseError::Error => b.err(err),
            }
        }
    }
}

#[inline]
pub fn either<I, T, U, E, F, G>(i: I, f: F, g: G) -> ParseResult<I, Either<T, U>, E>
    where I: Input,
          F: FnOnce(I) -> ParseResult<I, T, E>,
          G: FnOnce(I) -> ParseResult<I, U, E>,
          E: IntoParseError
{
    let m = i.mark();

    match f(i).into_inner() {
        (b, Ok(d)) => b.ret(Either::Left(d)),
        (b, Err(err)) => {
            match err.into_parse_error() {
                ParseError::Failure => g(b.restore(m)).map(Either::Right),
                ParseError::Error => b.err(err),
            }
        }
    }
}

#[inline]
pub fn or<I: Input, T, E, F, G>(i: I, f: F, g: G) -> ParseResult<I, T, E>
    where F: FnOnce(I) -> ParseResult<I, T, E>,
          G: FnOnce(I) -> ParseResult<I, T, E>,
          E: IntoParseError
{
    let m = i.mark();

    match f(i).into_inner() {
        (b, Ok(d)) => b.ret(d),
        (b, Err(err)) => {
            match err.into_parse_error() {
                ParseError::Failure => g(b.restore(m)),
                ParseError::Error => b.err(err),
            }
        }
    }
}

#[inline]
pub fn many<I: Input, T, E, F, U>(i: I, f: F) -> ParseResult<I, T, E>
    where F: FnMut(I) -> ParseResult<I, U, E>,
          T: FromIterator<U>
{
    chomp::combinators::many(i, f)
}

#[inline]
pub fn look_ahead<I: Input, T, E, F>(i: I, f: F) -> ParseResult<I, T, E>
    where F: FnOnce(I) -> ParseResult<I, T, E>
{

    chomp::combinators::look_ahead(i, f)
}

#[inline]
pub fn many_till<I: Input, T, E, R, F, U, N, V>(i: I, p: R, end: F) -> ParseResult<I, T, E>
    where T: FromIterator<U>,
          E: From<N>,
          R: FnMut(I) -> ParseResult<I, U, E>,
          F: FnMut(I) -> ParseResult<I, V, N>
{

    chomp::combinators::many_till(i, p, end)
}

// TODO: test
#[inline]
pub fn string_till<I: U8Input, F>(input: ESInput<I>, mut stop_at: F) -> ESParseResult<I, String>
    where F: Fn(ESInput<I>) -> ESParseResult<I, ()>
{
    many_till(input, parse_utf8_char, |i| look_ahead(i, &mut stop_at))
        .bind(|i, line: Vec<char>| i.ret(line.into_iter().collect()))
}

// like ParseResult::map_err, but this higher-order helper passes &Input to
// error replace function.
#[inline]
pub fn on_error<I: Input, T, E: ::std::error::Error, G>(parse_result: ParseResult<I,
                                                                                  T,
                                                                                  ESParseError>,
                                                        replace_err: G)
                                                        -> ParseResult<I, T, ESParseError>
    where G: FnOnce(&I) -> E,
          ErrorChain: ::std::convert::From<E>
{

    match parse_result.into_inner() {
        (i, Ok(t)) => i.ret(t),
        (i, Err(err)) => {

            match err {
                ESParseError::Failure(error_chain) => {

                    let err_val = replace_err(&i);

                    let next_error_chain = ErrorChain::new::<ErrorChain>(error_chain);
                    let next_error_chain = next_error_chain.chain_err::<E>(err_val);

                    i.err(ESParseError::Failure(next_error_chain))

                }
                ESParseError::Error(err) => i.err(ESParseError::Error(err)),
            }

            // TODO: remove
            // match e.into_parse_error() {
            //     ESParseError::Failure(error_chain) => {
            //         let err_val = transform_err(&i);
            //         let foo = ErrorChain::new(error_chain);
            //         let wrapped_err_chain = foo.chain_err(err_val);
            //         i.err(ESParseError::Failure(wrapped_err_chain))
            //     },
            //     ESParseError::Error(err) => {
            //         i.err(ESParseError::Error(err))
            //     }
            // }
            // let wrapped_err = ErrorChain::new(e).chain_err(err_val);

        }
    }
}

pub fn parse_utf8_char<I: U8Input>(mut i: ESInput<I>) -> ESParseResult<I, char> {

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

                // TODO:
                // unreachable!();

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

        match ::std::str::from_utf8(&internal_buf) {
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
            let fail_reason = error_location::ErrorLocation::new(loc, reason);
            return i.err(ESParseError::Failure(fail_reason.into()));

        }
        Some(c) => {
            return i.ret(c);
        }
    }

}

#[test]
fn parse_utf8_char_test() {

    use self::current_position::CurrentPosition;

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

// fn on_error<I: Input, T, E: ::std::error::Error + 'static, F, V: ::std::error::Error + 'static, G>
//     (i: I,
//      f: F,
//      g: G)
//      -> ParseResult<I, T, ErrorChain>
//     where F: FnOnce(I) -> ParseResult<I, T, E>,
//           G: FnOnce(&I) -> V,
//           ErrorChain: std::convert::From<E>,
//           ErrorChain: std::convert::From<V>
// {

//     match f(i).into_inner() {
//         (i, Ok(t)) => i.ret(t),
//         (i, Err(e)) => {
//             let err_val = g(&i);

//             let foo = ErrorChain::new(e);
//             let wrapped_err = foo.chain_err(err_val);

//             // let wrapped_err = ErrorChain::new(e).chain_err(err_val);
//             i.err(wrapped_err)
//         }
//     }
// }


// ------ sandbox ------


// trait __ParseResult {
//     type Input: Input;
//     type Type;
//     type Error;

//     // fn bind<F, U, V>(self, f: F) -> Bind<Self::Input, U, V>
//     //     where F: FnOnce(Self::Input, Self::Type) -> B,
//     //     B: IntoParseResult
// }

// pub type ESInput<I> = InputPosition<I, CurrentPosition>;
// pub type ESParseResult<I, T> = ParseResult<ESInput<I>, T, ESParseError>;

// trait IntoParseResult {
//     type Input: Input;
//     type Item;
//     type Error;

//     // fn into_parse_result(self) -> ParseResult<Self::Input, Self::Item, Self::Error>;
// }

// ref: https://www.reddit.com/r/rust/comments/5r6tib/parser_combinators_without_macros_my_take/
// pub trait Peg<I> {

//     // type Input: Input;
//     // type Item;
//     // type Error;
//     // type ParseResult: IntoParseResult<Input = Self::Input, Item = Self::Item, Error = Self::Error>;

//     // fn parse(&self, input: Self::Input) -> Self::ParseResult;
//     fn parse(input: I) -> bool;
// }
// use std::marker::PhantomData;


// struct Foo;

// // impl<I: U8Input> Peg for Foo<I> {

// //     type Input = ESInput<I>;
// //     // type Item = bool;
// //     // type Error = ESParseError;

// //     // type ParseResult: IntoParseResult<Input = Self::Input, Item = Self, Error = Self::Error>;

// //     // fn parse(input: Self::Input) -> Self::ParseResult {

// //     // }

// //     fn parse(input: Input) -> bool {

// //     }
// // }


// impl<I: U8Input> Peg<ESInput<I>> for Foo {

//     // type Input = ESInput<I>;
//     // type Item = bool;
//     // type Error = ESParseError;

//     // type ParseResult: IntoParseResult<Input = Self::Input, Item = Self, Error = Self::Error>;
// //
//     // fn parse(input: Self::Input) -> Self::ParseResult {

//     // }

//     fn parse(input: ESInput<I>) -> bool {
//         true
//     }
// }
