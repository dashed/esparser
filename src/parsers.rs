// rust imports

use std::rc::Rc;
use std::cell::RefCell;

// 3rd-party imports

use chomp::parsers::Error as ChompError;
use chomp::types::numbering::{InputPosition, LineNumber, Numbering};
use chomp::types::{Buffer, Input, ParseResult, U8Input};
use chomp::primitives::{Primitives, IntoInner};
use chomp::prelude::Either;

// macros

/// Override the or-combinator used by parse! macro in chomp
// TODO: document reason why?
macro_rules! __parse_internal_or {
    ($input:expr, $lhs:expr, $rhs:expr) => {
        $crate::parsers::or($input, $lhs, $rhs)
    };
}

// type aliases

// TODO: docs
type U8Error = ChompError<u8>;

pub type ESInput<I> = InputPosition<I, CurrentPosition>;
pub type ESParseResult<I, T> = ParseResult<ESInput<I>, T, ESParseError>;

// error types

enum ESParseError {
    // Parser shall backtrack.
    Failure(ErrorChain),

    // No backtracking is done.
    Error(ESError),
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

enum ESError {
    SyntaxError(SyntaxError),
}

// TODO: inner is 'Reason' string.
struct SyntaxError(String);

// ErrorChain

#[derive(Debug)]
struct ErrorChain {
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

// current position

#[derive(Clone)]
struct CurrentLine(u64);

#[derive(Clone)]
struct CurrentCol(u64);

// TODO: reference with link to chomp github where this came from
#[derive(Clone)]
pub struct CurrentPosition {
    line: CurrentLine,
    col: CurrentCol,
}

impl CurrentPosition {
    pub fn new() -> Self {
        CurrentPosition {
            line: CurrentLine(0),
            col: CurrentCol(0),
        }
    }

    pub fn line(&self) -> u64 {
        // zero-indexed to one-indexed
        (self.line.0) + 1
    }

    pub fn col(&self) -> u64 {
        // zero-indexed to one-indexed
        (self.col.0) + 1
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
                self.line.0 += 1; // line num
                self.col.0 = 0;  // col num
            } else {
                self.col.0 += 1; // col num
            }
        });
    }

    fn add(&mut self, t: Self::Token) {
        // TODO: refactor from fn source_character
        if t == b'\n' {
            self.line.0 += 1; // line num
            self.col.0 = 0;  // col num
        } else {
            self.col.0 += 1; // col num
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
