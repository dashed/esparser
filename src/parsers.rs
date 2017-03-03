
// 3rd-party imports

use chomp::combinators::{or};
use chomp::parsers::Error as ChompError;
use chomp::types::numbering::{InputPosition, LineNumber, Numbering};
use chomp::types::{Buffer, Input, ParseResult, U8Input};

// macros

/// Override the or-combinator used by parse! macro in chomp
// TODO: document reason why?
macro_rules! __parse_internal_or {
    ($input:expr, $lhs:expr, $rhs:expr) => {
        println!("rofl");
        or($input, $lhs, $rhs)
    };
}

// type aliases

// TODO: docs
type U8Error = ChompError<u8>;

type ESInput<I> = InputPosition<I, CurrentPosition>;
type ESParseResult<I, T> = ParseResult<ESInput<I>, T, ESParseError>;

// error types

// Mimic the Failure and Error semantics as detailed here:
// http://www.scala-lang.org/files/archive/api/current/scala-parser-combinators/scala/util/parsing/combinator/Parsers.html
enum ESParseError {

    // Parser shall backtrack.
    Failure(ErrorChain),

    // No backtracking is done.
    Error(ESError)
}

enum ESError {
    SyntaxError(SyntaxError)
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
    col: CurrentCol
}

impl CurrentPosition {

    pub fn new() -> Self {
        CurrentPosition {
            line: CurrentLine(0),
            col: CurrentCol(0)
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
