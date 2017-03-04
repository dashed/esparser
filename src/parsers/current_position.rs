// 3rd-party imports

use chomp::types::numbering::Numbering;
use chomp::types::Buffer;

// structs

#[derive(Clone, Debug)]
struct CurrentLine(u64);

#[derive(Clone, Debug)]
struct CurrentCol(u64);

// TODO: reference with link to chomp github where this came from
#[derive(Clone, Debug)]
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
