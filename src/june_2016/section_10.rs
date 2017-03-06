// 3rd-party imports

use chomp::types::U8Input;

// local imports

use parsers::{parse_utf8_char, ESParseResult, ESInput};

// 10 ECMAScript Language: Source Code
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-source-code

// 10.1 Source Text

// SourceCharacter

pub struct SourceCharacter(pub char);

pub fn source_character<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, SourceCharacter> {
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
    use parsers::parse_utf8_char_test;

    parse_utf8_char_test();
}
