// 11 ECMAScript Language: Lexical Grammar
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-lexical-grammar

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

    }
}

#[inline]
pub fn common_delim<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Vec<CommonDelim>> {
    many(i, |i| __common_delim(i, true))
}

// 11.2 White Space

struct WhiteSpace(char);

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
                (i -> string(i, b"\x0009").map(|_| '\u{0009}')) <|> // <TAB>; CHARACTER TABULATION
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
