// 11 ECMAScript Language: Lexical Grammar
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-lexical-grammar

// 3rd-party imports

use chomp::types::U8Input;

// local imports

use parsers::{ESParseResult, ESInput, ErrorLocation, on_error, string, parse_utf8_char, many,
              string_till};

#[derive(Debug)]
pub enum CommonDelim {
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

    let parse_result = parse!{i;

        let whitespace_char =
            (i -> string(i, b"\x0009").map(|_| '\u{0009}')) <|> // <TAB>; CHARACTER TABULATION
            string(b"\x000B") <|> // <VT>; LINE TABULATION
            string(b"\x000C") <|> // <FF>; FORM FEED (FF)
            string(b"\x0020") <|> // <SP>; SPACE
            string(b"\x00A0") <|> // <NBSP>; NO-BREAK SPACE
            string(b"\xFEFF") <|> // <ZWNBSP>; ZERO WIDTH NO-BREAK SPACE
            other_whitespace(); // Any other Unicode "Separator, space" code point

        ret WhiteSpace(whitespace_char)
    };

    on_error(parse_result,
             |i| ErrorLocation::new(i.position(), "Expected whitespace.".to_string()))

}

// 11.3 Line Terminators

struct LineTerminator(char);

// TODO: test
fn line_terminator<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, LineTerminator> {

    let parse_result = parse!{i;

        let line_terminator_char =
            string(b"\x000A") <|> // <LF>; LINE FEED (LF)
            string(b"\x000D") <|> // <CR>; CARRIAGE RETURN (CR)
            string(b"\x2028") <|> // <LS>; LINE SEPARATOR
            string(b"\x2029");    // <PS>; PARAGRAPH SEPARATOR

        ret LineTerminator(line_terminator_char)
    };

    on_error(parse_result, |i| {
        let loc = i.position();
        let reason = "Expected utf8 character.".to_string();
        ErrorLocation::new(loc, reason)
    })
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
