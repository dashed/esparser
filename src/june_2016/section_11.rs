// 11 ECMAScript Language: Lexical Grammar
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-lexical-grammar

// 3rd-party imports

use chomp::types::{U8Input, Input};

// local imports

use parsers::{ESParseResult, ESInput, string, parse_utf8_char, on_error, many, string_till};
use parsers::error_location::ErrorLocation;

#[derive(Debug)]
pub enum CommonDelim {
    WhiteSpace(WhiteSpace),
    LineTerminator(LineTerminator),
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

        return parse!{i;
            let delim =
                (i -> whitespace(i).map(CommonDelim::WhiteSpace)) <|>
                (i -> comment(i).map(|c| CommonDelim::Comment(c)));
            ret delim
        };

    }

    parse!{i;
        let delim =
            (i -> whitespace(i).map(CommonDelim::WhiteSpace)) <|>
            (i -> line_terminator(i).map(CommonDelim::LineTerminator)) <|>
            (i -> comment(i).map(|c| CommonDelim::Comment(c)));
        ret delim
    }
}

#[inline]
pub fn common_delim<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Vec<CommonDelim>> {
    many(i, |i| __common_delim(i, true))
}

// 11.2 White Space

#[derive(Debug)]
enum WhiteSpace {
    CharacterTabulation,
    LineTabulation,
    FormFeed,
    Space,
    NoBreakSpace,
    ZeroWidthNoBreakSpace,
    // TODO: bound for char to be whitespace?
    OtherWhiteSpace(char),
}

fn whitespace<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, WhiteSpace> {

    #[inline]
    fn other_whitespace<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, WhiteSpace> {
        parse_utf8_char(i).bind(|i, c: char| {
            if c.is_whitespace() {
                i.ret(WhiteSpace::OtherWhiteSpace(c))
            } else {
                let loc = i.position();
                let reason = "Expected whitespace.".to_string();
                i.err(ErrorLocation::new(loc, reason).into())
            }
        })
    }

    let parse_result = parse!{i;

        let whitespace_char =
            (i -> string(i, b"\x0009").map(|_| WhiteSpace::CharacterTabulation)) <|> // <TAB>; CHARACTER TABULATION
            (i -> string(i, b"\x000B").map(|_| WhiteSpace::LineTabulation)) <|> // <VT>; LINE TABULATION
            (i -> string(i, b"\x000C").map(|_| WhiteSpace::FormFeed)) <|> // <FF>; FORM FEED (FF)
            (i -> string(i, b"\x0020").map(|_| WhiteSpace::Space)) <|> // <SP>; SPACE
            (i -> string(i, b"\x00A0").map(|_| WhiteSpace::NoBreakSpace)) <|> // <NBSP>; NO-BREAK SPACE
            (i -> string(i, b"\xFEFF").map(|_| WhiteSpace::ZeroWidthNoBreakSpace)) <|> // <ZWNBSP>; ZERO WIDTH NO-BREAK SPACE
            other_whitespace(); // Any other Unicode "Separator, space" code point

        ret whitespace_char
    };

    parse_result

    // TODO: fix
    // on_error(parse_result,
    //          |i| ErrorLocation::new(i.position(), "Expected whitespace.".to_string()))

}

// 11.3 Line Terminators

#[derive(Debug)]
enum LineTerminator {
    LineFeed,
    CarriageReturn,
    LineSeparator,
    ParagraphSeparator,
}

// TODO: test
fn line_terminator<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, LineTerminator> {

    let parse_result = parse!{i;

        let result =
            (i -> string(i, b"\x000A").map(|_| LineTerminator::LineFeed)) <|>   // <LF>; LINE FEED (LF)
            (i -> string(i, b"\x000D").map(|_| LineTerminator::CarriageReturn)) <|> // <CR>; CARRIAGE RETURN (CR)
            (i -> string(i, b"\x2028").map(|_| LineTerminator::LineSeparator))  <|> // <LS>; LINE SEPARATOR
            (i -> string(i, b"\x2029").map(|_| LineTerminator::ParagraphSeparator)); // <PS>; PARAGRAPH SEPARATOR

        ret result
    };

    // TODO: fix
    parse_result
    // on_error(parse_result, |i| {
    //     let loc = i.position();
    //     let reason = "Expected utf8 character.".to_string();
    //     ErrorLocation::new(loc, reason)
    // })
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
            string(i, END).map(|_| ())
            // on_error(string(i, END).map(|_| ()), |i| {
            //     let loc = i.position();
            //     ErrorLocation::new(loc, "Expected */.".to_string())
            // })
        }

        // TODO: verify production rule satisfaction
        // http://www.ecma-international.org/ecma-262/7.0/#prod-MultiLineCommentChars

        parse!{i;

            (i -> {
                on_error(
                    string(i, b"/*"),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected /* for multi-line comment.".to_string())
                    }
                )
            });

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

            (i -> {
                on_error(
                    string(i, b"//"),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected // for single-line comment.".to_string())
                    }
                )
            });

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
