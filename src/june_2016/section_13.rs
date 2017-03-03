// 13 ECMAScript Language: Statements and Declarations
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-statements-and-declarations

// rust imports

use std::rc::Rc;
use std::cell::RefCell;

// 3rd-party imports

use chomp::types::{U8Input, Input};

// local imports

use super::types::{Parameters, Parameter};
use parsers::{ESInput, ESParseResult, parse_list};

// 13.2 Block

// StatementList

struct StatementList(StatementListItem, Vec<StatementListItem>);

impl StatementList {
    fn new(rhs_val: StatementListItem) -> Self {
        StatementList(rhs_val, vec![])
    }

    fn add_item(self, operator_delim: StatementListDelim, rhs_val: StatementListItem) -> Self {

        let StatementList(head, rest) = self;
        let mut rest = rest;

        rest.push(rhs_val);

        StatementList(head, rest)
    }
}

struct StatementListDelim;

generate_list_parser!(
    StatementList;
    StatementListItem; /* rest */
    StatementListState;
    StatementListDelim;
    StatementListItem);

// TODO: test
fn statement_list<I: U8Input>(i: ESInput<I>,
                              params: &Parameters)
                              -> ESParseResult<I, StatementList> {


    if is_debug_mode!() {
        if !(params.is_empty() || params.contains(&Parameter::Yield) ||
             params.contains(&Parameter::Return)) {
            panic!("misuse of statement_list");
        }
    }

    type Accumulator = Rc<RefCell<StatementListState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        accumulator.borrow_mut().add_delim(StatementListDelim);
        i.ret(())
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        statement_list_item(i, &params).bind(|i, rhs| {
            accumulator.borrow_mut().add_item(rhs);
            i.ret(())
        })
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// StatementListItem

// TODO: fix
struct StatementListItem;
// enum StatementListItem {
//     Statement(Statement),
//     Declaration(Declaration),
// }

// TODO: test
fn statement_list_item<I: U8Input>(i: ESInput<I>,
                                   params: &Parameters)
                                   -> ESParseResult<I, StatementListItem> {

    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::Return)) {
        panic!("misuse of statement_list_item");
    }

    i.ret(StatementListItem)

    // let mut yield_params = params.clone();
    // yield_params.remove(&Parameter::Yield);
    // let yield_params = yield_params;

    // parse!{i;

    //     let item = (i -> statement(i, &params).map(|x| StatementListItem::Statement(x))) <|>
    //     (i -> declaration(i, &yield_params).map(|x| StatementListItem::Declaration(x)));

    //     ret item
    // }
}
