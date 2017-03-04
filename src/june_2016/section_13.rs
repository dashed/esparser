// rust imports

use std::rc::Rc;
use std::cell::RefCell;

// 3rd-party imports

use chomp::types::{U8Input, Input};

// local imports

use super::types::{Parameters, Parameter};
use super::section_11::{common_delim, CommonDelim};
use parsers::{ESInput, ESParseResult, parse_list, token, option};

// 13 ECMAScript Language: Statements and Declarations
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-statements-and-declarations

enum Statement {
    BlockStatement(BlockStatement), /*     VariableStatement(VariableStatement),
                                     *     EmptyStatement(EmptyStatement),
                                     *     ExpressionStatement(ExpressionStatement),
                                     *     IfStatement(Box<IfStatement>),
                                     *     BreakableStatement(BreakableStatement), // TODO: more stuff */
}

// TODO: test
fn statement<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, Statement> {

    if !(params.is_empty() || params.contains(&Parameter::Yield) ||
         params.contains(&Parameter::Return)) {
        panic!("misuse of statement");
    }

    let mut yield_params = params.clone();
    yield_params.remove(&Parameter::Yield);
    let yield_params = yield_params;

    parse!{i;

        let x =
        (i -> block_statement(i, &params).map(Statement::BlockStatement));
    //     <|>
    //     (i -> variable_statement(i, &yield_params).map(Statement::VariableStatement))
    //     <|>
    //     (i -> empty_statement(i).map(Statement::EmptyStatement))
    //     <|>
    //     (i -> expression_statement(i, &params).map(Statement::ExpressionStatement))
    //     <|>
    //     (i -> if_statement(i, &params).map(|x| Statement::IfStatement(Box::new(x))))
    //     <|>
    //     (i -> breakable_statement(i, &params).map(Statement::BreakableStatement));

    //     // TODO: more statements

        ret x
    }
}

// 13.2 Block

// BlockStatement

struct BlockStatement(Block);

// TODO: test
fn block_statement<I: U8Input>(i: ESInput<I>,
                               params: &Parameters)
                               -> ESParseResult<I, BlockStatement> {

    if is_debug_mode!() {
        if !(params.is_empty() || params.contains(&Parameter::Yield) ||
             params.contains(&Parameter::Return)) {
            panic!("misuse of block_statement");
        }
    }

    block(i, params).map(BlockStatement)
}

// Block

struct Block(/* { */
             Vec<CommonDelim>,
             Option<Box<StatementList>>,
             Vec<CommonDelim> /* } */);

// TODO: test
fn block<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, Block> {

    if is_debug_mode!() {
        if !(params.is_empty() || params.contains(&Parameter::Yield) ||
             params.contains(&Parameter::Return)) {
            panic!("misuse of block");
        }
    }

    parse!{i;

        token(b'{');
        let delim_left = common_delim();

        let contents = option(|i| statement_list(i, params).map(|x| Some(Box::new(x))), None);

        let delim_right = common_delim();
        token(b'}');

        ret Block(delim_left, contents, delim_right)
    }
}

// StatementList

pub struct StatementList(StatementListItem, Vec<StatementListItem>);

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
pub fn statement_list<I: U8Input>(i: ESInput<I>,
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

    #[inline]
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
enum StatementListItem {
    Statement(Statement), //     Declaration(Declaration),
}

// TODO: test
fn statement_list_item<I: U8Input>(i: ESInput<I>,
                                   params: &Parameters)
                                   -> ESParseResult<I, StatementListItem> {

    if is_debug_mode!() {
        if !(params.is_empty() || params.contains(&Parameter::Yield) ||
             params.contains(&Parameter::Return)) {
            panic!("misuse of statement_list_item");
        }
    }

    let mut yield_params = params.clone();
    yield_params.remove(&Parameter::Yield);
    let yield_params = yield_params;

    parse!{i;

        let item = (i -> statement(i, &params).map(StatementListItem::Statement)) <|>
        (i -> statement(i, &params).map(StatementListItem::Statement));
        // (i -> declaration(i, &yield_params).map(|x| StatementListItem::Declaration(x)));

        ret item
    }
}

#[test]
fn foo() {

    use chomp::types::numbering::InputPosition;
    use parsers::current_position::CurrentPosition;
    use chomp::primitives::IntoInner;

    let i = InputPosition::new("var".as_bytes(), CurrentPosition::new());
    let params = Parameters::new();

    // match statement_list_item(i, &params).into_inner().1 {
    //     Ok(_) => {
    //         assert!(false);
    //     }
    //     Err(_) => {
    //         assert!(false);
    //     }
    // }
}
