// rust imports

use std::rc::Rc;
use std::cell::RefCell;

// 3rd-party imports

use chomp::types::{U8Input, Input};
use chomp::prelude::Either;

// local imports

use super::types::{Parameters, Parameter};
use super::section_11::{common_delim, common_delim_required, CommonDelim, SemiColon, semicolon};
use super::section_12::{initializer, Initializer, binding_identifier, BindingIdentifier};
use parsers::{ESInput, ESParseResult, parse_list, token, option, string, on_error, either};
use parsers::error_location::ErrorLocation;

// 13 ECMAScript Language: Statements and Declarations
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-statements-and-declarations

// Statement

enum Statement {
    BlockStatement(BlockStatement), /* TODO: fix
                                     *     VariableStatement(VariableStatement),
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

        // TODO: fix
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

// Declaration

struct Declaration;

// TODO: test
fn declaration<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, Declaration> {

    if is_debug_mode!() {
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of declaration");
        }
    }

    parse!{i;

        // TODO: complete

        ret {
            Declaration
        }
    }
}

// TODO: HoistableDeclaration

// TODO: http://www.ecma-international.org/ecma-262/7.0/#prod-BreakableStatement

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
        // validation
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
    Statement(Statement),
    Declaration(Declaration),
}

// TODO: test
fn statement_list_item<I: U8Input>(i: ESInput<I>,
                                   params: &Parameters)
                                   -> ESParseResult<I, StatementListItem> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield) ||
             params.contains(&Parameter::Return)) {
            panic!("misuse of statement_list_item");
        }
    }

    let mut yield_params = params.clone();
    yield_params.remove(&Parameter::Return);
    let yield_params = yield_params;

    parse!{i;

        let item = (i -> statement(i, &params).map(StatementListItem::Statement)) <|>
        (i -> declaration(i, &yield_params).map(StatementListItem::Declaration));

        ret item
    }
}


// 13.3.2 Variable Statement

struct VariableStatement(/* var */
                         Vec<CommonDelim>,
                         VariableDeclarationList,
                         SemiColon);

// TODO: test
fn variable_statement<I: U8Input>(i: ESInput<I>,
                                  params: &Parameters)
                                  -> ESParseResult<I, VariableStatement> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of variable_statement");
        }
    }

    let mut params = params.clone();
    params.insert(Parameter::In);
    let params = params;

    parse!{i;

        (i -> {

            on_error(
                string(i, b"var"),
                |i| {
                    let loc = i.position();
                    ErrorLocation::new(loc, "Expected 'var' keyword.".to_string())
                }
            )
        });

        let delim_1 = common_delim_required();
        let list = variable_declaration_list(&params);
        let semi_colon = semicolon();

        ret VariableStatement(delim_1, list, semi_colon)
    }
}

// VariableDeclarationList

struct VariableDeclarationList(VariableDeclaration, Vec<VariableDeclarationListRest>);

impl VariableDeclarationList {
    fn new(rhs_val: VariableDeclaration) -> Self {
        VariableDeclarationList(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: VariableDeclarationListDelim,
                rhs_val: VariableDeclaration)
                -> Self {

        let VariableDeclarationList(head, rest) = self;
        let mut rest = rest;

        let VariableDeclarationListDelim(delim_1, delim_2) = operator_delim;

        let rhs = VariableDeclarationListRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        VariableDeclarationList(head, rest)
    }
}

struct VariableDeclarationListRest(Vec<CommonDelim>,
                                   /* , (comma) */
                                   Vec<CommonDelim>,
                                   VariableDeclaration);

struct VariableDeclarationListDelim(Vec<CommonDelim>,
                                    /* , (comma) */
                                    Vec<CommonDelim>);

generate_list_parser!(
    VariableDeclarationList;
    VariableDeclarationListRest;
    VariableDeclarationListState;
    VariableDeclarationListDelim;
    VariableDeclaration);

// TODO: test
fn variable_declaration_list<I: U8Input>(i: ESInput<I>,
                                         params: &Parameters)
                                         -> ESParseResult<I, VariableDeclarationList> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield) ||
             params.contains(&Parameter::In)) {
            panic!("misuse of variable_declaration_list");
        }
    }

    type Accumulator = Rc<RefCell<VariableDeclarationListState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            (i -> {
                on_error(
                    token(i, b','),
                    |i| {
                        let loc = i.position();
                        // TODO: proper err message?
                        ErrorLocation::new(loc, "Expected , here.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();

            ret {
                let delim = VariableDeclarationListDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        variable_declaration(i, &params).bind(|i, rhs| {
            accumulator.borrow_mut().add_item(rhs);
            i.ret(())
        })
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

enum VariableDeclaration {
    BindingIdentifier(BindingIdentifier, Option<(Vec<CommonDelim>, Initializer)>),
    BindingPattern(BindingPattern, Vec<CommonDelim>, Initializer),
}

// TODO: test
fn variable_declaration<I: U8Input>(i: ESInput<I>,
                                    params: &Parameters)
                                    -> ESParseResult<I, VariableDeclaration> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield) ||
             params.contains(&Parameter::In)) {
            panic!("misuse of variable_declaration");
        }
    }

    let binding_params = {
        let mut binding_params = params.clone();
        binding_params.remove(&Parameter::In);
        binding_params
    };

    either(i,
           |i| binding_identifier(i, &binding_params), // left
           |i| binding_pattern(i, &binding_params) /* right */)
        .bind(|i, result| {
            match result {
                Either::Left(binding_identifier) => {
                    option(i,
                           |i| {
                        parse!{i;
                            let delim = common_delim();
                            let init = initializer(&params);

                            ret Some((delim, init))
                        }
                    },
                           None)
                        .map(|delim_and_init| {
                            VariableDeclaration::BindingIdentifier(binding_identifier,
                                                                   delim_and_init)
                        })
                }
                Either::Right(binding_pattern) => {
                    parse!{i;
                    let delim = common_delim();
                    let init = initializer(&params);
                    ret VariableDeclaration::BindingPattern(binding_pattern, delim, init)
                }
                }
            }
        })
}

// 13.3.3 Destructuring Binding Patterns

struct BindingPattern;

// TODO: test
fn binding_pattern<I: U8Input>(i: ESInput<I>,
                               params: &Parameters)
                               -> ESParseResult<I, BindingPattern> {

    // TODO: complete
    i.ret(BindingPattern)
}

// BindingProperty

enum BindingProperty {
    SingleNameBinding(SingleNameBinding),
    PropertyName(PropertyName,
                 Vec<CommonDelim>,
                 /* : (colon) */
                 Vec<CommonDelim>,
                 BindingElement),
}

// TODO: test
fn binding_property<I: U8Input>(i: ESInput<I>,
                                params: &Parameters)
                                -> ESParseResult<I, BindingProperty> {

                                    if is_debug_mode!() {
    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of binding_property");
    }
}

    #[inline]
    fn binding_property_property_name<I: U8Input>(i: ESInput<I>,
                                                  params: &Parameters)
                                                  -> ESParseResult<I, BindingProperty> {


        parse!{i;
            let prop_name = property_name(&params);

            let delim_1 = common_delim();
            token(b':');
            let delim_2 = common_delim();

            let bind_elem = binding_element(&params);

            ret BindingProperty::PropertyName(prop_name, delim_1, delim_2, bind_elem)
        }
    }

    parse!{i;

        let binding =
            (i -> single_name_binding(i, &params).map(|x| BindingProperty::SingleNameBinding(x)))
            <|>
            binding_property_property_name(&params);

        ret binding
    }
}

// BindingElement

enum BindingElement {
    SingleNameBinding(SingleNameBinding),
    BindingPattern(BindingPattern, Vec<CommonDelim>, Option<Initializer>),
}

// TODO: test
fn binding_element<I: U8Input>(i: ESInput<I>,
                               params: &Parameters)
                               -> ESParseResult<I, BindingElement> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of binding_element");
        }
    }

    #[inline]
    fn binding_element_binding_pattern<I: U8Input>(i: ESInput<I>,
                                                   params: &Parameters)
                                                   -> ESParseResult<I, BindingElement> {

        let mut init_params = params.clone();
        init_params.insert(Parameter::In);

        parse!{i;
            let bind_pat = binding_pattern(&params);

            // TODO: merge
            let delim = common_delim();

            let init = option(|i| initializer(i, &init_params).map(|x| Some(x)),
                None);

            ret BindingElement::BindingPattern(bind_pat, delim, init)
        }
    }

    parse!{i;

        let binding =
            (i -> single_name_binding(i, &params).map(|x| BindingElement::SingleNameBinding(x)))
            <|>
            binding_element_binding_pattern(&params);

        ret binding
    }
}

// SingleNameBinding

struct SingleNameBinding(BindingIdentifier, Option<(Vec<CommonDelim>, Initializer)>);

// TODO: test
fn single_name_binding<I: U8Input>(i: ESInput<I>,
                                   params: &Parameters)
                                   -> ESParseResult<I, SingleNameBinding> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of single_name_binding");
        }
    }

    let mut init_params = params.clone();
    init_params.insert(Parameter::In);

    parse!{i;

        let ident = binding_identifier(&params);

        let init = option(|i| {
            common_delim(i)
                .bind(|i, delim| {

                    initializer(i, &init_params)
                        .map(|init| Some((delim, init)))
                })
        },
            None);

        ret SingleNameBinding(ident, init)
    }
}

// BindingRestElement

enum BindingRestElement {
    BindingIdentifier(Vec<CommonDelim>, BindingIdentifier),
    BindingPattern(Vec<CommonDelim>, BindingPattern),
}

// TODO: test
fn binding_rest_element<I: U8Input>(i: ESInput<I>,
                                    params: &Parameters)
                                    -> ESParseResult<I, BindingRestElement> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of binding_rest_element");
        }
    }

    enum BindingRestElementContent {
        BindingIdentifier(BindingIdentifier),
        BindingPattern(BindingPattern),
    }

    parse!{i;

        (i -> {
            on_error(string(i, b"..."),
                |i| {
                    let loc = i.position();
                    // TODO: proper err message?
                    ErrorLocation::new(loc, "Expected ... here.".to_string())
                }
            )
        });

        let delim = common_delim();

        let contents = (i -> binding_identifier(i, &params).map(BindingRestElementContent::BindingIdentifier))
            <|>
            (i -> binding_pattern(i, &params).map(BindingRestElementContent::BindingPattern));

        ret {
            match contents {
                BindingRestElementContent::BindingIdentifier(x) => BindingRestElement::BindingIdentifier(delim, x),
                BindingRestElementContent::BindingPattern(x) => BindingRestElement::BindingPattern(delim, x)
            }
        }
    }
}

// TODO: remove this
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
