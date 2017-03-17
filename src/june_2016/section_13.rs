// rust imports

use std::rc::Rc;
use std::cell::RefCell;

// 3rd-party imports

use chomp::types::{U8Input, Input};
use chomp::prelude::Either;

// local imports

use super::types::{Parameters, Parameter};
use super::section_11::{common_delim, common_delim_required, CommonDelim, SemiColon, semicolon};
use super::section_12::{initializer, Initializer, binding_identifier, BindingIdentifier,
                        PropertyName, property_name, elision, Elision, Expression, expression};
use parsers::{ESInput, ESParseResult, parse_list, token, option, string, on_error, either, or};
use parsers::error_location::ErrorLocation;

// 13 ECMAScript Language: Statements and Declarations
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-statements-and-declarations

// Statement

enum Statement {
    BlockStatement(BlockStatement),
    VariableStatement(VariableStatement),
    EmptyStatement(EmptyStatement),
    ExpressionStatement(ExpressionStatement), /* TODO: fix
                                               *     IfStatement(Box<IfStatement>),
                                               *     BreakableStatement(BreakableStatement), // TODO: more stuff */
}

// TODO: test
fn statement<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, Statement> {

    if is_debug_mode!() {
        if !(params.is_empty() || params.contains(&Parameter::Yield) ||
             params.contains(&Parameter::Return)) {
            panic!("misuse of statement");
        }
    }

    let mut yield_params = params.clone();
    yield_params.remove(&Parameter::Return);
    let yield_params = yield_params;

    parse!{i;

        let stmt =
        (i -> block_statement(i, &params).map(Statement::BlockStatement))
        <|>
        (i -> variable_statement(i, &yield_params).map(Statement::VariableStatement))
        <|>
        (i -> empty_statement(i).map(Statement::EmptyStatement))
        <|>
        (i -> expression_statement(i, &yield_params).map(Statement::ExpressionStatement));
    //     <|>
    //     (i -> if_statement(i, &params).map(|x| Statement::IfStatement(Box::new(x))))
    //     <|>
    //     (i -> breakable_statement(i, &params).map(Statement::BreakableStatement));

    //     // TODO: more statements

        ret stmt
    }
}

// Declaration

struct Declaration;

// TODO: test
fn declaration<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, Declaration> {

    if is_debug_mode!() {
        // validation
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

// 13.3 Declarations and the Variable Statement

// 13.3.1 Let and Const Declarations

// TODO: LexicalDeclaration

enum LetOrConst {
    Let,
    Const
}

// TODO: test
fn let_or_const<I: U8Input>(i: ESInput<I>)
                                  -> ESParseResult<I, LetOrConst> {
    or(i, |i| string(i, b"let").map(|_| LetOrConst::Let),
        |i| string(i, b"const").map(|_| LetOrConst::Const))
}

// TODO: BindingList

enum LexicalBinding {
    BindingIdentifier(BindingIdentifier, Option<(Vec<CommonDelim>, Initializer)>),
    BindingPattern(BindingPattern, Vec<CommonDelim>, Initializer),
}

// TODO: test
fn lexical_binding<I: U8Input>(i: ESInput<I>, params: &Parameters)
                                  -> ESParseResult<I, LexicalBinding> {

    ensure_params!(params; "lexical_binding"; Parameter::In; Parameter::Yield);

    let binding_params = {
        let mut binding_params = params.clone();
        binding_params.remove(&Parameter::In);
        binding_params
    };

    or(i,
        |i| {
            parse!{i;

                let ident = binding_identifier(&binding_params);

                let init = option(|i| -> ESParseResult<I, Option<(Vec<CommonDelim>, Initializer)>> {
                    parse!{i;

                        let delim = common_delim();
                        let init = initializer(&params);

                        ret {
                            Some((delim, init))
                        }
                    }
                }, None);

                ret {
                    LexicalBinding::BindingIdentifier(ident, init)
                }
            }
        },
        |i| {
            parse!{i;

                let ident = binding_pattern(&binding_params);

                let delim = common_delim();

                let init = initializer(&params);

                ret {
                    LexicalBinding::BindingPattern(ident, delim, init)
                }
            }
        })
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

// BindingPattern

enum BindingPattern {
    ObjectBindingPattern(Box<ObjectBindingPattern>),
    ArrayBindingPattern(Box<ArrayBindingPattern>),
}

// TODO: test
fn binding_pattern<I: U8Input>(i: ESInput<I>,
                               params: &Parameters)
                               -> ESParseResult<I, BindingPattern> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of binding_pattern");
        }
    }

    or(i,
       |i| {
           object_binding_pattern(i, &params)
               .map(|x| BindingPattern::ObjectBindingPattern(Box::new(x)))
       },
       |i| {
           array_binding_pattern(i, &params)
               .map(|x| BindingPattern::ArrayBindingPattern(Box::new(x)))
       })
}

// ObjectBindingPattern

enum ObjectBindingPattern {
    Empty(Vec<CommonDelim>, Vec<CommonDelim>),
    BindingPropertyList(BindingPropertyList),
    BindingPropertyListTrailingComma(BindingPropertyList,
                                     /* , (comma) */
                                     Vec<CommonDelim>),
}

// TODO: test
fn object_binding_pattern<I: U8Input>(i: ESInput<I>,
                                      params: &Parameters)
                                      -> ESParseResult<I, ObjectBindingPattern> {
    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of object_binding_pattern");
        }
    }

    #[inline]
    fn contents<I: U8Input>(i: ESInput<I>,
                            params: &Parameters)
                            -> ESParseResult<I, ObjectBindingPattern> {
        parse!{i;

            let list = binding_property_list(params);

            let trailing_comma = option(|i| -> ESParseResult<I, _> {
                parse!{i;
                    let delim = common_delim();
                    token(b',');
                    ret Some(delim)
                }
            }, None);

            ret {
                match trailing_comma {
                    None => ObjectBindingPattern::BindingPropertyList(list),
                    Some(delims) => ObjectBindingPattern::BindingPropertyListTrailingComma(list, delims)
                }
            }
        }
    }

    parse!{i;

        token(b'{');
        let left_delim = common_delim();

        let contents = option(|i| contents(i, &params).map(|x| Some(x)),
            None);

        let right_delim = common_delim();
        token(b'}');

        ret {
            if contents.is_none() {
                ObjectBindingPattern::Empty(left_delim, right_delim)
            } else {
                contents.unwrap()
            }
        }
    }
}

// ArrayBindingPattern

struct ArrayBindingPattern(/* [ (left bracket) */
                           Vec<CommonDelim>,
                           ArrayBindingPatternContents,
                           Vec<CommonDelim> /* ] (right bracket) */);

enum ArrayBindingPatternContents {
    Rest(Option<Elision>, Vec<CommonDelim>, Option<BindingRestElement>),
    List(BindingElementList),
    ListWithRest(BindingElementList,
                 Vec<CommonDelim>, /* , (comma) */
                 Vec<CommonDelim>,
                 Option<Elision>,
                 Vec<CommonDelim>,
                 Option<BindingRestElement>),
}

// TODO: test
fn array_binding_pattern<I: U8Input>(i: ESInput<I>,
                                     params: &Parameters)
                                     -> ESParseResult<I, ArrayBindingPattern> {
    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of array_binding_pattern");
        }
    }

    #[inline]
    fn array_binding_pattern_rest<I: U8Input>
        (i: ESInput<I>,
         params: &Parameters)
         -> ESParseResult<I, (Option<Elision>, Vec<CommonDelim>, Option<BindingRestElement>)> {
        parse!{i;

            let elision = option(|i| elision(i).map(|x| Some(x)),
                None);
            let delim = common_delim();

            let rest = option(|i| binding_rest_element(i, &params).map(|x| Some(x)),
                None);

            ret (elision, delim, rest)
        }
    }

    #[inline]
    fn array_binding_pattern_contents<I: U8Input>
        (i: ESInput<I>,
         params: &Parameters)
         -> ESParseResult<I, ArrayBindingPatternContents> {
        parse!{i;

            // [BindingElementList_[?Yield]]
            // [BindingElementList_[?Yield] , Elision_opt BindingRestElement_[?Yield]_opt]

            let list = binding_element_list(&params);

            let maybe_end = option(|i| -> ESParseResult<I, _> {
                parse!{i;

                    let delim_1 = common_delim();

                    (i -> {
                        on_error(token(i, b','),
                            |i| {
                                let loc = i.position();
                                // TODO: proper err message?
                                ErrorLocation::new(loc, "Expected , delimeter here.".to_string())
                            }
                        )
                    });

                    let delim_2 = common_delim();

                    let (elision, delim_3, rest) = array_binding_pattern_rest(&params);

                    ret Some((delim_1, delim_2, elision, delim_3, rest))
                }
            }, None);

            ret {
                match maybe_end {
                    None => ArrayBindingPatternContents::List(list),
                    Some((delim_1, delim_2, elision, delim_3, rest)) =>
                        ArrayBindingPatternContents::ListWithRest(list, delim_1, delim_2, elision, delim_3, rest),
                }
            }
        }
    }

    parse!{i;

        token(b'[');
        let delim_left = common_delim();

        let contents = array_binding_pattern_contents(&params)
            <|>
            (i -> array_binding_pattern_rest(i, &params).map(|(elision, delim, rest)| {
                ArrayBindingPatternContents::Rest(elision, delim, rest)
            }));

        let delim_right = common_delim();
        token(b']');

        ret ArrayBindingPattern(delim_left, contents, delim_right)
    }
}

// BindingPropertyList

struct BindingPropertyList(BindingProperty, Vec<BindingPropertyListRest>);

impl BindingPropertyList {
    fn new(rhs_val: BindingProperty) -> Self {
        BindingPropertyList(rhs_val, vec![])
    }

    fn add_item(self, operator_delim: BindingPropertyListDelim, rhs_val: BindingProperty) -> Self {

        let BindingPropertyList(head, rest) = self;
        let mut rest = rest;

        let BindingPropertyListDelim(delim_1, delim_2) = operator_delim;

        let rhs = BindingPropertyListRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        BindingPropertyList(head, rest)
    }
}

struct BindingPropertyListRest(Vec<CommonDelim>,
                               /* , (comma) */
                               Vec<CommonDelim>,
                               BindingProperty);

struct BindingPropertyListDelim(Vec<CommonDelim>,
                                /* , (comma) */
                                Vec<CommonDelim>);

generate_list_parser!(
    BindingPropertyList;
    BindingPropertyListRest;
    BindingPropertyListState;
    BindingPropertyListDelim;
    BindingProperty);

// TODO: test
fn binding_property_list<I: U8Input>(i: ESInput<I>,
                                     params: &Parameters)
                                     -> ESParseResult<I, BindingPropertyList> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of binding_property_list");
        }
    }

    type Accumulator = Rc<RefCell<BindingPropertyListState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            (i -> {
                on_error(token(i, b','),
                    |i| {
                        let loc = i.position();
                        // TODO: proper err message?
                        ErrorLocation::new(loc, "Expected , here.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();

            ret {
                let delim = BindingPropertyListDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        binding_property(i, &params).bind(|i, rhs| {
            accumulator.borrow_mut().add_item(rhs);
            i.ret(())
        })
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// BindingElementList

struct BindingElementList(BindingElisionElement, Vec<BindingElementListRest>);

impl BindingElementList {
    fn new(rhs_val: BindingElisionElement) -> Self {
        BindingElementList(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: BindingElementListDelim,
                rhs_val: BindingElisionElement)
                -> Self {

        let BindingElementList(head, rest) = self;
        let mut rest = rest;

        let BindingElementListDelim(delim_1, delim_2) = operator_delim;

        let rhs = BindingElementListRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        BindingElementList(head, rest)
    }
}

struct BindingElementListRest(Vec<CommonDelim>,
                              /* , (comma) */
                              Vec<CommonDelim>,
                              BindingElisionElement);

struct BindingElementListDelim(Vec<CommonDelim>,
                               /* , (comma) */
                               Vec<CommonDelim>);

generate_list_parser!(
    BindingElementList;
    BindingElementListRest;
    BindingElementListState;
    BindingElementListDelim;
    BindingElisionElement);

// TODO: test
fn binding_element_list<I: U8Input>(i: ESInput<I>,
                                    params: &Parameters)
                                    -> ESParseResult<I, BindingElementList> {
    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of binding_elision_list");
        }
    }

    type Accumulator = Rc<RefCell<BindingElementListState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            (i -> {
                on_error(token(i, b','),
                    |i| {
                        let loc = i.position();
                        // TODO: proper err message?
                        ErrorLocation::new(loc, "Expected , here.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();

            ret {
                let delim = BindingElementListDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        binding_elision_element(i, &params).bind(|i, rhs| {
            accumulator.borrow_mut().add_item(rhs);
            i.ret(())
        })
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// BindingElisionElement

struct BindingElisionElement(Option<Elision>, Vec<CommonDelim>, BindingElement);

// TODO: test
fn binding_elision_element<I: U8Input>(i: ESInput<I>,
                                       params: &Parameters)
                                       -> ESParseResult<I, BindingElisionElement> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of binding_elision_element");
        }
    }

    parse!{i;

        let e = option(|i| elision(i).map(Some),
            None);

        let delim = common_delim();

        let bind_elem = binding_element(&params);

        ret BindingElisionElement(e, delim, bind_elem)
    }
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

pub enum BindingElement {
    SingleNameBinding(SingleNameBinding),
    BindingPattern(BindingPattern, Vec<CommonDelim>, Option<Initializer>),
}

// TODO: test
pub fn binding_element<I: U8Input>(i: ESInput<I>,
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

pub enum BindingRestElement {
    BindingIdentifier(Vec<CommonDelim>, BindingIdentifier),
    BindingPattern(Vec<CommonDelim>, BindingPattern),
}

// TODO: test
pub fn binding_rest_element<I: U8Input>(i: ESInput<I>,
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

// 13.4 Empty Statement

struct EmptyStatement(SemiColon);

// TODO: test
fn empty_statement<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, EmptyStatement> {
    semicolon(i).map(EmptyStatement)
}

// 13.5 Expression Statement

struct ExpressionStatement(Expression, SemiColon);

// TODO: test
fn expression_statement<I: U8Input>(i: ESInput<I>,
                                    params: &Parameters)
                                    -> ESParseResult<I, ExpressionStatement> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of expression_statement");
        }
    }

    either(i,
           |i| -> ESParseResult<I, ()> {
        parse!{i;

                string(b"{") <|>
                string(b"function") <|>
                string(b"class") <|>
                string(b"let") <|>
                string(b"[");

                ret {()}
            }
    },
           |i| {

        let mut in_params = params.clone();
        in_params.insert(Parameter::In);
        let in_params = in_params;

        parse!{i;

                let expr = expression(&in_params);
                let semi_colon = semicolon();

                ret ExpressionStatement(expr, semi_colon)
            }
    })
        .bind(|i, result| {
            match result {
                // TODO: improve error message to indicate token that should not be produced
                Either::Left(_) => i.err("".into()),
                Either::Right(statement) => i.ret(statement),
            }
        })
}

// 13.6 The if Statement

enum IfStatement {
    OneBranch(/* if */
              Vec<CommonDelim>,
              /* ( */
              Vec<CommonDelim>,
              Expression,
              Vec<CommonDelim>,
              /* ) */
              Vec<CommonDelim>,
              Statement),
    TwoBranch(/* if */
              Vec<CommonDelim>,
              /* ( */
              Vec<CommonDelim>,
              Expression,
              Vec<CommonDelim>,
              /* ) */
              Vec<CommonDelim>,
              Statement,
              Vec<CommonDelim>,
              /* else */
              Vec<CommonDelim>,
              Statement),
}

// TODO: test
fn if_statement<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, IfStatement> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield) ||
             params.contains(&Parameter::Return)) {
            panic!("misuse of if_statement");
        }
    }

    let mut test_condition_params = Parameters::new();
    test_condition_params.insert(Parameter::In);

    if params.contains(&Parameter::Yield) {
        test_condition_params.insert(Parameter::Yield);
    }
    let test_condition_params = test_condition_params;

    #[inline]
    fn optional_else<I: U8Input>
        (i: ESInput<I>,
         params: &Parameters)
         -> ESParseResult<I, (Vec<CommonDelim>, Vec<CommonDelim>, Statement)> {

        if is_debug_mode!() {
            // validation
            if !(params.is_empty() || params.contains(&Parameter::Yield) ||
                 params.contains(&Parameter::Return)) {
                panic!("misuse of optional_else");
            }
        }

        parse!{i;

            let delim_1 = common_delim();
            string(b"else");
            let delim_2 = common_delim();

            let stmt = statement(&params);

            ret {
                (delim_1, delim_2, stmt)
            }
        }
    }

    parse!{i;

        string(b"if");

        let delim_1 = common_delim();
        token(b'(');
        let delim_2 = common_delim();

        let expr = expression(&test_condition_params);

        let delim_3 = common_delim();
        token(b')');
        let delim_4 = common_delim();

        let stmt = statement(&params);

        let else_branch = option(
            |i| optional_else(i, &params).map(Some),
            None);

        ret {
            match else_branch {
                Some((delim_5, delim_6, else_branch)) => {
                    IfStatement::TwoBranch(delim_1, delim_2, expr, delim_3, delim_4, stmt, delim_5, delim_6, else_branch)
                },
                None => {
                    IfStatement::OneBranch(delim_1, delim_2, expr, delim_3, delim_4, stmt)
                }
            }
        }
    }
}

// 13.7 Iteration Statements

enum IterationStatement {
    DoWhile(/* do */
            Vec<CommonDelim>,
            Statement,
            Vec<CommonDelim>,
            /* while */
            Vec<CommonDelim>,
            /* ( */
            Vec<CommonDelim>,
            Expression,
            Vec<CommonDelim>,
            /* ) */
            SemiColon),
    While(/* while */
          Vec<CommonDelim>,
          /* ( */
          Vec<CommonDelim>,
          Expression,
          Vec<CommonDelim>,
          /* ) */
          Vec<CommonDelim>,
          Statement),

    ForLoop(/* for */
            Vec<CommonDelim>,
            /* ( */
            Vec<CommonDelim>,
            // initialization
            Option<Expression>,
            Vec<CommonDelim>,
            /* ;
            condition */
            Vec<CommonDelim>,
            Option<Expression>,
            Vec<CommonDelim>,
            /* ;
            afterthought */
            Vec<CommonDelim>,
            Option<Expression>,
            Vec<CommonDelim>,
            /* ) */
            Vec<CommonDelim>,
            Statement),

    ForVarLoop(/* for */
            Vec<CommonDelim>,
            /* ( */
            Vec<CommonDelim>,
            /* var */
            Vec<CommonDelim>,
            // initialization
            VariableDeclarationList,
            Vec<CommonDelim>,
            /* ;
            condition */
            Vec<CommonDelim>,
            Option<Expression>,
            Vec<CommonDelim>,
            /* ;
            afterthought */
            Vec<CommonDelim>,
            Option<Expression>,
            Vec<CommonDelim>,
            /* ) */
            Vec<CommonDelim>,
            Statement),

    ForDeclarationLoop,

    ForIn,
    ForVarIn,
    ForDeclarationIn,

    ForOf,
    ForVarOf,
    ForDeclarationOf,
}

// TODO: test
fn iteration_statement<I: U8Input>(i: ESInput<I>,
                                   params: &Parameters)
                                   -> ESParseResult<I, IterationStatement> {

    ensure_params!(params; "iteration_statement"; Parameter::Return; Parameter::Yield);

    let expr_params = {
        let mut expr_params = params.clone();

        expr_params.remove(&Parameter::Return);
        expr_params.insert(Parameter::In);

        expr_params
    };
    let expr_params = &expr_params;

    fn do_while<I: U8Input>(i: ESInput<I>,
                            params: &Parameters,
                            expr_params: &Parameters)
                            -> ESParseResult<I, IterationStatement> {
        parse!{i;

            string(b"do");

            let delim_1 = common_delim();

            let stmt = statement(params);

            let delim_2 = common_delim();

            string(b"while");

            let delim_3 = common_delim();

            string(b"(");

            let delim_4 = common_delim();

            let expr = expression(expr_params);

            let delim_5 = common_delim();

            string(b")");

            let semi_colon = semicolon();

            ret {
                IterationStatement::DoWhile(delim_1, stmt, delim_2, delim_3, delim_4, expr, delim_5, semi_colon)
            }
        }
    }

    fn while_parse<I: U8Input>(i: ESInput<I>,
                               params: &Parameters,
                               expr_params: &Parameters)
                               -> ESParseResult<I, IterationStatement> {
        parse!{i;

            string(b"while");

            let delim_1 = common_delim();

            string(b"(");

            let delim_2 = common_delim();

            let expr = expression(&expr_params);

            let delim_3 = common_delim();

            string(b")");

            let delim_4 = common_delim();

            let stmt = statement(&params);

            ret {
                IterationStatement::While(delim_1, delim_2, expr, delim_3, delim_4, stmt)
            }
        }
    }

    fn for_loop<I: U8Input>(i: ESInput<I>,
                            params: &Parameters,
                            expr_params: &Parameters)
                            -> ESParseResult<I, IterationStatement> {

        let init_expr_params = {
            let mut init_expr_params = expr_params.clone();
            init_expr_params.remove(&Parameter::In);
            init_expr_params
        };

        parse!{i;


            string(b"for");

            let delim_1 = common_delim();

            string(b"(");

            let delim_2 = common_delim();

            // initialization

            let initialization = (i -> {
                either(i, |i| or(i, |i| string(i, b"let"), |i| string(i, b"[")),
                    |i| option(i, |i| expression(i, &init_expr_params).map(Some), None))
                    .bind(|i, result| -> ESParseResult<I, Option<Expression>> {
                        match result {
                            // TODO: err
                            Either::Left(_) => i.err("".into()),
                            Either::Right(expr) => i.ret(expr)
                        }
                    })
            });

            let delim_3 = common_delim();

            string(b";");

            let delim_4 = common_delim();

            // condition

            let condition = option(|i| expression(i, &expr_params).map(Some), None);

            let delim_5 = common_delim();

            string(b";");

            let delim_6 = common_delim();

            let afterthought = option(|i| expression(i, &expr_params).map(Some), None);

            let delim_7 = common_delim();

            string(b")");

            let delim_8 = common_delim();

            let stmt = statement(&params);

            ret {
                IterationStatement::ForLoop(delim_1, delim_2, initialization,
                    delim_3, delim_4, condition, delim_5, delim_6, afterthought, delim_7, delim_8, stmt)
            }
        }
    }

    fn for_var_loop<I: U8Input>(i: ESInput<I>,
                                params: &Parameters,
                                expr_params: &Parameters)
                                -> ESParseResult<I, IterationStatement> {

        let init_expr_params = {
            let mut init_expr_params = expr_params.clone();
            init_expr_params.remove(&Parameter::In);
            init_expr_params
        };

        parse!{i;


            string(b"for");

            let delim_1 = common_delim();

            string(b"(");

            let delim_2 = common_delim();

            string(b"var");

            let delim_3 = common_delim();

            // initialization

            let vars_list = variable_declaration_list(&init_expr_params);

            let delim_4 = common_delim();

            string(b";");

            let delim_5 = common_delim();

            // condition

            let condition = option(|i| expression(i, &expr_params).map(Some), None);

            let delim_6 = common_delim();

            string(b";");

            let delim_7 = common_delim();

            let afterthought = option(|i| expression(i, &expr_params).map(Some), None);

            let delim_8 = common_delim();

            string(b")");

            let delim_9 = common_delim();

            let stmt = statement(&params);

            ret {
                IterationStatement::ForVarLoop(delim_1, delim_2, delim_3, vars_list, delim_4, delim_5, condition, delim_6, delim_7, afterthought, delim_8, delim_9, stmt)
            }
        }
    }

    let parse_result = parse!{i;

        let iteration_statement: IterationStatement =

            do_while(&params, &expr_params) <|>
            while_parse(&params, &expr_params) <|>

            for_loop(&params, &expr_params) <|>
            for_var_loop(&params, &expr_params) <|>
            for_declaration_loop(&params, &expr_params);


        ret iteration_statement
    };

    parse_result
}

// 13.8 The continue Statement

// TODO: complete

// 13.9 The break Statement

// TODO: complete

// 13.10 The return Statement

// TODO: complete

// 13.11 The with Statement

// TODO: complete

// 13.12 The switch Statement

// TODO: complete

// 13.13 Labelled Statements

// TODO: complete

// 13.14 The throw Statement

// TODO: complete

// 13.15 The try Statement

// TODO: complete

// 13.16 The debugger Statement

// TODO: complete

// ----

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
