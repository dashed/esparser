// rust imports

use std::rc::Rc;
use std::cell::RefCell;

// 3rd-party imports

use chomp::types::{U8Input, Input};
use chomp::prelude::Either;

// local imports

use parsers::{ESParseResult, ESInput, string, parse_utf8_char, on_error, many, many1, string_till,
              token, option, either, parse_list, ErrorChain, ESParseError};
use super::section_11::{reserved_word, identifier_name, IdentifierName, CommonDelim, common_delim,
                        string_literal, StringLiteral, numeric_literal, NumericLiteral};
use super::section_14::{method_definition, MethodDefinition};
use super::types::{Parameters, Parameter};
use parsers::error_location::ErrorLocation;

// 12 ECMAScript Language: Expressions
//
// Reference: http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-expressions

// 12.1 Identifiers

// TODO: move this somewhere
#[inline]
fn yield_keyword<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, I::Buffer> {
    on_error(string(i, b"yield"), |i| {
        let reason = format!("Expected yield keyword.");
        ErrorLocation::new(i.position(), reason)
    })
}

// IdentifierReference

enum IdentifierReference {
    Identifier(Identifier),
    Yield,
}

// TODO: test
fn identifier_reference<I: U8Input>(i: ESInput<I>,
                                    params: &Parameters)
                                    -> ESParseResult<I, IdentifierReference> {

    if !params.contains(&Parameter::Yield) {

        let result = either(i,
                            // left
                            yield_keyword,
                            // right
                            identifier)
            .bind(|i, result| {
                match result {
                    Either::Left(_) => i.ret(IdentifierReference::Yield),
                    Either::Right(ident) => i.ret(IdentifierReference::Identifier(ident)),
                }
            });

        return result;
    }

    if is_debug_mode!() {
        if params.len() >= 2 {
            panic!("misuse of identifier_reference");
        }
    }

    identifier(i).map(|ident| IdentifierReference::Identifier(ident))

}

// BindingIdentifier

pub enum BindingIdentifier {
    Identifier(Identifier),
    Yield,
}

// TODO: test
pub fn binding_identifier<I: U8Input>(i: ESInput<I>,
                                      params: &Parameters)
                                      -> ESParseResult<I, BindingIdentifier> {

    if !params.contains(&Parameter::Yield) {

        let result = either(i,
                            // left
                            yield_keyword,
                            // right
                            identifier)
            .bind(|i, result| {
                match result {
                    Either::Left(_) => i.ret(BindingIdentifier::Yield),
                    Either::Right(ident) => i.ret(BindingIdentifier::Identifier(ident)),
                }
            });

        return result;
    }

    if is_debug_mode!() {
        // validation
        if params.len() >= 2 {
            panic!("misuse of binding_identifier");
        }
    }

    identifier(i).map(BindingIdentifier::Identifier)

}

// LabelIdentifier

enum LabelIdentifier {
    Identifier(Identifier),
    Yield,
}

// TODO: test
fn label_identifier<I: U8Input>(i: ESInput<I>,
                                params: &Parameters)
                                -> ESParseResult<I, LabelIdentifier> {

    if !params.contains(&Parameter::Yield) {

        let result = either(i,
                            // left
                            yield_keyword,
                            // right
                            identifier)
            .bind(|i, result| {
                match result {
                    Either::Left(_) => i.ret(LabelIdentifier::Yield),
                    Either::Right(ident) => i.ret(LabelIdentifier::Identifier(ident)),
                }
            });

        return result;
    }

    if params.len() >= 2 {
        panic!("misuse of binding_identifier");
    }

    identifier(i).map(|ident| LabelIdentifier::Identifier(ident))

}

// Identifier

struct Identifier(IdentifierName);

// TODO: test
fn identifier<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Identifier> {
    either(i,
           |i| reserved_word(i), // left
           |i| identifier_name(i) /* right */)
        .bind(|i, result| {
            match result {
                Either::Left(_) => {
                    let loc = i.position();
                    let reason = format!("Reserved keyword may not be used as an identifier.");
                    i.err(ErrorLocation::new(loc, reason).into())
                }
                Either::Right(name) => i.ret(Identifier(name)),
            }
        })
}

// 12.2.5 Array Initializer

// ArrayLiteral

struct ArrayLiteral(/* [ (left bracket) */
                    Vec<CommonDelim>,
                    ArrayLiteralContents,
                    Vec<CommonDelim> /* ] (right bracket) */);

enum ArrayLiteralContents {
    Empty(Option<Elision>),
    List(ElementList),
    ListWithElision(ElementList,
                    Vec<CommonDelim>,
                    /* , (comma) */
                    Vec<CommonDelim>,
                    Elision),
}


// TODO: test
fn array_literal<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, ArrayLiteral> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of array_literal");
        }
    }


    #[inline]
    fn array_literal_contents<I: U8Input>(i: ESInput<I>,
                                          params: &Parameters)
                                          -> ESParseResult<I, ArrayLiteralContents> {
        parse!{i;

            // [ElementList_[?Yield]]
            // [ElementList_[?Yield] , Elision_opt]

            let list = element_list(&params);

            let maybe_end = option(|i| -> ESParseResult<I, Option<(_, _, _)>> {
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
                    let elision = elision();

                    ret Some((delim_1, delim_2, elision))
                }
            }, None);

            ret {
                match maybe_end {
                    None => ArrayLiteralContents::List(list),
                    Some((delim_1, delim_2, elision)) => ArrayLiteralContents::ListWithElision(list, delim_1, delim_2, elision),
                }
            }
        }
    }

    parse!{i;

        token(b'[');
        let delim_left = common_delim();

        let contents = option(|i| elision(i).map(|x| ArrayLiteralContents::Empty(Some(x))),
            ArrayLiteralContents::Empty(None)) <|>
            array_literal_contents(&params);

        let delim_right = common_delim();
        token(b']');

        ret ArrayLiteral(delim_left, contents, delim_right)
    }
}

// ElementList

enum ElementListItem {
    ItemExpression(Option<Elision>, AssignmentExpression),
    ItemSpread(Option<Elision>, SpreadElement),
}

struct ElementList(ElementListItem, Vec<ElementListRest>);

impl ElementList {
    fn new(rhs_val: ElementListItem) -> Self {
        ElementList(rhs_val, vec![])
    }

    fn add_item(self, operator_delim: ElementListDelim, rhs_val: ElementListItem) -> Self {

        let ElementList(head, rest) = self;
        let mut rest = rest;

        let ElementListDelim(delim_1, delim_2) = operator_delim;

        let rhs = ElementListRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        ElementList(head, rest)
    }
}

struct ElementListRest(Vec<CommonDelim>,
                       /* , (comma) */
                       Vec<CommonDelim>,
                       ElementListItem);

struct ElementListDelim(Vec<CommonDelim>,
                        /* , (comma) */
                        Vec<CommonDelim>);

generate_list_parser!(
    ElementList;
    ElementListRest;
    ElementListState;
    ElementListDelim;
    ElementListItem);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-ElementList
fn element_list<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, ElementList> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of element_list");
        }
    }

    type Accumulator = Rc<RefCell<ElementListState>>;

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
                let delim = ElementListDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    let mut assign_expr = params.clone();
    assign_expr.insert(Parameter::In);

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;

            let elision_prefix = option(|i| elision(i).map(|x| Some(x)), None);

            let item = either(
                |i| {
                    assignment_expression(i, &assign_expr)
                },
                |i| {
                    spread_element(i, &params)
                }
            );

            ret {
                let rhs = match item {
                    Either::Left(x) => {
                        ElementListItem::ItemExpression(elision_prefix, x)
                    }
                    Either::Right(x) => {
                        ElementListItem::ItemSpread(elision_prefix, x)
                    }
                };

                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// Elision

// TODO: refactor
pub struct Elision(Vec<ElisionItem>);

enum ElisionItem {
    CommonDelim(Vec<CommonDelim>),
    Comma,
}

// TODO: test
pub fn elision<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Elision> {
    parse!{i;

        token(b',');

        let list: Vec<ElisionItem> = many(|i| -> ESParseResult<I, ElisionItem> {
            parse!{i;
                let l = (i -> common_delim(i).map(ElisionItem::CommonDelim)) <|>
                (i -> token(i, b',').map(|_| ElisionItem::Comma));
                ret l
            }
        });

        ret Elision(list)
    }
}

// SpreadElement

struct SpreadElement(AssignmentExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-SpreadElement
fn spread_element<I: U8Input>(i: ESInput<I>,
                              params: &Parameters)
                              -> ESParseResult<I, SpreadElement> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of spread_element");
        }
    }

    parse!{i;

        // spread operator
        (i -> {
            on_error(string(i, b"..."), |i| {
                let reason = format!("Expected spread oeprator.");
                ErrorLocation::new(i.position(), reason)
            })
        });

        common_delim();

        let expr = (i -> {
            let mut params = params.clone();
            params.insert(Parameter::In);
            assignment_expression(i, &params)
        });

        ret SpreadElement(expr)
    }
}


// 12.2.6 Object Initializer

// ObjectLiteral

struct ObjectLiteral(/* { (left curly bracket) */
                     Vec<CommonDelim>,
                     ObjectLiteralContents,
                     Vec<CommonDelim> /* } (right curly bracket) */);

enum ObjectLiteralContents {
    Empty,
    PropertyDefinitionList(PropertyDefinitionList),
    PropertyDefinitionListTrailingComma(PropertyDefinitionList, Vec<CommonDelim> /* , */),
}

// TODO: test
fn object_literal<I: U8Input>(i: ESInput<I>,
                              params: &Parameters)
                              -> ESParseResult<I, ObjectLiteral> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of object_literal");
        }
    }

    #[inline]
    fn object_literal_contents<I: U8Input>(i: ESInput<I>,
                                           params: &Parameters)
                                           -> ESParseResult<I, ObjectLiteralContents> {
        parse!{i;

            let list = property_definition_list(&params);

            let trailing_comma = option(|i| -> ESParseResult<I, _> {
                parse!{i;
                    let delim = common_delim();
                    token(b',');

                    ret Some(delim)
                }
            }, None);

            ret {
                match trailing_comma {
                    None => ObjectLiteralContents::PropertyDefinitionList(list),
                    Some(delim) => ObjectLiteralContents::PropertyDefinitionListTrailingComma(list, delim)
                }
            }
        }
    }

    parse!{i;

        token(b'{');
        let delim_left = common_delim();

        let contents = option(|i| object_literal_contents(i, &params), ObjectLiteralContents::Empty);

        let delim_right = common_delim();
        token(b'}');

        ret ObjectLiteral(delim_left, contents, delim_right)
    }
}

// PropertyDefinitionList

struct PropertyDefinitionList(PropertyDefinition, Vec<PropertyDefinitionListRest>);

impl PropertyDefinitionList {
    fn new(rhs_val: PropertyDefinition) -> Self {
        PropertyDefinitionList(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: PropertyDefinitionListDelim,
                rhs_val: PropertyDefinition)
                -> Self {

        let PropertyDefinitionList(head, rest) = self;
        let mut rest = rest;

        let PropertyDefinitionListDelim(delim_1, delim_2) = operator_delim;

        let rhs = PropertyDefinitionListRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        PropertyDefinitionList(head, rest)
    }
}

struct PropertyDefinitionListRest(Vec<CommonDelim>,
                                  /* , (comma) */
                                  Vec<CommonDelim>,
                                  PropertyDefinition);

struct PropertyDefinitionListDelim(Vec<CommonDelim>,
                                   /* , (comma) */
                                   Vec<CommonDelim>);

generate_list_parser!(
    PropertyDefinitionList;
    PropertyDefinitionListRest;
    PropertyDefinitionListState;
    PropertyDefinitionListDelim;
    PropertyDefinition);

// TODO: test
fn property_definition_list<I: U8Input>(i: ESInput<I>,
                                        params: &Parameters)
                                        -> ESParseResult<I, PropertyDefinitionList> {

    // validation
    if !(params.is_empty() || params.contains(&Parameter::Yield)) {
        panic!("misuse of property_definition_list");
    }

    type Accumulator = Rc<RefCell<PropertyDefinitionListState>>;

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
                let delim = PropertyDefinitionListDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        property_definition(i, &params).bind(|i, prop_def| {
            accumulator.borrow_mut().add_item(prop_def);
            i.ret(())
        })
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// PropertyDefinition

enum PropertyDefinition {
    IdentifierReference(IdentifierReference),
    CoverInitializedName(CoverInitializedName),
    PropertyName(PropertyName,
                 Vec<CommonDelim>,
                 /* : */
                 Vec<CommonDelim>,
                 AssignmentExpression),
    MethodDefinition(MethodDefinition),
}

// TODO: test
fn property_definition<I: U8Input>(i: ESInput<I>,
                                   params: &Parameters)
                                   -> ESParseResult<I, PropertyDefinition> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of property_definition");
        }
    }

    #[inline]
    fn prop_name<I: U8Input>(i: ESInput<I>,
                             params: &Parameters)
                             -> ESParseResult<I, PropertyDefinition> {

        let mut expr_params = params.clone();
        expr_params.insert(Parameter::In);
        let expr_params = expr_params;

        parse!{i;

            let name = property_name(&params);

            let delim_1 = common_delim();
            token(b':');
            let delim_2 = common_delim();

            let expr = assignment_expression(&expr_params);

            ret PropertyDefinition::PropertyName(name, delim_1, delim_2, expr)
        }
    }

    parse!{i;

        let prop_def =
            (i -> identifier_reference(i, &params).map(PropertyDefinition::IdentifierReference))
            <|>
            (i -> cover_initialized_name(i, &params).map(PropertyDefinition::CoverInitializedName))
            <|>
            prop_name(&params)
            <|>
            (i -> method_definition(i, &params).map(PropertyDefinition::MethodDefinition));

        ret prop_def
    }
}

// PropertyName

pub enum PropertyName {
    LiteralPropertyName(LiteralPropertyName),
    ComputedPropertyName(ComputedPropertyName),
}

// TODO: test
pub fn property_name<I: U8Input>(i: ESInput<I>,
                                 params: &Parameters)
                                 -> ESParseResult<I, PropertyName> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of property_name");
        }
    }

    parse!{i;

        let prop_name = (i -> literal_property_name(i).map(PropertyName::LiteralPropertyName))
        <|>
        (i -> computed_property_name(i, &params).map(PropertyName::ComputedPropertyName));

        ret prop_name
    }
}

// LiteralPropertyName

enum LiteralPropertyName {
    IdentifierName(IdentifierName),
    StringLiteral(StringLiteral),
    NumericLiteral(NumericLiteral),
}

// TODO: test
fn literal_property_name<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, LiteralPropertyName> {
    parse!{i;

        let literal_prop_name =
            (i -> identifier_name(i).map(LiteralPropertyName::IdentifierName))
            <|>
            (i -> string_literal(i).map(LiteralPropertyName::StringLiteral))
            <|>
            (i -> numeric_literal(i).map(LiteralPropertyName::NumericLiteral));

        ret literal_prop_name
    }
}

// ComputedPropertyName

struct ComputedPropertyName(/* [ */
                            Vec<CommonDelim>,
                            AssignmentExpression,
                            Vec<CommonDelim> /* ] */);

// TODO: test
fn computed_property_name<I: U8Input>(i: ESInput<I>,
                                      params: &Parameters)
                                      -> ESParseResult<I, ComputedPropertyName> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of computed_property_name");
        }
    }

    let mut params = params.clone();
    params.insert(Parameter::In);
    let params = params;

    parse!{i;

        token(b'[');
        let delim_left = common_delim();

        let expr = assignment_expression(&params);

        let delim_right = common_delim();
        token(b']');

        ret ComputedPropertyName(delim_left, expr, delim_right)
    }
}

// CoverInitializedName

struct CoverInitializedName(IdentifierReference, Vec<CommonDelim>, Initializer);

// TODO: test
fn cover_initialized_name<I: U8Input>(i: ESInput<I>,
                                      params: &Parameters)
                                      -> ESParseResult<I, CoverInitializedName> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of cover_initialized_name");
        }
    }

    parse!{i;

        let id_ref = identifier_reference(&params);

        let delim = common_delim();

        let initializer = (i -> {

            let mut params = params.clone();
            params.insert(Parameter::In);

            initializer(i, &params)
        });

        ret CoverInitializedName(id_ref, delim, initializer)
    }
}

// Initializer

pub struct Initializer(/* = */
                       Vec<CommonDelim>,
                       AssignmentExpression);

// TODO: test
pub fn initializer<I: U8Input>(i: ESInput<I>,
                               params: &Parameters)
                               -> ESParseResult<I, Initializer> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::In) ||
             params.contains(&Parameter::Yield)) {
            panic!("misuse of initializer");
        }
    }

    parse!{i;

        token(b'=');

        let delim = common_delim();

        let expr = assignment_expression(params);

        ret Initializer(delim, expr)
    }
}

// 12.15 Assignment Operators

// AssignmentExpression

struct AssignmentExpression;
// TODO: fix
// enum AssignmentExpression {
//     ConditionalExpression(Box<ConditionalExpression>),
// }

// TODO: test
fn assignment_expression<I: U8Input>(i: ESInput<I>,
                                     params: &Parameters)
                                     -> ESParseResult<I, AssignmentExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::In) ||
             params.contains(&Parameter::Yield)) {
            panic!("misuse of assignment_expression");
        }
    }

    i.ret(AssignmentExpression)
    // TODO: fix
    // parse!{i;

    //     let result = (i -> conditional_expression(i, params)
    //         .map(|x| AssignmentExpression::ConditionalExpression(Box::new(x))));

    //     // TODO: complete

    //     ret {
    //         result
    //     }
    // }
}
