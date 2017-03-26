// rust imports

use std::rc::Rc;
use std::cell::RefCell;

// 3rd-party imports

use chomp::types::{U8Input, Input};
use chomp::prelude::Either;

// local imports

use parsers::{ESParseResult, ESInput, string, parse_utf8_char, on_error, many, many1, string_till,
              token, option, either, parse_list, ErrorChain, ESParseError, or};
use super::section_11::{reserved_word, identifier_name, IdentifierName, CommonDelim, common_delim,
                        common_delim_no_line_term, string_literal, StringLiteral, numeric_literal,
                        NumericLiteral, boolean_literal, null_literal, Bool, template_middle,
                        TemplateMiddle, template_tail, TemplateTail, template_head, TemplateHead,
                        NoSubstitutionTemplate, no_substitution_template};
use super::section_14::{method_definition, MethodDefinition, function_expression,
                        FunctionExpression};
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

// 12.2 Primary Expression

enum PrimaryExpression {
    This,
    IdentifierReference(IdentifierReference),
    Literal(Literal),
    ArrayLiteral(ArrayLiteral),
    ObjectLiteral(ObjectLiteral),
    FunctionExpression(FunctionExpression),
    // TODO: ClassExpression(ClassExpression),
    // TODO: GeneratorExpression(GeneratorExpression),
    // TODO: RegularExpressionLiteral(RegularExpressionLiteral),
    TemplateLiteral(TemplateLiteral), /* TODO: CoverParenthesizedExpressionAndArrowParameterList(CoverParenthesizedExpressionAndArrowParameterList), */
}

fn primary_expression<I: U8Input>(i: ESInput<I>,
                                  params: &Parameters)
                                  -> ESParseResult<I, PrimaryExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of primary_expression");
        }
    }

    parse!{i;

        let result =

            (i -> string(i, b"this").map(|_| PrimaryExpression::This))

            // TODO: fix
            // on_error(
            //     |i| string(i, b"this").map(|_| PrimaryExpression::This),
            // |i| {
            //     let reason = format!("Expected this keyword.");
            //     ErrorLocation::new(i.position(), reason)
            // })

            <|>

            (i -> identifier_reference(i, &params)
                .map(PrimaryExpression::IdentifierReference))

            <|>
            (i -> literal(i).map(PrimaryExpression::Literal))
            <|>
            (i -> array_literal(i, &params).map(PrimaryExpression::ArrayLiteral))
            <|>
            (i -> object_literal(i, &params).map(PrimaryExpression::ObjectLiteral))
            <|>
            (i -> function_expression(i).map(PrimaryExpression::FunctionExpression))
            <|>
            (i -> template_literal(i, &params).map(PrimaryExpression::TemplateLiteral));

        ret result
    }

}

// 12.2.4 Literals

// Literal

enum Literal {
    Null,
    Boolean(Bool),
    Numeric(NumericLiteral),
    String(StringLiteral),
}

// TODO: test
fn literal<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, Literal> {
    parse!{i;
        let literal_result =
        (i -> null_literal(i).map(|_| Literal::Null)) <|>
        (i -> boolean_literal(i).map(Literal::Boolean)) <|>
        (i -> numeric_literal(i).map(Literal::Numeric)) <|>
        (i -> string_literal(i).map(Literal::String));
        ret literal_result
    }
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

// 12.2.9 Template Literals

// TemplateLiteral

enum TemplateLiteral {
    NoSubstitutionTemplate(NoSubstitutionTemplate),
    SubstitutionTemplate(TemplateHead,
                         Vec<CommonDelim>,
                         Expression,
                         Vec<CommonDelim>,
                         TemplateSpans),
}


// TODO: test
fn template_literal<I: U8Input>(i: ESInput<I>,
                                params: &Parameters)
                                -> ESParseResult<I, TemplateLiteral> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of template_literal");
        }
    }

    or(i,
       |i| no_substitution_template(i).map(TemplateLiteral::NoSubstitutionTemplate),
       |i| {

        let mut expr_params = params.clone();
        expr_params.insert(Parameter::In);
        let expr_params = expr_params;

        parse!{i;

                let head = template_head();

                let delim_left = common_delim();
                let expr = expression(&expr_params);
                let delim_right = common_delim();

                let spans = template_spans(&params);

                ret TemplateLiteral::SubstitutionTemplate(head, delim_left, expr, delim_right, spans)
            }
    })
}

// TemplateSpans

enum TemplateSpans {
    TemplateTail(TemplateTail),
    TemplateMiddleList(TemplateMiddleList, Vec<CommonDelim>, TemplateTail),
}

// TODO: test
fn template_spans<I: U8Input>(i: ESInput<I>,
                              params: &Parameters)
                              -> ESParseResult<I, TemplateSpans> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of template_spans");
        }
    }

    option(i, |i| template_middle_list(i, params).map(Some), None).bind(|i, result| {

        match result {
            Some(middle) => {
                common_delim(i)
                    .bind(|i, delim| template_tail(i).map(|tail| (delim, tail)))
                    .bind(|i, (delim, tail)| {
                        i.ret(TemplateSpans::TemplateMiddleList(middle, delim, tail))
                    })
            }
            None => template_tail(i).map(TemplateSpans::TemplateTail),
        }
    })
}

// TemplateMiddleList

struct TemplateMiddleListItem(TemplateMiddle,
                              /* ${ */
                              Vec<CommonDelim>,
                              Expression);

struct TemplateMiddleList(TemplateMiddleListItem, Vec<TemplateMiddleListItem>);

impl TemplateMiddleList {
    fn new(rhs_val: TemplateMiddleListItem) -> Self {
        TemplateMiddleList(rhs_val, vec![])
    }

    fn add_item(self, delim: TemplateMiddleListDelim, rhs_val: TemplateMiddleListItem) -> Self {

        let TemplateMiddleList(head, rest) = self;

        let mut rest = rest;

        rest.push(rhs_val);

        TemplateMiddleList(head, rest)
    }
}

struct TemplateMiddleListDelim;

generate_list_parser!(
    TemplateMiddleList;
    TemplateMiddleListItem; /* rest */
    TemplateMiddleListState;
    TemplateMiddleListDelim;
    TemplateMiddleListItem);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-TemplateMiddleList
fn template_middle_list<I: U8Input>(i: ESInput<I>,
                                    params: &Parameters)
                                    -> ESParseResult<I, TemplateMiddleList> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of template_middle_list");
        }
    }

    type Accumulator = Rc<RefCell<TemplateMiddleListState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            // no-op

            ret {
                accumulator.borrow_mut().add_delim(TemplateMiddleListDelim);
                ()
            }
        }
    }

    let mut expr_params = params.clone();
    expr_params.insert(Parameter::In);
    let expr_params = expr_params;

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {

        parse!{i;

            let middle = template_middle();

            let delim = common_delim();

            let expr = expression(&expr_params);

            ret {
                let rhs = TemplateMiddleListItem(middle, delim, expr);
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// 12.3 Left-Hand-Side Expressions

// MemberExpression

enum MemberExpressionHead {
    PrimaryExpression(PrimaryExpression),
    SuperProperty(SuperProperty),
    MetaProperty(MetaProperty),
    FunctionCall(/* new */
                 Vec<CommonDelim>,
                 Box<MemberExpression>,
                 Vec<CommonDelim>,
                 Arguments),
}

struct MemberExpression(MemberExpressionHead, Vec<MemberExpressionRest>);

impl MemberExpression {
    fn new(rhs_val: MemberExpressionItem) -> Self {
        match rhs_val {
            MemberExpressionItem::HeadItem(head) => MemberExpression(head, vec![]),
            MemberExpressionItem::RestItem(_) => panic!("invariant violation"),
        }
    }

    fn add_item(self,
                operator_delim: MemberExpressionDelim,
                rhs_val: MemberExpressionItem)
                -> Self {

        let MemberExpression(head, rest) = self;
        let mut rest = rest;

        let MemberExpressionDelim(delim) = operator_delim;

        let rest_item = match rhs_val {
            MemberExpressionItem::HeadItem(_head) => panic!("invariant violation"),
            MemberExpressionItem::RestItem(rest_item) => rest_item,
        };

        let rhs = MemberExpressionRest(delim, rest_item);

        rest.push(rhs);

        MemberExpression(head, rest)
    }
}

enum MemberExpressionRestItem {
    PropertyAccessorBracket(/* [ */
                            Vec<CommonDelim>,
                            Expression,
                            Vec<CommonDelim> /* ] */),
    PropertyAccessorDot(/* . */
                        Vec<CommonDelim>,
                        IdentifierName),
    TaggedTemplate(TemplateLiteral),
}

struct MemberExpressionRest(Vec<CommonDelim>, MemberExpressionRestItem);

struct MemberExpressionDelim(Vec<CommonDelim>);

enum MemberExpressionItem {
    HeadItem(MemberExpressionHead),
    RestItem(MemberExpressionRestItem),
}

generate_list_parser!(
    MemberExpression;
    MemberExpressionRest;
    MemberExpressionState;
    MemberExpressionDelim;
    MemberExpressionItem);

// TODO: test
fn member_expression<I: U8Input>(i: ESInput<I>,
                                 params: &Parameters)
                                 -> ESParseResult<I, MemberExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of member_expression");
        }
    }

    let mut expr_params = params.clone();
    expr_params.insert(Parameter::In);
    let expr_params = expr_params;

    type Accumulator = Rc<RefCell<MemberExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim = common_delim();

            ret {
                let delim = MemberExpressionDelim(delim);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {

        let is_initial = {
            accumulator.borrow().is_initial()
        };

        if is_initial {
            parse!{i;

                let head = (i -> primary_expression(i, &params).map(MemberExpressionHead::PrimaryExpression)) <|>

                    (i -> super_property(i, &params).map(MemberExpressionHead::SuperProperty)) <|>

                    (i -> meta_property(i).map(MemberExpressionHead::MetaProperty)) <|>

                    (i -> {
                        parse!{i;

                            string(b"new");

                            let delim_1 = common_delim();

                            let member_expr = member_expression(&params);

                            let delim_2 = common_delim();

                            let args = arguments(&params);

                            ret MemberExpressionHead::FunctionCall(delim_1, Box::new(member_expr), delim_2, args)
                        }
                    });

                ret {
                    let rhs = MemberExpressionItem::HeadItem(head);
                    accumulator.borrow_mut().add_item(rhs);
                    ()
                }
            }
        } else {
            parse!{i;

                let rest_item =
                    (i -> {
                        parse!{i;

                            token(b'[');
                            let delim_1 = common_delim();

                            let expr = expression(&expr_params);

                            let delim_2 = common_delim();
                            token(b']');

                            ret MemberExpressionRestItem::PropertyAccessorBracket(delim_1, expr, delim_2)
                        }
                    })
                    <|>
                    (i -> {
                        parse!{i;

                            token(b'.');
                            let delim = common_delim();

                            let name = identifier_name();

                            ret MemberExpressionRestItem::PropertyAccessorDot(delim, name)
                        }
                    })
                    <|>
                    (i -> template_literal(i, &params).map(MemberExpressionRestItem::TaggedTemplate));


                ret {
                    let rhs = MemberExpressionItem::RestItem(rest_item);
                    accumulator.borrow_mut().add_item(rhs);
                    ()
                }
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// SuperProperty

enum SuperProperty {
    PropertyAccessorBracket(/* super */
                            Vec<CommonDelim>,
                            /* [ */
                            Vec<CommonDelim>,
                            Expression,
                            Vec<CommonDelim> /* ] */),
    PropertyAccessorDot(/* super */
                        Vec<CommonDelim>,
                        /* . */
                        Vec<CommonDelim>,
                        IdentifierName),
}

// TODO: test
fn super_property<I: U8Input>(i: ESInput<I>,
                              params: &Parameters)
                              -> ESParseResult<I, SuperProperty> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of super_property");
        }
    }

    string(i, b"super")
        .then(|i| {
            or(i,
                |i| {
                    let mut params_expr = params.clone();
                    params_expr.insert(Parameter::In);

                    parse!{i;

                        let delim = common_delim();

                        token(b'[');
                        let delim_left = common_delim();

                        let expr = expression(&params_expr);

                        let delim_right = common_delim();
                        token(b']');

                        ret {
                            SuperProperty::PropertyAccessorBracket(delim, delim_left, expr, delim_right)
                        }
                    }
                },
                |i| {
                    parse!{i;

                        let delim = common_delim();

                        token(b'.');
                        let delim_left = common_delim();
                        let name = identifier_name();

                            ret {
                                SuperProperty::PropertyAccessorDot(delim, delim_left, name)
                            }
                    }
                })
        })
}

// MetaProperty

struct MetaProperty(NewTarget);

// TODO: test
fn meta_property<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, MetaProperty> {
    new_target(i).map(MetaProperty)
}
// NewTarget

struct NewTarget(/* new */
                 Vec<CommonDelim>,
                 /* . (dot) */
                 Vec<CommonDelim> /* target */);

// TODO: test
fn new_target<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, NewTarget> {
    parse!{i;

        string(b"new");

        let delim_1 = common_delim();

        string(b".");

        let delim_2 = common_delim();

        string(b"target");


        ret {
            NewTarget(delim_1, delim_2)
        }
    }
}

// NewExpression

enum NewExpression {
    MemberExpression(MemberExpression),
    NewExpression(/* new */
                  Vec<CommonDelim>,
                  Box<NewExpression>),
}

// TODO: test
fn new_expression<I: U8Input>(i: ESInput<I>,
                              params: &Parameters)
                              -> ESParseResult<I, NewExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of new_expression");
        }
    }

    or(i,
       |i| {
        parse!{i;
                string(b"new");

                let delim = common_delim();

                let new_expr = new_expression(&params);

                ret {
                    NewExpression::NewExpression(delim, Box::new(new_expr))
                }
            }
    },
       |i| member_expression(i, &params).map(NewExpression::MemberExpression))
}

// CallExpression

enum CallExpressionHead {
    FunctionCall(MemberExpression, Vec<CommonDelim>, Arguments),
    SuperCall(SuperCall),
}

struct CallExpression(CallExpressionHead, Vec<CallExpressionRest>);

impl CallExpression {
    fn new(rhs_val: CallExpressionItem) -> Self {
        match rhs_val {
            CallExpressionItem::HeadItem(head) => CallExpression(head, vec![]),
            CallExpressionItem::RestItem(_) => panic!("invariant violation"),
        }
    }

    fn add_item(self, operator_delim: CallExpressionDelim, rhs_val: CallExpressionItem) -> Self {

        let CallExpression(head, rest) = self;
        let mut rest = rest;

        let CallExpressionDelim(delim) = operator_delim;

        let rest_item = match rhs_val {
            CallExpressionItem::HeadItem(_head) => panic!("invariant violation"),
            CallExpressionItem::RestItem(rest_item) => rest_item,
        };

        let rhs = CallExpressionRest(delim, rest_item);

        rest.push(rhs);

        CallExpression(head, rest)
    }
}

enum CallExpressionRestItem {
    FunctionCall(Arguments),
    PropertyAccessorBracket(/* [ */
                            Vec<CommonDelim>,
                            Expression,
                            Vec<CommonDelim> /* ] */),
    PropertyAccessorDot(/* . */
                        Vec<CommonDelim>,
                        IdentifierName),
    TaggedTemplate(TemplateLiteral),
}

struct CallExpressionRest(Vec<CommonDelim>, CallExpressionRestItem);

struct CallExpressionDelim(Vec<CommonDelim>);

enum CallExpressionItem {
    HeadItem(CallExpressionHead),
    RestItem(CallExpressionRestItem),
}

generate_list_parser!(
    CallExpression;
    CallExpressionRest;
    CallExpressionState;
    CallExpressionDelim;
    CallExpressionItem);

// TODO: test
fn call_expression<I: U8Input>(i: ESInput<I>,
                               params: &Parameters)
                               -> ESParseResult<I, CallExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of call_expression");
        }
    }

    type Accumulator = Rc<RefCell<CallExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim = common_delim();

            ret {
                let delim = CallExpressionDelim(delim);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    let mut expr_params = params.clone();
    expr_params.insert(Parameter::In);
    let expr_params = expr_params;

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {

        let is_initial = {
            accumulator.borrow().is_initial()
        };

        if is_initial {
            parse!{i;

                let head = or(
                    |i| super_call(i, &params).map(CallExpressionHead::SuperCall),
                    |i| {
                        parse!{i;
                            let member = member_expression(&params);
                            let delim = common_delim();
                            let args = arguments(&params);

                            ret CallExpressionHead::FunctionCall(member, delim, args)
                        }
                    });

                ret {
                    let rhs = CallExpressionItem::HeadItem(head);
                    accumulator.borrow_mut().add_item(rhs);
                    ()
                }
            }
        } else {
            parse!{i;

                let rest_item =
                    (i -> {
                        arguments(i, &params)
                            .map(CallExpressionRestItem::FunctionCall)
                    }) <|>
                    (i -> {
                        parse!{i;

                            string(b"[");
                            let delim_left = common_delim();

                            let expr = expression(&expr_params);

                            let delim_right = common_delim();
                            string(b"]");

                            ret CallExpressionRestItem::PropertyAccessorBracket(delim_left, expr, delim_right)
                        }
                    }) <|>
                    (i -> {
                        parse!{i;
                            string(b".");
                            let delim_left = common_delim();
                            let ident = identifier_name();

                            ret CallExpressionRestItem::PropertyAccessorDot(delim_left, ident)
                        }
                    }) <|>
                    (i -> {
                        template_literal(i, &params)
                            .map(CallExpressionRestItem::TaggedTemplate)
                    });

                ret {
                    let rhs = CallExpressionItem::RestItem(rest_item);
                    accumulator.borrow_mut().add_item(rhs);
                    ()
                }
            }
        }

    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// SuperCall

struct SuperCall(/* super */
                 Vec<CommonDelim>,
                 Arguments);

// TODO: test
fn super_call<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, SuperCall> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of super_call");
        }
    }

    parse!{i;

        string(b"super");

        let delim = common_delim();

        let args = arguments(params);

        ret SuperCall(delim, args)
    }
}

// Arguments

enum Arguments {
    NoArguments(Vec<CommonDelim>),
    Arguments(Vec<CommonDelim>, ArgumentList, Vec<CommonDelim>),
}

// TODO: test
fn arguments<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, Arguments> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of arguments");
        }
    }

    or(i,
       |i| {
        parse!{i;

                string(b"(");
                let delim = common_delim();
                string(b")");

                ret Arguments::NoArguments(delim)
            }
    },
       |i| {
        parse!{i;

                string(b"(");
                let delim_1 = common_delim();

                let args_list = arguments_list(&params);

                let delim_2 = common_delim();
                string(b")");

                ret Arguments::Arguments(delim_1, args_list, delim_2)
            }
    })
}

// ArgumentList

enum ArgumentListItem {
    AssignmentExpression(AssignmentExpression),
    RestAssignmentExpression(/* ... */
                             Vec<CommonDelim>,
                             AssignmentExpression),
}

struct ArgumentList(ArgumentListItem, Vec<ArgumentListRest>);

impl ArgumentList {
    fn new(rhs_val: ArgumentListItem) -> Self {
        ArgumentList(rhs_val, vec![])
    }

    fn add_item(self, operator_delim: ArgumentListDelim, rhs_val: ArgumentListItem) -> Self {

        let ArgumentList(head, rest) = self;
        let mut rest = rest;

        let ArgumentListDelim(delim_1, delim_2) = operator_delim;

        let rhs = ArgumentListRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        ArgumentList(head, rest)
    }
}

struct ArgumentListRest(Vec<CommonDelim>,
                        /* , (comma) */
                        Vec<CommonDelim>,
                        ArgumentListItem);

struct ArgumentListDelim(Vec<CommonDelim>,
                         /* , (comma) */
                         Vec<CommonDelim>);

generate_list_parser!(
    ArgumentList;
    ArgumentListRest;
    ArgumentListState;
    ArgumentListDelim;
    ArgumentListItem);

// TODO: test
fn arguments_list<I: U8Input>(i: ESInput<I>,
                              params: &Parameters)
                              -> ESParseResult<I, ArgumentList> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of arguments_list");
        }
    }

    type Accumulator = Rc<RefCell<ArgumentListState>>;

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
                let delim = ArgumentListDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }


    let mut expr_params = params.clone();
    expr_params.insert(Parameter::In);

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {

        option(i,
               |i| {
                   string(i, b"...")
                       .then(common_delim)
                       .map(|x| Some(x))
               },
               None)
            .bind(|i, delim| assignment_expression(i, &expr_params).map(|x| (delim, x)))
            .bind(|i, (rest_op, assignment_expression)| -> ESParseResult<I, ()> {
                let rhs = if let Some(delim) = rest_op {
                    ArgumentListItem::RestAssignmentExpression(delim, assignment_expression)
                } else {
                    ArgumentListItem::AssignmentExpression(assignment_expression)
                };

                accumulator.borrow_mut().add_item(rhs);
                i.ret(())
            })
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// LeftHandSideExpression

pub enum LeftHandSideExpression {
    NewExpression(NewExpression),
    CallExpression(CallExpression),
}

// TODO: test
pub fn left_hand_side_expression<I: U8Input>(i: ESInput<I>,
                                             params: &Parameters)
                                             -> ESParseResult<I, LeftHandSideExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of left_hand_side_expression");
        }
    }

    or(i,
       |i| new_expression(i, &params).map(LeftHandSideExpression::NewExpression),
       |i| call_expression(i, &params).map(LeftHandSideExpression::CallExpression))
}


// 12.4 Update Expressions

// UpdateExpression

enum UpdateExpression {
    LeftHandSideExpression(LeftHandSideExpression),
    PostIncrement(LeftHandSideExpression,
                  /* ++ */
                  Vec<CommonDelim>),
    PostDecrement(LeftHandSideExpression,
                  /* -- */
                  Vec<CommonDelim>),
    PreIncrement(Vec<CommonDelim>,
                 /* ++ */
                 UnaryExpression),
    PreDecrement(Vec<CommonDelim>,
                 /* -- */
                 UnaryExpression),
}

// TODO: test
fn update_expression<I: U8Input>(i: ESInput<I>,
                                 params: &Parameters)
                                 -> ESParseResult<I, UpdateExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of update_expression");
        }
    }

    enum PreOperator {
        PreIncrement,
        PreDecrement,
    }

    enum PostOperator {
        PostIncrement(Vec<CommonDelim>),
        PostDecrement(Vec<CommonDelim>),
        None,
    }

    or(i,
       |i| {
        parse!{i;

                let operator = (i -> string(i, b"++").map(|_| PreOperator::PreIncrement)) <|>
                    (i -> string(i, b"--").map(|_| PreOperator::PreDecrement));

                let delim = common_delim();

                let unary_expr = unary_expression(&params);

                ret {
                    match operator {
                        PreOperator::PreIncrement => UpdateExpression::PreIncrement(delim, unary_expr),
                        PreOperator::PreDecrement => UpdateExpression::PreDecrement(delim, unary_expr),
                    }
                }
            }
    },
       |i| {
        parse!{i;

                let lhs_expr = left_hand_side_expression(&params);

                let operator = (i -> {
                    // TODO: test this case
                    common_delim_no_line_term(i)
                        .bind(|i, delim| {
                            string(i, b"++")
                                .map(|_| PostOperator::PostIncrement(delim))
                        })
                }) <|>
                (i -> {
                    // TODO: test this case
                    common_delim_no_line_term(i)
                        .bind(|i, delim| {
                            string(i, b"--")
                                .map(|_| PostOperator::PostDecrement(delim))
                        })
                }) <|>
                (i -> i.ret(PostOperator::None));

                ret {
                    match operator {
                        PostOperator::PostIncrement(delim) => UpdateExpression::PostIncrement(lhs_expr, delim),
                        PostOperator::PostDecrement(delim) => UpdateExpression::PostDecrement(lhs_expr, delim),
                        PostOperator::None => UpdateExpression::LeftHandSideExpression(lhs_expr),
                    }
                }
            }
    })
}

// 12.5 Unary Operator

// UnaryExpression

enum UnaryExpression {
    UpdateExpression(Box<UpdateExpression>),
    Delete(Vec<CommonDelim>, Box<UnaryExpression>),
    Void(Vec<CommonDelim>, Box<UnaryExpression>),
    TypeOf(Vec<CommonDelim>, Box<UnaryExpression>),
    Plus(Vec<CommonDelim>, Box<UnaryExpression>),
    Minus(Vec<CommonDelim>, Box<UnaryExpression>),
    Tilde(Vec<CommonDelim>, Box<UnaryExpression>),
    ExclamationMark(Vec<CommonDelim>, Box<UnaryExpression>),
}

// TODO: test
fn unary_expression<I: U8Input>(i: ESInput<I>,
                                params: &Parameters)
                                -> ESParseResult<I, UnaryExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of unary_expression");
        }
    }

    enum UnaryExpressionOperator {
        Delete, // delete
        Void, // void
        TypeOf, // typeof
        Plus, // +
        Minus, // -
        Tilde, // ~
        ExclamationMark, // !
    }

    or(i,
       |i| {
        parse!{i;

                let operator = (i -> string(i, b"delete").map(|_| UnaryExpressionOperator::Delete)) <|>
                    (i -> string(i, b"void").map(|_| UnaryExpressionOperator::Void)) <|>
                    (i -> string(i, b"typeof").map(|_| UnaryExpressionOperator::TypeOf)) <|>
                    (i -> string(i, b"+").map(|_| UnaryExpressionOperator::Plus)) <|>
                    (i -> string(i, b"-").map(|_| UnaryExpressionOperator::Minus)) <|>
                    (i -> string(i, b"~").map(|_| UnaryExpressionOperator::Tilde)) <|>
                    (i -> string(i, b"!").map(|_| UnaryExpressionOperator::ExclamationMark));

                let delim = common_delim();

                let unary_expr = unary_expression(&params);

                ret {

                    let unary_expr = Box::new(unary_expr);

                    match operator {
                        UnaryExpressionOperator::Delete => UnaryExpression::Delete(delim, unary_expr),
                        UnaryExpressionOperator::Void => UnaryExpression::Void(delim, unary_expr),
                        UnaryExpressionOperator::TypeOf => UnaryExpression::TypeOf(delim, unary_expr),
                        UnaryExpressionOperator::Plus => UnaryExpression::Plus(delim, unary_expr),
                        UnaryExpressionOperator::Minus => UnaryExpression::Minus(delim, unary_expr),
                        UnaryExpressionOperator::Tilde => UnaryExpression::Tilde(delim, unary_expr),
                        UnaryExpressionOperator::ExclamationMark => UnaryExpression::ExclamationMark(delim, unary_expr),
                    }
                }
            }
    },
       |i| update_expression(i, &params).map(|x| UnaryExpression::UpdateExpression(Box::new(x))))
}

// 12.6 Exponentiation Operator

// ExponentiationExpression

enum ExponentiationExpression {
    UnaryExpression(UnaryExpression),
    UpdateExpression(UpdateExpression,
                     Vec<CommonDelim>,
                     Vec<CommonDelim>,
                     Box<ExponentiationExpression>),
}

// TODO: test
fn exponentiation_expression<I: U8Input>(i: ESInput<I>,
                                         params: &Parameters)
                                         -> ESParseResult<I, ExponentiationExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of exponentiation_expression");
        }
    }

    or(i,
       |i| unary_expression(i, &params).map(|x| ExponentiationExpression::UnaryExpression(x)),
       |i| {
        parse!{i;

                let update_expr = update_expression(&params);

                let delim_1 = common_delim();

                string(b"**");

                let delim_2 = common_delim();

                let exp_expr = exponentiation_expression(&params);

                ret {
                    ExponentiationExpression::UpdateExpression(update_expr, delim_1, delim_2, Box::new(exp_expr))
                }
            }
    })
}

// 12.7 Multiplicative Operators

// MultiplicativeExpression

struct MultiplicativeExpression(ExponentiationExpression, Vec<MultiplicativeExpressionRest>);

impl MultiplicativeExpression {
    fn new(rhs_val: ExponentiationExpression) -> Self {
        MultiplicativeExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: MultiplicativeExpressionDelim,
                rhs_val: ExponentiationExpression)
                -> Self {

        let MultiplicativeExpression(head, rest) = self;
        let mut rest = rest;

        let MultiplicativeExpressionDelim(delim_1, operator, delim_2) = operator_delim;

        let rhs = MultiplicativeExpressionRest(delim_1, operator, delim_2, rhs_val);

        rest.push(rhs);

        MultiplicativeExpression(head, rest)
    }
}

struct MultiplicativeExpressionRest(Vec<CommonDelim>,
                                    MultiplicativeOperator,
                                    Vec<CommonDelim>,
                                    ExponentiationExpression);

struct MultiplicativeExpressionDelim(Vec<CommonDelim>, MultiplicativeOperator, Vec<CommonDelim>);

generate_list_parser!(
    MultiplicativeExpression;
    MultiplicativeExpressionRest;
    MultiplicativeExpressionState;
    MultiplicativeExpressionDelim;
    ExponentiationExpression);

// TODO: test
fn multiplicative_expression<I: U8Input>(i: ESInput<I>,
                                         params: &Parameters)
                                         -> ESParseResult<I, MultiplicativeExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of multiplicative_expression");
        }
    }

    type Accumulator = Rc<RefCell<MultiplicativeExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            let multiplicative_operator = (i -> {
                on_error(multiplicative_operator(i),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected one of these operators: *, /, or %.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();
            ret {
                let delim = MultiplicativeExpressionDelim(delim_1, multiplicative_operator, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = exponentiation_expression(&params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// MultiplicativeOperator

enum MultiplicativeOperator {
    Multiplication, // *
    Division, // /
    Remainder, // %
}

// TODO: test
#[inline]
fn multiplicative_operator<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, MultiplicativeOperator> {
    parse!{i;

        let operator = (i -> string(i, b"*").map(|_| MultiplicativeOperator::Multiplication)) <|>
            (i -> string(i, b"/").map(|_| MultiplicativeOperator::Division)) <|>
            (i -> string(i, b"%").map(|_| MultiplicativeOperator::Remainder));

        ret operator
    }
}

// 12.8 Additive Operators

// AdditiveExpression

struct AdditiveExpression(MultiplicativeExpression, Vec<AdditiveExpressionRest>);

impl AdditiveExpression {
    fn new(rhs_val: MultiplicativeExpression) -> Self {
        AdditiveExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: AdditiveExpressionDelim,
                rhs_val: MultiplicativeExpression)
                -> Self {

        let AdditiveExpression(head, rest) = self;
        let mut rest = rest;

        let AdditiveExpressionDelim(delim_1, operator, delim_2) = operator_delim;

        let rhs = AdditiveExpressionRest(delim_1, operator, delim_2, rhs_val);

        rest.push(rhs);

        AdditiveExpression(head, rest)
    }
}

struct AdditiveExpressionRest(Vec<CommonDelim>,
                              AdditiveExpressionOperator,
                              Vec<CommonDelim>,
                              MultiplicativeExpression);

enum AdditiveExpressionOperator {
    Add,
    Subtract,
}

struct AdditiveExpressionDelim(Vec<CommonDelim>, AdditiveExpressionOperator, Vec<CommonDelim>);

generate_list_parser!(
    AdditiveExpression;
    AdditiveExpressionRest;
    AdditiveExpressionState;
    AdditiveExpressionDelim;
    MultiplicativeExpression);

// TODO: test
fn additive_expression<I: U8Input>(i: ESInput<I>,
                                   params: &Parameters)
                                   -> ESParseResult<I, AdditiveExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of additive_expression");
        }
    }

    type Accumulator = Rc<RefCell<AdditiveExpressionState>>;

    #[inline]
    fn additive_operator<I: U8Input>(i: ESInput<I>)
                                     -> ESParseResult<I, AdditiveExpressionOperator> {
        parse!{i;

            let operator = (i -> string(i, b"+").map(|_| AdditiveExpressionOperator::Add)) <|>
                (i -> string(i, b"-").map(|_| AdditiveExpressionOperator::Subtract));

            ret operator
        }
    }

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            let additive_operator = (i -> {
                on_error(additive_operator(i),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected one of these operators: +, or -.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();
            ret {
                let delim = AdditiveExpressionDelim(delim_1, additive_operator, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = multiplicative_expression(&params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// 12.9 Bitwise Shift Operators

// ShiftExpression

struct ShiftExpression(AdditiveExpression, Vec<ShiftExpressionRest>);

impl ShiftExpression {
    fn new(rhs_val: AdditiveExpression) -> Self {
        ShiftExpression(rhs_val, vec![])
    }

    fn add_item(self, operator_delim: ShiftExpressionDelim, rhs_val: AdditiveExpression) -> Self {

        let ShiftExpression(head, rest) = self;
        let mut rest = rest;

        let ShiftExpressionDelim(delim_1, operator, delim_2) = operator_delim;

        let rhs = ShiftExpressionRest(delim_1, operator, delim_2, rhs_val);

        rest.push(rhs);

        ShiftExpression(head, rest)
    }
}

struct ShiftExpressionRest(Vec<CommonDelim>,
                           ShiftExpressionOperator,
                           Vec<CommonDelim>,
                           AdditiveExpression);

enum ShiftExpressionOperator {
    // TODO: better semantic names
    Left, // <<
    SignRight, // >>
    Right, // >>>
}

struct ShiftExpressionDelim(Vec<CommonDelim>, ShiftExpressionOperator, Vec<CommonDelim>);

generate_list_parser!(
    ShiftExpression;
    ShiftExpressionRest;
    ShiftExpressionState;
    ShiftExpressionDelim;
    AdditiveExpression);

// TODO: test
fn shift_expression<I: U8Input>(i: ESInput<I>,
                                params: &Parameters)
                                -> ESParseResult<I, ShiftExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::Yield)) {
            panic!("misuse of shift_expression");
        }
    }

    type Accumulator = Rc<RefCell<ShiftExpressionState>>;

    #[inline]
    fn bitwise_operator<I: U8Input>(i: ESInput<I>) -> ESParseResult<I, ShiftExpressionOperator> {
        parse!{i;

            let operator = (i -> string(i, b"<<").map(|_| ShiftExpressionOperator::Left)) <|>
                (i -> string(i, b">>>").map(|_| ShiftExpressionOperator::Right)) <|>
                (i -> string(i, b">>").map(|_| ShiftExpressionOperator::SignRight));

            ret operator
        }
    }

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            let bitwise_operator = (i -> {
                on_error(bitwise_operator(i),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected one of these operators: <<, >>, or >>>.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();
            ret {
                let delim = ShiftExpressionDelim(delim_1, bitwise_operator, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = additive_expression(&params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// 12.10 Relational Operators

// RelationalExpression

struct RelationalExpression(ShiftExpression, Vec<RelationalExpressionRest>);

impl RelationalExpression {
    fn new(rhs_val: ShiftExpression) -> Self {
        RelationalExpression(rhs_val, vec![])
    }

    fn add_item(self, operator_delim: RelationalExpressionDelim, rhs_val: ShiftExpression) -> Self {

        let RelationalExpression(head, rest) = self;
        let mut rest = rest;

        let RelationalExpressionDelim(delim_1, operator, delim_2) = operator_delim;

        let rhs = RelationalExpressionRest(delim_1, operator, delim_2, rhs_val);

        rest.push(rhs);

        RelationalExpression(head, rest)
    }
}

struct RelationalExpressionRest(Vec<CommonDelim>,
                                RelationalExpressionOperator,
                                Vec<CommonDelim>,
                                ShiftExpression);

enum RelationalExpressionOperator {
    Less,
    Greater,
    LessOrEqual,
    GreaterOrEqual,
    InstanceOf,
    In,
}

struct RelationalExpressionDelim(Vec<CommonDelim>, RelationalExpressionOperator, Vec<CommonDelim>);

generate_list_parser!(
    RelationalExpression;
    RelationalExpressionRest;
    RelationalExpressionState;
    RelationalExpressionDelim;
    ShiftExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-RelationalExpression
fn relational_expression<I: U8Input>(i: ESInput<I>,
                                     params: &Parameters)
                                     -> ESParseResult<I, RelationalExpression> {

    ensure_params!(params; "relational_expression"; Parameter::In; Parameter::Yield);

    let has_in = params.contains(&Parameter::In);

    let shift_params = {
        let mut params = Parameters::new();
        if params.contains(&Parameter::Yield) {
            params.insert(Parameter::Yield);
        }
        params
    };

    type Accumulator = Rc<RefCell<RelationalExpressionState>>;

    #[inline]
    fn relational_operator<I: U8Input>(i: ESInput<I>,
                                       has_in: bool)
                                       -> ESParseResult<I, RelationalExpressionOperator> {
        parse!{i;

            let operator = (i -> string(i, b"<=").map(|_| RelationalExpressionOperator::LessOrEqual)) <|>
                (i -> string(i, b">=").map(|_| RelationalExpressionOperator::GreaterOrEqual)) <|>
                (i -> string(i, b"instanceof").map(|_| RelationalExpressionOperator::GreaterOrEqual)) <|>
                (i -> {
                    if has_in {
                        string(i, b"in").map(|_| RelationalExpressionOperator::In)
                    } else {
                        i.err({
                            // TODO: reason
                            ESParseError::Failure(ErrorChain::new(""))
                        })
                    }
                }) <|>
                (i -> string(i, b">").map(|_| RelationalExpressionOperator::Greater)) <|>
                (i -> string(i, b"<").map(|_| RelationalExpressionOperator::Less));

            ret operator
        }
    };

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>,
                             accumulator: Accumulator,
                             has_in: bool)
                             -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            let relational_operator = (i -> {
                on_error(relational_operator(i, has_in),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected one of these operators: <, >, <=, >=, instanceof, or in.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();
            ret {
                let delim = RelationalExpressionDelim(delim_1, relational_operator, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = shift_expression(&shift_params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, |i, acc| delimiter(i, acc, has_in), reducer).map(|x| x.unwrap())
}

// 12.11 Equality Operators

// EqualityExpression

struct EqualityExpression(RelationalExpression, Vec<EqualityExpressionRest>);

impl EqualityExpression {
    fn new(rhs_val: RelationalExpression) -> Self {
        EqualityExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: EqualityExpressionDelim,
                rhs_val: RelationalExpression)
                -> Self {

        let EqualityExpression(head, rest) = self;
        let mut rest = rest;

        let EqualityExpressionDelim(delim_1, operator, delim_2) = operator_delim;

        let rhs = EqualityExpressionRest(delim_1, operator, delim_2, rhs_val);

        rest.push(rhs);

        EqualityExpression(head, rest)
    }
}

struct EqualityExpressionRest(Vec<CommonDelim>,
                              EqualityExpressionOperator,
                              Vec<CommonDelim>,
                              RelationalExpression);

enum EqualityExpressionOperator {
    Equality,
    Inequality,
    StrictEquality,
    StrictInequality,
}

struct EqualityExpressionDelim(Vec<CommonDelim>, EqualityExpressionOperator, Vec<CommonDelim>);

generate_list_parser!(
    EqualityExpression;
    EqualityExpressionRest;
    EqualityExpressionState;
    EqualityExpressionDelim;
    RelationalExpression);

// TODO: test
fn equality_expression<I: U8Input>(i: ESInput<I>,
                                   params: &Parameters)
                                   -> ESParseResult<I, EqualityExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::In) ||
             params.contains(&Parameter::Yield)) {
            panic!("misuse of equality_expression");
        }
    }

    type Accumulator = Rc<RefCell<EqualityExpressionState>>;

    #[inline]
    fn equality_operator<I: U8Input>(i: ESInput<I>)
                                     -> ESParseResult<I, EqualityExpressionOperator> {
        parse!{i;

            let operator = (i -> string(i, b"===").map(|_| EqualityExpressionOperator::StrictEquality)) <|>
            (i -> string(i, b"==").map(|_| EqualityExpressionOperator::Equality)) <|>
            (i -> string(i, b"!==").map(|_| EqualityExpressionOperator::StrictInequality)) <|>
            (i -> string(i, b"!=").map(|_| EqualityExpressionOperator::Inequality));

            ret operator
        }
    }

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            let equality_operator = (i -> {
                on_error(
                    equality_operator(i),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected one of these operators: ==, ===, !==, or !=.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();
            ret {
                let delim = EqualityExpressionDelim(delim_1, equality_operator, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = relational_expression(params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// 12.12 Binary Bitwise Operators

// BitwiseANDExpression

// BitwiseANDExpression := EqualityExpression BitwiseANDExpressionRest*
// BitwiseANDExpressionRest := Delim ^ Delim EqualityExpression

struct BitwiseANDExpression(EqualityExpression, Vec<BitwiseANDExpressionRest>);

impl BitwiseANDExpression {
    fn new(rhs_val: EqualityExpression) -> Self {
        BitwiseANDExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: BitwiseANDExpressionDelim,
                rhs_val: EqualityExpression)
                -> Self {

        let BitwiseANDExpression(head, rest) = self;
        let mut rest = rest;

        let BitwiseANDExpressionDelim(delim_1, delim_2) = operator_delim;

        let rhs = BitwiseANDExpressionRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        BitwiseANDExpression(head, rest)
    }
}

struct BitwiseANDExpressionRest(Vec<CommonDelim>, Vec<CommonDelim>, EqualityExpression);

struct BitwiseANDExpressionDelim(Vec<CommonDelim>, Vec<CommonDelim>);

generate_list_parser!(
    BitwiseANDExpression;
    BitwiseANDExpressionRest;
    BitwiseANDExpressionState;
    BitwiseANDExpressionDelim;
    EqualityExpression);

// TODO: test
fn bitwise_and_expression<I: U8Input>(i: ESInput<I>,
                                      params: &Parameters)
                                      -> ESParseResult<I, BitwiseANDExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::In) ||
             params.contains(&Parameter::Yield)) {
            panic!("misuse of bitwise_and_expression");
        }
    }

    type Accumulator = Rc<RefCell<BitwiseANDExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;
            let delim_1 = common_delim();

            (i -> {
                on_error(string(i, b"&"),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected & operator.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();
            ret {

                let delim = BitwiseANDExpressionDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = equality_expression(params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// BitwiseXORExpression

// BitwiseXORExpression := BitwiseANDExpression BitwiseXORExpressionRest*
// BitwiseXORExpressionRest := Delim ^ Delim BitwiseANDExpression

struct BitwiseXORExpression(BitwiseANDExpression, Vec<BitwiseXORExpressionRest>);

impl BitwiseXORExpression {
    fn new(rhs_val: BitwiseANDExpression) -> Self {
        BitwiseXORExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: BitwiseXORExpressionDelim,
                rhs_val: BitwiseANDExpression)
                -> Self {

        let BitwiseXORExpression(head, rest) = self;
        let mut rest = rest;

        let BitwiseXORExpressionDelim(delim_1, delim_2) = operator_delim;

        let rhs = BitwiseXORExpressionRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        BitwiseXORExpression(head, rest)
    }
}

struct BitwiseXORExpressionRest(Vec<CommonDelim>, Vec<CommonDelim>, BitwiseANDExpression);

struct BitwiseXORExpressionDelim(Vec<CommonDelim>, Vec<CommonDelim>);

generate_list_parser!(
    BitwiseXORExpression;
    BitwiseXORExpressionRest;
    BitwiseXORExpressionState;
    BitwiseXORExpressionDelim;
    BitwiseANDExpression);

// TODO: test
fn bitwise_xor_expression<I: U8Input>(i: ESInput<I>,
                                      params: &Parameters)
                                      -> ESParseResult<I, BitwiseXORExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::In) ||
             params.contains(&Parameter::Yield)) {
            panic!("misuse of bitwise_xor_expression");
        }
    }

    type Accumulator = Rc<RefCell<BitwiseXORExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;

            let delim_1 = common_delim();

            (i -> {
                on_error(string(i, b"^"),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected ^ operator.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();

            ret {
                let delim = BitwiseXORExpressionDelim(delim_1, delim_2);
                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = bitwise_and_expression(params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())

}

// BitwiseORExpression

// BitwiseORExpression := BitwiseXORExpression BitwiseORExpressionRest*
// BitwiseORExpressionRest := Delim | Delim BitwiseXORExpression

struct BitwiseORExpression(BitwiseXORExpression, Vec<BitwiseORExpressionRest>);

impl BitwiseORExpression {
    fn new(rhs_val: BitwiseXORExpression) -> Self {
        BitwiseORExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: BitwiseORExpressionDelim,
                rhs_val: BitwiseXORExpression)
                -> Self {

        let BitwiseORExpression(head, rest) = self;
        let mut rest = rest;

        let BitwiseORExpressionDelim(delim_1, delim_2) = operator_delim;

        let rhs = BitwiseORExpressionRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        BitwiseORExpression(head, rest)
    }
}

struct BitwiseORExpressionRest(Vec<CommonDelim>, Vec<CommonDelim>, BitwiseXORExpression);

struct BitwiseORExpressionDelim(Vec<CommonDelim>, Vec<CommonDelim>);

generate_list_parser!(
    BitwiseORExpression;
    BitwiseORExpressionRest;
    BitwiseORExpressionState;
    BitwiseORExpressionDelim;
    BitwiseXORExpression);

// TODO: test
fn bitwise_or_expression<I: U8Input>(i: ESInput<I>,
                                     params: &Parameters)
                                     -> ESParseResult<I, BitwiseORExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::In) ||
             params.contains(&Parameter::Yield)) {
            panic!("misuse of bitwise_or_expression");
        }
    }

    type Accumulator = Rc<RefCell<BitwiseORExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;
            let delim_1 = common_delim();

            (i -> {
                on_error(string(i, b"|"),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected | operator.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();
            ret {
                let delim = BitwiseORExpressionDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = bitwise_xor_expression(params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}

// 12.13 Binary Logical Operators

// LogicalANDExpression

// LogicalAndExpression := BitwiseORExpression LogicalAndExpressionRest*
// LogicalAndExpressionRest := Delim && Delim BitwiseORExpression

struct LogicalAndExpression(BitwiseORExpression, Vec<LogicalAndExpressionRest>);

impl LogicalAndExpression {
    fn new(rhs_val: BitwiseORExpression) -> Self {
        LogicalAndExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: LogicalAndExpressionDelim,
                rhs_val: BitwiseORExpression)
                -> Self {

        let LogicalAndExpression(head, rest) = self;
        let mut rest = rest;

        let LogicalAndExpressionDelim(delim_1, delim_2) = operator_delim;

        let rhs = LogicalAndExpressionRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        LogicalAndExpression(head, rest)
    }
}

struct LogicalAndExpressionRest(Vec<CommonDelim>, Vec<CommonDelim>, BitwiseORExpression);

struct LogicalAndExpressionDelim(Vec<CommonDelim>, Vec<CommonDelim>);

generate_list_parser!(
    LogicalAndExpression;
    LogicalAndExpressionRest;
    LogicalAndExpressionState;
    LogicalAndExpressionDelim;
    BitwiseORExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-LogicalANDExpression
fn logical_and_expression<I: U8Input>(i: ESInput<I>,
                                      params: &Parameters)
                                      -> ESParseResult<I, LogicalAndExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::In) ||
             params.contains(&Parameter::Yield)) {
            panic!("misuse of logical_and_expression");
        }
    }

    type Accumulator = Rc<RefCell<LogicalAndExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;
            let delim_1 = common_delim();

            (i -> {
                on_error(string(i, b"&&"),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected && operator.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();
            ret {
                let delim = LogicalAndExpressionDelim(delim_1, delim_2);
                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = bitwise_or_expression(params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())

}

// LogicOrExpression

// LogicOrExpression := LogicalAndExpression LogicOrExpressionRest*
// LogicOrExpressionRest := Delim || Delim LogicalAndExpression

struct LogicOrExpression(LogicalAndExpression, Vec<LogicOrExpressionRest>);

impl LogicOrExpression {
    fn new(rhs_val: LogicalAndExpression) -> Self {
        LogicOrExpression(rhs_val, vec![])
    }

    fn add_item(self,
                operator_delim: LogicOrExpressionDelim,
                rhs_val: LogicalAndExpression)
                -> Self {

        let LogicOrExpression(head, rest) = self;
        let mut rest = rest;

        let LogicOrExpressionDelim(delim_1, delim_2) = operator_delim;

        let rhs = LogicOrExpressionRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        LogicOrExpression(head, rest)
    }
}

struct LogicOrExpressionRest(Vec<CommonDelim>, Vec<CommonDelim>, LogicalAndExpression);

struct LogicOrExpressionDelim(Vec<CommonDelim>, Vec<CommonDelim>);

generate_list_parser!(
    LogicOrExpression;
    LogicOrExpressionRest;
    LogicOrExpressionState;
    LogicOrExpressionDelim;
    LogicalAndExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Parameters
fn logical_or_expression<I: U8Input>(i: ESInput<I>,
                                     params: &Parameters)
                                     -> ESParseResult<I, LogicOrExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::In) ||
             params.contains(&Parameter::Yield)) {
            panic!("misuse of logical_or_expression");
        }
    }

    type Accumulator = Rc<RefCell<LogicOrExpressionState>>;

    #[inline]
    fn delimiter<I: U8Input>(i: ESInput<I>, accumulator: Accumulator) -> ESParseResult<I, ()> {
        parse!{i;
            let delim_1 = common_delim();

            (i -> {
                on_error(string(i, b"||"),
                    |i| {
                        let loc = i.position();
                        ErrorLocation::new(loc, "Expected || operator.".to_string())
                    }
                )
            });

            let delim_2 = common_delim();
            ret {

                let delim = LogicOrExpressionDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    #[inline]
    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;
            let rhs = logical_and_expression(params);
            ret {
                accumulator.borrow_mut().add_item(rhs);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}


// 12.14 Conditional Operator ( ? : )

// ConditionalExpression

enum ConditionalExpression {
    Conditional(LogicOrExpression,
                Vec<CommonDelim>,
                Vec<CommonDelim>,
                AssignmentExpression,
                Vec<CommonDelim>,
                Vec<CommonDelim>,
                AssignmentExpression),
    LogicOrExpression(LogicOrExpression),
}


// TODO: test
fn conditional_expression<I: U8Input>(i: ESInput<I>,
                                      params: &Parameters)
                                      -> ESParseResult<I, ConditionalExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::In) ||
             params.contains(&Parameter::Yield)) {
            panic!("misuse of conditional_expression");
        }
    }

    #[inline]
    fn conditional<I: U8Input>(i: ESInput<I>,
                               params: &Parameters)
                               -> ESParseResult<I,
                                                (Vec<CommonDelim>,
                                                 Vec<CommonDelim>,
                                                 AssignmentExpression,
                                                 Vec<CommonDelim>,
                                                 Vec<CommonDelim>,
                                                 AssignmentExpression)> {

        parse!{i;

            let delim_1 = common_delim();
            token(b'?');
            let delim_2 = common_delim();

            let consequent = (i -> {
                let mut params = params.clone();
                params.insert(Parameter::In);
                assignment_expression(i, &params)
            });

            let delim_3 = common_delim();
            token(b':');
            let delim_4 = common_delim();

            let alternative = assignment_expression(&params);

            ret {
                (delim_1, delim_2, consequent, delim_3, delim_4, alternative)
            }
        }
    }

    parse!{i;

        let logical_or_expression = logical_or_expression(&params);

        let conditional = option(|i| conditional(i, &params).map(Some),
            None);

        ret {
            match conditional {
                Some((delim_1, delim_2, consequent, delim_3, delim_4, alternative)) => {
                    ConditionalExpression::Conditional(
                        logical_or_expression, delim_1, delim_2, consequent, delim_3, delim_4, alternative)
                }
                None => {
                    ConditionalExpression::LogicOrExpression(logical_or_expression)
                }
            }
        }
    }
}

// 12.15 Assignment Operators

// AssignmentExpression

pub enum AssignmentExpression {
    ConditionalExpression(Box<ConditionalExpression>), // TODO: complete
}

// TODO: test
pub fn assignment_expression<I: U8Input>(i: ESInput<I>,
                                         params: &Parameters)
                                         -> ESParseResult<I, AssignmentExpression> {

    if is_debug_mode!() {
        // validation
        if !(params.is_empty() || params.contains(&Parameter::In) ||
             params.contains(&Parameter::Yield)) {
            panic!("misuse of assignment_expression");
        }
    }

    parse!{i;

        let result = (i -> conditional_expression(i, params)
            .map(|x| AssignmentExpression::ConditionalExpression(Box::new(x))));

        // TODO: complete

        ret {
            result
        }
    }
}

// 12.16 Comma Operator ( , )

// Expression

pub struct Expression(AssignmentExpression, Vec<ExpressionRest>);

impl Expression {
    fn new(rhs_val: AssignmentExpression) -> Self {
        Expression(rhs_val, vec![])
    }

    fn add_item(self, operator_delim: ExpressionDelim, rhs_val: AssignmentExpression) -> Self {

        let Expression(head, rest) = self;
        let mut rest = rest;

        let ExpressionDelim(delim_1, delim_2) = operator_delim;

        let rhs = ExpressionRest(delim_1, delim_2, rhs_val);

        rest.push(rhs);

        Expression(head, rest)
    }
}

struct ExpressionRest(Vec<CommonDelim>,
                      /* , (comma) */
                      Vec<CommonDelim>,
                      AssignmentExpression);

struct ExpressionDelim(Vec<CommonDelim>,
                       /* , (comma) */
                       Vec<CommonDelim>);

generate_list_parser!(
    Expression;
    ExpressionRest;
    ExpressionState;
    ExpressionDelim;
    AssignmentExpression);

// TODO: test
// http://www.ecma-international.org/ecma-262/7.0/#prod-Expression
pub fn expression<I: U8Input>(i: ESInput<I>, params: &Parameters) -> ESParseResult<I, Expression> {

    if is_debug_mode!() {
        if !(params.is_empty() || params.contains(&Parameter::Yield) ||
             params.contains(&Parameter::In)) {
            panic!("misuse of expression");
        }
    }

    type Accumulator = Rc<RefCell<ExpressionState>>;

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
                let delim = ExpressionDelim(delim_1, delim_2);

                accumulator.borrow_mut().add_delim(delim);
                ()
            }
        }
    }

    let reducer = |i: ESInput<I>, accumulator: Accumulator| -> ESParseResult<I, ()> {
        parse!{i;

            let item = assignment_expression(&params);

            ret {
                accumulator.borrow_mut().add_item(item);
                ()
            }
        }
    };

    parse_list(i, delimiter, reducer).map(|x| x.unwrap())
}
