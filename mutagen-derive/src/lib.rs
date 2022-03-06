extern crate proc_macro;

use std::{borrow::Cow, collections::HashMap};

use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{format_ident, quote, ToTokens};
use syn::{
    bracketed, parenthesized,
    parse::{Parse, ParseStream},
    parse2, parse_macro_input,
    punctuated::Punctuated,
    spanned::Spanned,
    token::{Bracket, Paren},
    Attribute, Data, DataEnum, DataStruct, Error, ExprClosure, Field, Fields, Ident, LitFloat,
    Result, Token, Type,
};

mod a {
    // Base path in the attribute
    pub const BASE: &str = "mutagen";

    // Keys
    pub const GEN_WEIGHT: &str = "gen_weight";
    pub const GEN_ARG: &str = "gen_arg";
    pub const GEN_PREFERRED: &str = "gen_preferred";
    pub const MUT_REROLL: &str = "mut_reroll";
    pub const MUT_ARG: &str = "mut_arg";
    pub const MUT_WEIGHT: &str = "mut_weight";
    pub const SKIP: &str = "skip";

    // Allowed keys for each item
    pub const ENUM: &[&str] = &[MUT_REROLL, MUT_ARG, GEN_ARG];
    pub const ENUM_VARIANT: &[&str] = &[GEN_WEIGHT, GEN_PREFERRED, MUT_REROLL];
    pub const FIELD: &[&str] = &[MUT_WEIGHT, SKIP];
    pub const TYPE: &[&str] = &[MUT_REROLL, MUT_ARG, GEN_ARG];
}

#[proc_macro_derive(Generatable, attributes(mutagen))]
pub fn derive_generatable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as syn::DeriveInput);
    let output = generatable_type(input).unwrap_or_else(|e| e.to_compile_error());
    proc_macro::TokenStream::from(output)
}

fn generatable_type(input: syn::DeriveInput) -> Result<TokenStream2> {
    let span = input.span();

    let gen_arg = parse_attrs(&input.attrs, a::TYPE)?
        .get(a::GEN_ARG)
        .cloned()
        .ok_or_else(|| Error::new(span, "Missing gen_arg attribute"))?
        .to_type()?;

    let body = match &input.data {
        Data::Struct(s) => generatable_struct(&input.ident, s, &input.attrs, span)?,
        Data::Enum(e) => generatable_enum(&input.ident, e, &input.attrs, span)?,
        Data::Union(_) => panic!("#[derive(Generatable)] is not yet implemented for unions"),
    };

    let ident = input.ident;

    Ok(quote! {
        #[automatically_derived]
        impl<'a> ::mutagen::Generatable<'a> for #ident {
            type GenArg = #gen_arg;

            fn generate_rng<R: ::mutagen::rand::Rng + ?Sized>(
                rng: &mut R,
                mut arg: Self::GenArg,
            ) -> Self {
                ::mutagen::State::handle_event(&mut arg, ::mutagen::Event { kind: ::mutagen::EventKind::Generate, key: ::std::borrow::Cow::Borrowed(stringify!(#ident)) });
                #body
            }
        }
    })
}

fn generatable_struct(
    ident: &Ident,
    s: &DataStruct,
    _attrs: &[Attribute],
    _span: Span,
) -> Result<TokenStream2> {
    let fields = generatable_fields(&s.fields)?;

    Ok(quote! {
        #ident #fields
    })
}

fn generatable_enum(
    enum_ident: &Ident,
    e: &DataEnum,
    _attrs: &[Attribute],
    span: Span,
) -> Result<TokenStream2> {
    if e.variants.is_empty() {
        return Err(Error::new(
            span,
            &format!(
                "Cannot derive Generatable for enum {}: no variants",
                enum_ident
            ),
        ));
    }

    roll(
        &e.variants.iter().collect::<Vec<_>>(),
        |variant| {
            let attrs = parse_attrs(&variant.attrs, a::ENUM_VARIANT)?;

            let weight = attrs
                .get(a::GEN_WEIGHT)
                .cloned()
                .unwrap_or_else(|| Value::None(span));

            if attrs.contains_key(a::GEN_PREFERRED) {
                let w = weight.to_weight()?.unwrap_or_else(|| quote!(0.0));

                let c: TokenStream2 = quote! {
                    |mut arg: Self::GenArg| {
                        (#w) * 100.0
                    }
                };

                Ok(Value::Closure(parse2(c)?))
            } else {
                Ok(weight)
            }
        },
        |variant, _| {
            let ident = &variant.ident;
            let fields = generatable_fields(&variant.fields)?;
            Ok(quote! {
                {
                    ::mutagen::State::handle_event(&mut arg, ::mutagen::Event { kind: ::mutagen::EventKind::Generate, key: ::std::borrow::Cow::Borrowed(stringify!(#enum_ident::#ident)) });
                    #enum_ident::#ident #fields
                }
            })
        },
        &format!("Generation for {}", enum_ident),
    )
}

fn generatable_fields(fields: &Fields) -> Result<TokenStream2> {
    match fields {
        Fields::Named(f) => {
            let item: Vec<TokenStream2> = f
                .named
                .iter()
                .map(|f| {
                    let name = &f.ident;

                    if parse_attrs(&f.attrs, a::FIELD)?.contains_key(a::SKIP) {
                        Ok(quote! {
                            #name: ::std::default::Default::default()
                        })
                    } else {
                        Ok(quote! {
                            #name: ::mutagen::Generatable::generate_rng(rng, ::mutagen::State::deepened(::std::convert::From::from(::mutagen::Reborrow::reborrow(&mut arg))))
                        })
                    }
                })
                .collect::<Result<_>>()?;

            Ok(quote! {{ #(#item),* }})
        }
        Fields::Unnamed(f) => {
            let item: Vec<TokenStream2> = f
                .unnamed
                .iter()
                .map(|f| {
                    if parse_attrs(&f.attrs, a::FIELD)?.contains_key(a::SKIP) {
                        Ok(quote! {
                            ::std::default::Default::default()
                        })
                    } else {
                        Ok(quote! {
                            ::mutagen::Generatable::generate_rng(rng, ::mutagen::State::deepened(::std::convert::From::from(::mutagen::Reborrow::reborrow(&mut arg))))
                        })
                    }
                })
                .collect::<Result<_>>()?;

            Ok(quote! {( #(#item),* )})
        }
        Fields::Unit => Ok(TokenStream2::new()),
    }
}

#[proc_macro_derive(Mutatable, attributes(mutagen))]
pub fn derive_mutatable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as syn::DeriveInput);
    let output = mutatable_type(input).unwrap_or_else(|e| e.to_compile_error());
    proc_macro::TokenStream::from(output)
}

fn mutatable_type(input: syn::DeriveInput) -> Result<TokenStream2> {
    let span = input.span();

    let mut_arg = parse_attrs(&input.attrs, a::TYPE)?
        .get(a::MUT_ARG)
        .cloned()
        .ok_or_else(|| Error::new(span, "Missing mut_arg attribute"))?
        .to_type()?;

    let body = match &input.data {
        Data::Struct(s) => mutatable_struct(&input.ident, s, &input.attrs, span)?,
        Data::Enum(e) => mutatable_enum(&input.ident, e, &input.attrs, span)?,
        Data::Union(_) => panic!("#[derive(Mutatable)] is not yet implemented for unions"),
    };

    let ident = input.ident;

    Ok(quote! {
        #[automatically_derived]
        impl<'a> ::mutagen::Mutatable<'a> for #ident {
            type MutArg = #mut_arg;

            fn mutate_rng<R: ::mutagen::rand::Rng + ?Sized>(
                &mut self,
                rng: &mut R,
                mut arg: Self::MutArg
            ) {
                ::mutagen::State::handle_event(&mut arg, ::mutagen::Event { kind: ::mutagen::EventKind::Mutate, key: ::std::borrow::Cow::Borrowed(stringify!(#ident)) });
                #body
            }
        }
    })
}

fn mutatable_struct(
    ident: &Ident,
    s: &DataStruct,
    _attrs: &[Attribute],
    _span: Span,
) -> Result<TokenStream2> {
    let bindings = fields_bindings(&s.fields)?;
    let body = mutatable_fields(
        &flatten_fields(&s.fields),
        &ident.to_string(),
        s.fields.span(),
    )?;

    Ok(quote! {
        let #ident #bindings = self;
        #body
    })
}

fn mutatable_enum(
    enum_ident: &Ident,
    e: &DataEnum,
    attrs: &[Attribute],
    span: Span,
) -> Result<TokenStream2> {
    if e.variants.is_empty() {
        panic!("Cannot derive Mutatable for enum with no variants");
    }

    let attrs = parse_attrs(attrs, a::ENUM)?;
    let mut_reroll_enum = attrs
        .get(a::MUT_REROLL)
        .cloned()
        .unwrap_or_else(|| Value::None(span))
        .to_prob()?;

    let variants: Vec<_> = e
        .variants
        .iter()
        .map(|variant| {
            let variant_attrs = parse_attrs(&variant.attrs, a::ENUM_VARIANT)?;
            let mut_reroll = if let Some(v) = variant_attrs.get(a::MUT_REROLL) {
                v.to_prob()?
            } else {
                mut_reroll_enum.clone()
            };

            let ident = &variant.ident;
            let bindings = fields_bindings(&variant.fields)?;
            let fields_body = mutatable_fields(
                &flatten_fields(&variant.fields),
                &format!("{}::{}", &enum_ident, &variant.ident),
                variant.fields.span(),
            )?;

            let out: TokenStream2 = if let Some(mut_reroll) = mut_reroll {
                quote! {
                    #enum_ident::#ident #bindings => {
                        if rng.sample(::rand::distributions::Bernoulli::new(#mut_reroll).unwrap()) {
                            *self = ::mutagen::Generatable::generate_rng(rng, ::std::convert::From::from(::mutagen::Reborrow::reborrow(&mut arg)));
                        } else {
                            #fields_body
                        }
                    }
                }
            } else {
                quote! {
                    #enum_ident::#ident #bindings => {
                        ::mutagen::State::handle_event(&mut arg, ::mutagen::Event { kind: ::mutagen::EventKind::Mutate, key: ::std::borrow::Cow::Borrowed(stringify!(#enum_ident::#ident)) });
                        #fields_body
                    }
                }
            };

            Ok(out)
        })
        .collect::<Result<_>>()?;

    Ok(quote! {
        match self {
            #( #variants )*
        }
    })
}

fn fields_bindings(fields: &Fields) -> Result<TokenStream2> {
    match fields {
        Fields::Named(fields) => {
            let bindings: Vec<TokenStream2> = fields
                .named
                .iter()
                .map(|field| {
                    let ident = &field.ident;
                    if parse_attrs(&field.attrs, a::FIELD)?.contains_key(a::SKIP) {
                        Ok(quote! { #ident: _ })
                    } else {
                        Ok(ident.to_token_stream())
                    }
                })
                .collect::<Result<_>>()?;

            Ok(quote! {
                { #(#bindings),* }
            })
        }

        Fields::Unnamed(fields) => {
            let fields: Vec<TokenStream2> = fields
                .unnamed
                .iter()
                .enumerate()
                .map(|(i, field)| {
                    if parse_attrs(&field.attrs, a::FIELD)?.contains_key(a::SKIP) {
                        Ok(quote!(_))
                    } else {
                        Ok(tuple_field_ident(i).to_token_stream())
                    }
                })
                .collect::<Result<_>>()?;

            Ok(quote! {
                ( #(#fields),* )
            })
        }

        Fields::Unit => Ok(TokenStream2::new()),
    }
}

fn mutatable_fields(fields: &[&Field], path: &str, span: Span) -> Result<TokenStream2> {
    if fields.is_empty() {
        return Ok(TokenStream2::new());
    }

    roll(
        fields,
        |field| {
            let attrs = parse_attrs(&field.attrs, a::FIELD)?;

            Ok(if attrs.contains_key(a::SKIP) {
                Value::Val(0.0)
            } else {
                attrs
                    .get(a::MUT_WEIGHT)
                    .cloned()
                    .unwrap_or_else(|| Value::None(span))
            })
        },
        |field, i| {
            let ident = field_ident(field, i);
            Ok(quote! {
                ::mutagen::Mutatable::mutate_rng(#ident, rng, ::mutagen::State::deepened(::std::convert::From::from(::mutagen::Reborrow::reborrow(&mut arg))));
            })
        },
        &format!("mutation for {}", path),
    )
}

#[proc_macro_derive(UpdatableRecursively, attributes(mutagen))]
pub fn derive_updatable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as syn::DeriveInput);
    let output = updatable_type(input).unwrap_or_else(|e| e.to_compile_error());
    proc_macro::TokenStream::from(output)
}

fn updatable_type(input: syn::DeriveInput) -> Result<TokenStream2> {
    let span = input.span();

    let body = match &input.data {
        Data::Struct(s) => updatable_struct(&input.ident, s, &input.attrs, span)?,
        Data::Enum(e) => updatable_enum(&input.ident, e, &input.attrs, span)?,
        Data::Union(_) => panic!("#[derive(UpdatableRecursively)] is not implemented for unions"),
    };

    let ident = input.ident;

    Ok(quote! {
        #[automatically_derived]
        impl<'a> ::mutagen::UpdatableRecursively<'a> for #ident {
            fn update_recursively(&mut self, mut arg: Self::UpdateArg) {
                ::mutagen::State::handle_event(&mut arg, ::mutagen::Event { kind: ::mutagen::EventKind::Update, key: ::std::borrow::Cow::Borrowed(stringify!(#ident)) });
                #body
                ::mutagen::Updatable::update(self, ::std::convert::From::from(::mutagen::Reborrow::reborrow(&mut arg)));
            }
        }
    })
}

fn updatable_struct(
    ident: &Ident,
    s: &DataStruct,
    _attrs: &[Attribute],
    _span: Span,
) -> Result<TokenStream2> {
    let bindings = fields_bindings(&s.fields)?;
    let body = updatable_fields(
        &flatten_fields(&s.fields),
        &ident.to_string(),
        s.fields.span(),
    )?;

    Ok(quote! {
        let #ident #bindings = self;
        #body
    })
}

fn updatable_enum(
    enum_ident: &Ident,
    e: &DataEnum,
    _attrs: &[Attribute],
    _span: Span,
) -> Result<TokenStream2> {
    if e.variants.is_empty() {
        panic!("Cannot derive Mutatable for enum with no variants");
    }

    let variants: Vec<_> = e
        .variants
        .iter()
        .map(|variant| {
            let ident = &variant.ident;
            let bindings = fields_bindings(&variant.fields)?;
            let fields_body = updatable_fields(
                &flatten_fields(&variant.fields),
                &format!("{}::{}", &enum_ident, &variant.ident),
                variant.fields.span(),
            )?;

            let out: TokenStream2 = quote! {
                #enum_ident::#ident #bindings => {
                    ::mutagen::State::handle_event(&mut arg, ::mutagen::Event { kind: ::mutagen::EventKind::Update, key: ::std::borrow::Cow::Borrowed(stringify!(#enum_ident::#ident)) });
                    #fields_body
                }
            };

            Ok(out)
        })
        .collect::<Result<_>>()?;

    Ok(quote! {
        match self {
            #( #variants )*
        }
    })
}

fn updatable_fields(fields: &[&Field], _path: &str, _span: Span) -> Result<TokenStream2> {
    if fields.is_empty() {
        return Ok(TokenStream2::new());
    }

    Ok(fields
       .iter()
       .enumerate()
       .map(|(i, field)| {
           if parse_attrs(&field.attrs, a::FIELD)?.contains_key(a::SKIP) {
               Ok(TokenStream2::new())
           } else {
               let ident = field_ident(field, i);
               Ok(quote! {
                   ::mutagen::UpdatableRecursively::update_recursively(#ident, ::mutagen::State::deepened(::std::convert::From::from(::mutagen::Reborrow::reborrow(&mut arg))));
               })
           }
       })
       .collect::<Result<_>>()?)
}

fn roll<T, Wf, Bf>(choices: &[T], weight_fn: Wf, body_fn: Bf, err: &str) -> Result<TokenStream2>
where
    Wf: Fn(&T) -> Result<Value>,
    Bf: Fn(&T, usize) -> Result<TokenStream2>,
{
    let n = choices.len();

    if n == 0 {
        panic!("roll was called with 0 choices");
    } else if n == 1 {
        return Ok(body_fn(&choices[0], 0)?);
    }

    let weight_values: Vec<_> = choices.iter().map(weight_fn).collect::<Result<_>>()?;

    let weights_opt: Vec<Option<TokenStream2>> = weight_values
        .iter()
        .map(Value::to_weight)
        .collect::<Result<_>>()?;

    let weights: Vec<TokenStream2> = weights_opt
        .iter()
        .map(|w| w.as_ref().cloned().unwrap_or(quote!(0.0)))
        .collect();

    let cumul_idents: Vec<Ident> = (0..n)
        .map(|i| format_ident!("cumul_weights_{}", i))
        .collect();

    let cumul_sum: TokenStream2 = cumul_idents
        .windows(2)
        .enumerate()
        .map(|(i, w)| {
            let pre = &w[0];
            let ident = &w[1];
            quote! {
                let #ident: f64 = #pre + weights[#i + 1];
            }
        })
        .collect();

    let checks: TokenStream2 = choices
        .iter()
        .zip(weights_opt.iter())
        .enumerate()
        .filter(|(_, (_, weight))| weight.is_some())
        .map(|(i, (choice, _))| {
            let body = body_fn(choice, i)?;
            Ok(quote! { if roll < cumul_weights[#i] { #body } else })
        })
        .collect::<Result<_>>()?;

    Ok(quote! {
        let weights: [f64; #n] = [
            #(#weights),*
        ];

        let cumul_weights_0: f64 = weights[0];
        #cumul_sum

        let cumul_weights: [f64; #n] = [
            #(#cumul_idents),*
        ];


        let total_weight = cumul_weights[#n - 1];
        assert!(total_weight > 0.0, "Failed to roll {}. Total weight was {} (should be > 0).", #err, total_weight);
        let roll: f64 = rng.gen_range(0.0..total_weight);

        #checks

        {
            unreachable!("Failed to roll {}. Rolled {}, total weight is {}", #err, roll, total_weight)
        }
    })
}

fn flatten_fields(fields: &Fields) -> Vec<&Field> {
    match fields {
        Fields::Named(fields) => fields.named.iter().collect(),
        Fields::Unnamed(fields) => fields.unnamed.iter().collect(),
        Fields::Unit => Vec::new(),
    }
}

fn field_ident(field: &Field, i: usize) -> Cow<'_, Ident> {
    if let Some(ident) = field.ident.as_ref() {
        Cow::Borrowed(ident)
    } else {
        Cow::Owned(tuple_field_ident(i))
    }
}

fn tuple_field_ident(i: usize) -> Ident {
    Ident::new(&format!("_{}", i), Span::call_site())
}

struct AttrsData {
    _paren: Paren,
    values: Punctuated<KeyValue, Token![,]>,
}

impl Parse for AttrsData {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        // Remove when fixed https://github.com/rust-lang/rust-clippy/issues/4637
        #[allow(clippy::eval_order_dependence)]
        Ok(Self {
            _paren: parenthesized!(content in input),
            values: content.parse_terminated(KeyValue::parse)?,
        })
    }
}

struct KeyValue {
    key: Ident,
    _eq: Option<Token![=]>,
    value: Value,
}

impl Parse for KeyValue {
    fn parse(input: ParseStream) -> Result<Self> {
        let key: Ident = input.parse()?;
        let _eq: Option<Token![=]> = input.parse()?;

        let value: Value = if _eq.is_some() {
            input.parse()?
        } else {
            Value::None(key.span())
        };

        Ok(Self { key, _eq, value })
    }
}

#[derive(Clone)]
enum Value {
    Lit(LitFloat),
    FnIdent(Ident),
    Values(Values),
    Closure(ExprClosure),
    Val(f64),
    Type(Type),
    None(Span),
}

impl Value {
    fn to_type(&self) -> Result<TokenStream2> {
        match self {
            Value::Lit(lit) => Err(Error::new(lit.span(), "Expected type, found literal")),
            Value::FnIdent(ident) => Err(Error::new(ident.span(), "Expected type, found ident")),
            Value::Values(values) => Err(Error::new_spanned(values, "Expected type, found array")),
            Value::Closure(c) => Err(Error::new(c.span(), "Expected type, found closure")),
            Value::Val(_) => panic!("Internal error: expected type, found value"),
            Value::Type(t) => Ok(quote!(#t)),
            Value::None(span) => Err(Error::new(*span, "Expected type, found nothing")),
        }
    }

    fn to_weight(&self) -> Result<Option<TokenStream2>> {
        match self {
            Value::Lit(lit) => {
                let v: f64 = lit.base10_parse()?;

                if v < 0.0 {
                    Err(Error::new(lit.span(), "Invalid weight"))
                } else if v == 0.0 {
                    Ok(None)
                } else {
                    Ok(Some(lit.to_token_stream()))
                }
            }
            Value::FnIdent(ident) => {
                let ident_s = ident.to_string();

                Ok(Some(quote! {
                {
                    let value = #ident (::mutagen::Reborrow::reborrow(&mut arg));
                    assert!(value >= 0.0, "{} returned invalid weight {}", #ident_s, value);
                    value
                }
                }))
            }
            Value::Values(values) => values.to_weight(),
            Value::Closure(c) => Ok(Some(quote! {
                {
                    let value = (#c)(::mutagen::Reborrow::reborrow(&mut arg));
                    assert!(value >= 0.0, "Closure returned invalid weight {}", value);
                    value
                }
            })),
            Value::Val(v) => {
                if *v == 0.0 {
                    Ok(None)
                } else {
                    Ok(Some(quote!(#v)))
                }
            }
            Value::Type(t) => Err(Error::new(t.span(), "Expected weight, found type")),
            Value::None(_) => Ok(Some(quote!(1.0))),
        }
    }

    fn to_prob(&self) -> Result<Option<TokenStream2>> {
        match self {
            Value::Lit(lit) => {
                let v: f64 = lit.base10_parse()?;
                if v < 0.0 || v > 1.0 {
                    Err(Error::new(lit.span(), "Invalid probability"))
                } else if v == 0.0 {
                    Ok(None)
                } else {
                    Ok(Some(lit.to_token_stream()))
                }
            }
            Value::FnIdent(ident) => {
                let ident_s = ident.to_string();

                Ok(Some(quote! {
                    {
                        let value = #ident (::mutagen::Reborrow::reborrow(&mut arg));
                        assert!(value >= 0.0, "{} returned invalid probability {}", #ident_s, value);
                        value
                    }
                }))
            }
            Value::Values(values) => Err(Error::new_spanned(
                values,
                "Expected probability, found array",
            )),
            Value::Closure(c) => Ok(Some(quote! {
                {
                    let value = (#c)(::mutagen::Reborrow::reborrow(&mut arg));
                    assert!(value >= 0.0, "Closure returned invalid probability {}", value);
                    value
                }
            })),
            Value::Val(v) => {
                if *v == 0.0 {
                    Ok(None)
                } else {
                    Ok(Some(quote!(#v)))
                }
            }
            Value::Type(t) => Err(Error::new(t.span(), "Expected probability, found type")),
            Value::None(_) => Ok(None),
        }
    }
}

impl Parse for Value {
    fn parse(input: ParseStream) -> Result<Self> {
        // TODO Add support for closure variant
        let lookahead = input.lookahead1();
        if lookahead.peek(Bracket) {
            input.parse().map(Value::Values)
        } else if lookahead.peek(Token![type]) {
            let _type: Token![type] = input.parse()?;
            input.parse().map(Value::Type)
        } else if lookahead.peek(LitFloat) {
            input.parse().map(Value::Lit)
        } else if lookahead.peek(Ident) {
            input.parse().map(Value::FnIdent)
        } else {
            Err(lookahead.error())
        }
    }
}

impl ToTokens for Value {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            Value::Lit(lit) => lit.to_tokens(tokens),
            Value::FnIdent(ident) => ident.to_tokens(tokens),
            Value::Values(values) => values.to_tokens(tokens),
            Value::Closure(c) => c.to_tokens(tokens),
            Value::Val(v) => {
                if *v == 0.0 {
                } else {
                    TokenStream2::to_tokens(&quote!(#v), tokens);
                }
            }
            Value::Type(t) => t.to_tokens(tokens),
            Value::None(_) => {}
        }
    }
}

#[derive(Clone)]
struct Values {
    bracket: Bracket,
    values: Punctuated<Value, Token![,]>,
}

impl Values {
    fn to_weight(&self) -> Result<Option<TokenStream2>> {
        let weights = self
            .values
            .iter()
            .map(|value| {
                let value_weight = value.to_weight()?;
                Ok(quote! {weight *= #value_weight;})
            })
            .collect::<Result<Vec<TokenStream2>>>()?;

        Ok(Some(quote! {
            {
                let mut weight = 1.0;
                #(#weights)*
                weight
            }
        }))
    }
}

impl Parse for Values {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        Ok(Self {
            bracket: bracketed!(content in input),
            values: content.parse_terminated(Value::parse)?,
        })
    }
}

impl ToTokens for Values {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        self.bracket
            .surround(tokens, |tokens| self.values.to_tokens(tokens));
    }
}

type Attrs = HashMap<String, Value>;

fn parse_attrs(attributes: &[Attribute], allowed: &[&str]) -> Result<Attrs> {
    Ok(attributes
        .iter()
        .filter(|attr| attr.path.is_ident(a::BASE))
        .map(|attr| {
            let data: AttrsData = parse2(attr.tokens.clone())?;
            data.values
                .into_iter()
                .map(|kv| {
                    let key = kv.key.to_string();

                    if !allowed.contains(&key.as_str()) {
                        return Err(Error::new(
                            attr.span(),
                            format!(
                                "Attribute {} not allowed on this item. Allowed attributes: {:?}",
                                key, allowed
                            ),
                        ));
                    }

                    Ok((key, kv.value))
                })
                .collect::<Result<Vec<_>>>()
        })
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .flatten()
        .collect())
}
