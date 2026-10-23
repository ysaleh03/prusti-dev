//! Processes `#[im_model]` attributed types.
//!
//! Usage documentation can be found in the corresponding macro definition.
//!
//! Given a `#[im_model]` attributed type `T` with fields `f0: Tf0`, `f1: Tf1`,
//! ... `fn: Tfn`, generates a function of type Addr<T> -> Addr<Tf0> for each
//! field. The implementation is `unimplemented!()`, `#[pure]` and `#[trusted]`
use super::parse_quote_spanned;
use crate::specifications::preparser::parse_prusti;
use proc_macro2::TokenTree;
use quote::quote;
use syn::{parse_quote, spanned::Spanned};
use uuid::Uuid;

/// See module level documentation
pub fn rewrite(
    item_struct: &syn::ItemStruct,
    spec_id: &str,
) -> syn::Result<(syn::ItemTrait, syn::ItemImpl)> {
    let item_ident = &item_struct.ident;
    let new_lifetime = generate_lifetime(item_struct);

    let (impl_generics, ty_generics, where_clause) = item_struct.generics.split_for_impl();

    let trait_ident = generate_trait_ident(item_struct);
    let mut new_trait: syn::ItemTrait = parse_quote_spanned! {item_struct.span() =>
        trait #trait_ident #impl_generics #where_clause {}
    };

    let mut new_impl: syn::ItemImpl = parse_quote_spanned! {item_struct.span() =>
        impl #impl_generics #trait_ident #ty_generics for #item_ident #ty_generics #where_clause {}
    };

    let fields = match &item_struct.fields {
        syn::Fields::Named(f) if !f.named.is_empty() => &f.named,
        syn::Fields::Unnamed(_) => {
            return Err(syn::Error::new(
                item_struct.span(),
                "im_model fields must be named",
            ))
        }
        _ => {
            return Err(syn::Error::new(
                item_struct.span(),
                "im_model must have at least one field",
            ))
        }
    };

    let self_ty: syn::Type = parse_quote!(#item_ident #ty_generics);
    let trait_name = &trait_ident.to_string();

    let mut trait_items = vec![];
    let mut impl_items = vec![];

    trait_items.push(parse_quote! {
        #[trusted]
        #[pure_memory]
        #[prusti::im_model_field]
        fn this<#new_lifetime>(&self) -> ::prusti_contracts::Addr<#new_lifetime, #self_ty>;
    });
    impl_items.push(parse_quote! {
        #[prusti::spec_only]
        #[prusti::im_model_field = #trait_name]
        fn this<#new_lifetime>(&self) -> ::prusti_contracts::Addr<#new_lifetime, #self_ty> {
            unimplemented!("ImModels can only be used in specifications")
        }
    });

    for field in fields {
        let name = field.ident.as_ref().expect("field names checked");
        let field_ty = &field.ty;

        trait_items.push(parse_quote_spanned! {field.span()=>
            #[trusted]
            #[pure_memory]
            #[prusti::im_model_field]
            fn #name<#new_lifetime>(&self) -> ::prusti_contracts::Addr<#new_lifetime, #field_ty>;
        });
        impl_items.push(parse_quote_spanned! {field.span()=>
            #[prusti::spec_only]
            #[prusti::im_model_field = #trait_name]
            fn #name<#new_lifetime>(&self) -> ::prusti_contracts::Addr<#new_lifetime, #field_ty> {
                unimplemented!("ImModels can only be used in specifications")
            }

        });
    }

    for (capability_index, attr) in item_struct
        .attrs
        .iter()
        .filter(|attr| {
            attr.path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "capable")
        })
        .enumerate()
    {
        let input = parse_capable(attr)?;
        let capability = input.capability.to_string();
        let side_condition = input
            .side_condition
            .unwrap_or_else(|| parse_quote_spanned! {attr.span()=> true});
        let name = syn::Ident::new(
            &format!("prusti_capable_{capability}_{capability_index}"),
            attr.span(),
        );
        let side_name = syn::Ident::new(&format!("{name}_side_condition"), attr.span());
        let addr_name = syn::Ident::new(&format!("{name}_addr"), attr.span());
        let ty = input.ty;
        let addr = input.addr;
        let capability_attr = syn::LitStr::new(&capability, attr.span());

        trait_items.push(syn::parse2(quote! {
            #[prusti::capable_side_condition]
            #[prusti::spec_id = #spec_id]
            fn #side_name(&self) -> bool;
        })?);
        trait_items.push(syn::parse2(quote! {
            #[prusti::capable_addr]
            #[prusti::capability = #capability_attr]
            #[prusti::spec_id = #spec_id]
            fn #addr_name<'a>(&'a self) -> ::prusti_contracts::Addr<'a, #ty>;
        })?);
        impl_items.push(syn::parse2(quote! {
            #[prusti::spec_only]
            #[prusti::capable_side_condition]
            #[prusti::spec_id = #spec_id]
            fn #side_name(&self) -> bool {
                #side_condition
            }
        })?);
        impl_items.push(syn::parse2(quote! {
            #[prusti::spec_only]
            #[prusti::capable_addr]
            #[prusti::capability = #capability_attr]
            #[prusti::spec_id = #spec_id]
            fn #addr_name<'a>(&'a self) -> ::prusti_contracts::Addr<'a, #ty> {
                #addr
            }
        })?);
    }

    new_trait.items = trait_items;
    new_impl.items = impl_items;

    Ok((new_trait, new_impl))
}

fn parse_capable(attr: &syn::Attribute) -> syn::Result<CapableInput> {
    let mut tokens = attr.tokens.clone().into_iter();
    let TokenTree::Group(group) = tokens
        .next()
        .ok_or_else(|| syn::Error::new(attr.span(), "capable requires arguments"))?
    else {
        return Err(syn::Error::new(attr.span(), "capable requires arguments"));
    };
    if tokens.next().is_some() {
        return Err(syn::Error::new(attr.span(), "invalid capable arguments"));
    }
    syn::parse2(group.stream())
}

struct CapableInput {
    side_condition: Option<syn::Expr>,
    capability: syn::Ident,
    ty: syn::Type,
    addr: syn::Expr,
}

impl syn::parse::Parse for CapableInput {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let receiver: syn::Receiver = input.parse()?;
        if !receiver
            .reference
            .as_ref()
            .is_some_and(|(_, lifetime)| lifetime.is_none())
        {
            return Err(syn::Error::new(
                receiver.span(),
                "expected `&self` or `&mut self`",
            ));
        }
        let side_condition = if input.peek(syn::Token![if]) {
            input.parse::<syn::Token![if]>()?;
            let mut tokens = proc_macro2::TokenStream::new();
            loop {
                if input.peek(syn::Token![=>]) {
                    input.parse::<syn::Token![=>]>()?;
                    break;
                }
                tokens.extend([input.parse::<TokenTree>()?]);
            }
            Some(syn::parse2(parse_prusti(tokens)?)?)
        } else {
            input.parse::<syn::Token![=>]>()?;
            None
        };
        let capability: syn::Ident = input.parse()?;
        match capability.to_string().as_str() {
            "read" | "write" | "exclusive" | "shared" | "local" => (),
            _ => {
                return Err(syn::Error::new(capability.span(), "unknown capability"));
            }
        }
        input.parse::<syn::Token![<]>()?;
        let ty = input.parse()?;
        input.parse::<syn::Token![>]>()?;
        let content;
        syn::parenthesized!(content in input);
        let addr = syn::parse2(parse_prusti(content.parse()?)?)?;
        Ok(Self {
            side_condition,
            capability,
            ty,
            addr,
        })
    }
}

fn generate_trait_ident(item_struct: &syn::ItemStruct) -> syn::Ident {
    let name = item_struct.ident.to_string();

    // let uuid = Uuid::new_v4().simple();
    syn::Ident::new(
        format!("Prusti{name}ImSpec").as_str(),
        item_struct.ident.span(),
    )
}

fn generate_lifetime(item_struct: &syn::ItemStruct) -> syn::Lifetime {
    let mut name = item_struct.ident.to_string();

    for param in item_struct.generics.params.iter() {
        if let syn::GenericParam::Type(ty_param) = param {
            name.push_str(ty_param.ident.to_string().as_str());
        }
    }

    let uuid = Uuid::new_v4().simple();

    syn::Lifetime::new(
        format!("'prusti_lifetime_{uuid}").as_str(),
        item_struct.ident.span(),
    )
}

// TODO: Tests
