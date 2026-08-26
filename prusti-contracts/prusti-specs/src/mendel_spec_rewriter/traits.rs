//! Encoding of mendel specs for traits
use super::common::*;
use crate::is_predicate_macro;
use proc_macro2::TokenStream;
use quote::quote_spanned;
use syn::{parse_quote, parse_quote_spanned, spanned::Spanned};

pub fn rewrite_mendel_spec(
    item_trait: &mut syn::ItemTrait,
    _mod_path: syn::Path,
) -> syn::Result<TokenStream> {
    let mut new_trait = item_trait.clone();
    new_trait.items = Vec::new();

    let mut shared: syn::TraitItemConst = parse_quote! { const SHARED_CAPABILITIES: () = (); };
    let mut mutable: syn::TraitItemConst = parse_quote! { const MUTABLE_CAPABILITIES: () = (); };

    for trait_item in item_trait.items.iter() {
        match trait_item {
            syn::TraitItem::Type(_) => {
                return Err(syn::Error::new(
                    trait_item.span(),
                    "Associated types in mendel trait specs should not be declared",
                ));
            }
            syn::TraitItem::Method(trait_method) => {
                if trait_method.default.is_none() {
                    return Err(syn::Error::new(
                        trait_method.span(),
                        "Expected a method body; mendel specs cannot contain stubs",
                    ));
                }
                if !trait_method.attrs.contains(&parse_quote! { #[ghost_fn] }) {
                    return Err(syn::Error::new(
                        trait_method.span(),
                        "Cannot declare non-ghost functions in mendel spec",
                    ));
                }
                new_trait.items.push(trait_item.clone());
            }
            syn::TraitItem::Macro(makro) if is_abstract_ptr_macro(makro) => {
                let accessor = generate_abstract_ptr_accessor(makro)?;
                new_trait.items.push(syn::TraitItem::Method(accessor));
            }
            syn::TraitItem::Macro(makro) if is_capable_macro(makro) => {
                let (is_mutable, attr) = extend_with_macro(makro)?;
                if is_mutable {
                    mutable.attrs.push(attr);
                } else {
                    shared.attrs.push(attr);
                }
            }
            syn::TraitItem::Macro(makro) if is_predicate_macro(makro) => {
                return Err(syn::Error::new(
                    makro.span(),
                    "Cannot declare abstract predicate in mendel spec",
                ));
            }
            _ => unimplemented!("Unimplemented trait item for mendel spec"),
        };
    }

    new_trait.items.extend(vec![
        syn::TraitItem::Const(shared),
        syn::TraitItem::Const(mutable),
    ]);

    Ok(quote_spanned! {item_trait.span()=>
        #[prusti::mendel_spec]
        #new_trait
    })
}

#[derive(Debug)]
struct AbstractPtrInput {
    name: syn::Ident,
    _comma: syn::Token![,],
    ty: syn::Type,
}

impl syn::parse::Parse for AbstractPtrInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let name = input.parse()?;
        let _comma = input.parse()?;
        let ty = input.parse()?;
        Ok(AbstractPtrInput { name, _comma, ty })
    }
}

fn generate_abstract_ptr_accessor(
    makro: &syn::TraitItemMacro,
) -> syn::Result<syn::TraitItemMethod> {
    let abstract_ptr_input: AbstractPtrInput = makro.mac.parse_body()?;
    let name = abstract_ptr_input.name;
    let ty = abstract_ptr_input.ty;
    let method = parse_quote_spanned! {makro.span()=>
        #[prusti::abstract_ptr]
        fn #name(&self) -> AbsPtr<#ty> { unimplemented!() }
    };
    Ok(method)
}

fn extend_with_macro(makro: &syn::TraitItemMacro) -> syn::Result<(bool, syn::Attribute)> {
    let capable_input: CapableInput = makro.mac.parse_body()?;
    let receiver = capable_input.receiver;

    let capability = match capable_input.capability {
        CapabilityInput { capability, ptr } => quote_spanned! {makro.span()=>
            ::prusti_contracts::AbsPtr::#capability(self.#ptr())
        },
    };

    let attr = if let Some(expr) = capable_input.side_conditions {
        let side_conditions = quote_spanned! {expr.span()=> #expr };
        parse_quote_spanned! {makro.span()=> #[capable(!#side_conditions || #capability)]}
    } else {
        parse_quote_spanned! {makro.span()=> #[capable(#capability)]}
    };

    Ok((receiver.mutability.is_some(), attr))
}

#[derive(Debug)]
struct CapabilityInput {
    capability: syn::Ident,
    ptr: syn::Ident,
}

impl syn::parse::Parse for CapabilityInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let capability: syn::Ident = input.parse()?;

        let content;
        syn::parenthesized!(content in input);

        match capability.to_string().as_str() {
            "read" | "write" | "local" | "unique" | "immutable" | "readRef" | "writeRef"
            | "noReadRef" | "noWriteRef" => {
                let ptr = content.parse()?;
                if !content.is_empty() {
                    return Err(content.error("unexpected tokens"));
                }
                Ok(CapabilityInput { capability, ptr })
            }
            _ => Err(syn::Error::new(capability.span(), "unknown capability")),
        }
    }
}

#[derive(Debug)]
struct CapableInput {
    receiver: syn::Receiver,
    _if: Option<syn::Token![if]>,
    side_conditions: Option<syn::Expr>,
    _fat_arrow: syn::Token![=>],
    capability: CapabilityInput,
}

impl syn::parse::Parse for CapableInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let receiver: syn::Receiver = input.parse()?;

        if !receiver.reference.clone().is_some_and(|r| r.1.is_none()) {
            return Err(syn::Error::new(
                receiver.span(),
                "Expected `&self` or `&mut self`",
            ));
        }

        let (_if, side_conditions) = if input.peek(syn::Token![if]) {
            let _if = input.parse()?;
            let expr = input.parse()?;
            (Some(_if), Some(expr))
        } else {
            (None, None)
        };

        let _fat_arrow = input.parse()?;
        let capability = input.parse()?;

        Ok(CapableInput {
            receiver,
            _if,
            side_conditions,
            _fat_arrow,
            capability,
        })
    }
}

// fn check_for_legacy_attributes(param: TypeParam) -> syn::Result<TypeParam> {
//     if let Some(attr) = param.attrs.first() {
//         Err(syn::Error::new(
//             attr.span(),
//             "The `#[concrete]` and `#[generic]` attributes are deprecated. To refine specs for specific concrete types, use type-conditional spec refinements instead.",
//         ))
//     } else {
//         Ok(param)
//     }
// }
