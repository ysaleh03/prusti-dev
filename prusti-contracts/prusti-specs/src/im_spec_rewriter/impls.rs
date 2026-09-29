//! Encoding of mendel specs for impls
use super::common::*;
use crate::is_predicate_macro;
use proc_macro2::TokenStream;
use quote::quote_spanned;
use syn::{parse_quote, parse_quote_spanned, spanned::Spanned};

pub fn rewrite_im_spec(
    item_impl: &mut syn::ItemImpl,
    _mod_path: syn::Path,
) -> syn::Result<TokenStream> {
    let mut new_impl = item_impl.clone();
    new_impl.items = Vec::new();

    let mut shared: syn::ImplItemConst = parse_quote! { const SHARED_CAPABILITIES: () = (); };
    let mut mutable: syn::ImplItemConst = parse_quote! { const MUTABLE_CAPABILITIES: () = (); };

    for impl_item in item_impl.items.iter() {
        match impl_item {
            syn::ImplItem::Type(_) => {
                return Err(syn::Error::new(
                    impl_item.span(),
                    "Associated types in im_spec impls should not be declared",
                ));
            }
            syn::ImplItem::Method(impl_method) => {
                if !impl_method.attrs.contains(&parse_quote! { #[ghost_fn] }) {
                    return Err(syn::Error::new(
                        impl_method.span(),
                        "Cannot declare non-ghost functions in im_spec",
                    ));
                }
                new_impl.items.push(impl_item.clone());
            }
            syn::ImplItem::Macro(makro) if is_capable_macro(makro) => {
                let (is_mutable, attr) = extend_with_macro(makro)?;
                if is_mutable {
                    mutable.attrs.push(attr);
                } else {
                    shared.attrs.push(attr);
                }
            }
            syn::ImplItem::Macro(makro) if is_predicate_macro(makro) => {
                return Err(syn::Error::new(
                    makro.span(),
                    "Cannot declare abstract predicate in im_spec",
                ));
            }
            _ => unimplemented!("Unimplemented impl item for im_spec"),
        };
    }

    new_impl.items.extend(vec![
        syn::ImplItem::Const(shared),
        syn::ImplItem::Const(mutable),
    ]);

    Ok(quote_spanned! {item_impl.span()=>
        #[prusti::im_spec]
        #new_impl
    })
}

fn extend_with_macro(makro: &syn::ImplItemMacro) -> syn::Result<(bool, syn::Attribute)> {
    let capable_input: CapableInput = makro.mac.parse_body()?;
    let receiver = capable_input.receiver;

    let capability = match capable_input.capability {
        CapabilityInput {
            capability,
            addr: ptr,
        } => quote_spanned! {makro.span()=>
            ::prusti_contracts::Addr::#capability(self.#ptr())
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
    addr: syn::Ident,
}

impl syn::parse::Parse for CapabilityInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let capability: syn::Ident = input.parse()?;

        let content;
        syn::parenthesized!(content in input);

        match capability.to_string().as_str() {
            "unique" | "shared" | "local_unique" | "atomic_unique" => {
                let addr = content.parse()?;
                if !content.is_empty() {
                    return Err(content.error("unexpected tokens"));
                }
                Ok(CapabilityInput { capability, addr })
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
