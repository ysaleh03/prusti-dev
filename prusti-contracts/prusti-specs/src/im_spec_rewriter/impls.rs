//! Encoding of mendel specs for impls
use super::common::*;
use crate::is_predicate_macro;
use proc_macro2::TokenStream;
use quote::{quote_spanned, ToTokens};
use syn::{parse_quote, parse_quote_spanned, spanned::Spanned};

pub fn rewrite_im_spec(
    item_impl: &mut syn::ItemImpl,
    _mod_path: syn::Path,
) -> syn::Result<TokenStream> {
    let mut new_trait = generate_empty_trait(item_impl)?;

    let mut shared: syn::TraitItemConst = parse_quote! { const SHARED_CAPABILITIES: () = (); };
    let mut mutable: syn::TraitItemConst = parse_quote! { const MUTABLE_CAPABILITIES: () = (); };

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
                        "All functions in im_spec must be `#[ghost_fn]`",
                    ));
                }
                new_trait
                    .items
                    .push(syn::TraitItem::Method(syn::TraitItemMethod {
                        attrs: impl_method.attrs.clone(),
                        sig: impl_method.sig.clone(),
                        default: Some(impl_method.block.clone()),
                        semi_token: None,
                    }));
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

    new_trait.items.extend(vec![
        syn::TraitItem::Const(shared),
        syn::TraitItem::Const(mutable),
    ]);

    let trait_ident = &new_trait.ident;
    let (impl_generics, ty_generics, where_clause) = item_impl.generics.split_for_impl();
    let self_ty = &*item_impl.self_ty;

    let empty_impl: syn::ItemImpl = parse_quote_spanned! {item_impl.span()=>
        impl #impl_generics #trait_ident #ty_generics for #self_ty #where_clause {}
    };

    Ok(quote_spanned! {item_impl.span()=>
        #[prusti::im_spec]
        #new_trait

        #[prusti::im_spec]
        #empty_impl
    })
}

fn generate_empty_trait(item_impl: &syn::ItemImpl) -> syn::Result<syn::ItemTrait> {
    let ident = match &*item_impl.self_ty {
        syn::Type::Path(type_path) => &type_path.path.segments.last().unwrap().ident,
        _ => {
            return Err(syn::Error::new(
                item_impl.span(),
                "`im_spec` can only be used on structs",
            ))
        }
    };
    let mut name = ident.to_string();

    for param in item_impl.generics.params.iter() {
        if let syn::GenericParam::Type(ty_param) = param {
            name.push_str(ty_param.ident.to_string().as_str());
        }
    }

    let uuid = uuid::Uuid::new_v4().simple();
    let trait_ident = syn::Ident::new(format!("Prusti{name}ImModel{uuid}").as_str(), ident.span());
    let (impl_generics, _ty_generics, where_clause) = &item_impl.generics.split_for_impl();

    Ok(parse_quote_spanned! {item_impl.span()=>
        trait #trait_ident #impl_generics #where_clause {}
    })
}

fn extend_with_macro(makro: &syn::ImplItemMacro) -> syn::Result<(bool, syn::Attribute)> {
    let capable_input: CapableInput = makro.mac.parse_body()?;
    let receiver = capable_input.receiver;

    let capability = match capable_input.capability {
        CapabilityInput {
            capability,
            addr0,
            addr1,
        } => {
            if let Some(addr1) = addr1 {
                quote_spanned! {makro.span()=>
                ::prusti_contracts::Addr::#capability(
                    self.#addr0(),
                    self.#addr1()
                )}
            } else {
                quote_spanned! {makro.span()=>
                ::prusti_contracts::Addr::#capability(
                    self.#addr0()
                )}
            }
        }
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
    addr0: syn::Ident,
    addr1: Option<syn::Ident>,
}

impl syn::parse::Parse for CapabilityInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let capability: syn::Ident = input.parse()?;

        let content;
        syn::parenthesized!(content in input);

        match capability.to_string().as_str() {
            "unique" | "shared" | "atomic_unique" => {
                let addr0 = content.parse()?;
                if !content.is_empty() {
                    return Err(content.error("unexpected tokens"));
                }
                Ok(CapabilityInput {
                    capability,
                    addr0,
                    addr1: None,
                })
            }
            "local_unique" => {
                let addr0 = content.parse()?;
                let addr1 = content.parse()?;
                if !content.is_empty() {
                    return Err(content.error("unexpected tokens"));
                }
                Ok(CapabilityInput {
                    capability,
                    addr0,
                    addr1: Some(addr1),
                })
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
