//! Encoding of mendel specs for traits
use super::common::*;
use crate::is_predicate_macro;
use proc_macro2::TokenStream;
use quote::quote_spanned;
use syn::{parse_quote, spanned::Spanned, TypeParam};

/// Generates a struct for a `syn::ItemTrait` which is used for checking
/// compilation of mendel specs on traits.
///
/// Given an mendel spec for traits
/// ```rust
/// #[mendel_spec]
/// trait SomeTrait<T> {
///     fn foo(&self, arg: Self::ArgTy) -> Self::RetTy;
/// }
/// ```
/// it produces a struct
/// ```rust
/// struct Aux<T, TSelf> where TSelf: SomeTrait {
///     // phantom data for T, TSelf
/// }
/// ```
/// and a corresponding impl block with methods of `SomeTrait`.
///
pub fn rewrite_mendel_spec(
    item_trait: &mut syn::ItemTrait,
    mod_path: syn::Path,
) -> syn::Result<TokenStream> {
    let mut trait_path = mod_path;
    trait_path.segments.push(syn::PathSegment {
        ident: item_trait.ident.clone(),
        arguments: syn::PathArguments::None,
    });

    for trait_item in item_trait.items.iter_mut() {
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
                        "this cannot be a stub",
                    ));
                }
            }
            syn::TraitItem::Macro(makro) if is_abstract_ptr_macro(makro) => {
                let accessor = generate_abstract_ptr_accessor(makro)?;
                *trait_item = syn::TraitItem::Method(accessor);
            }
            syn::TraitItem::Macro(makro) if is_local_region_macro(makro) => {
                let accessor = generate_local_region_accessor(makro)?;
                *trait_item = syn::TraitItem::Method(accessor);
            }
            syn::TraitItem::Macro(makro) if is_predicate_macro(makro) => {
                return Err(syn::Error::new(
                    makro.span(),
                    "Can not declare abstract predicate in mendel spec",
                ));
            }
            _ => unimplemented!("Unimplemented trait item for mendel spec"),
        };
    }

    Ok(quote_spanned! {item_trait.span()=>
        #item_trait
    })
}

fn parse_trait_type_params(item_trait: &syn::ItemTrait) -> syn::Result<Vec<TypeParam>> {
    item_trait
        .generics
        .type_params()
        .cloned()
        .map(check_for_legacy_attributes)
        .collect()
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
    let method = parse_quote! {
        #[abstract_ptr]
        fn #name(&self) -> AbsPtr<#ty> { unimplemented!() }
    };
    Ok(method)
}

fn generate_local_region_accessor(
    makro: &syn::TraitItemMacro,
) -> syn::Result<syn::TraitItemMethod> {
    let name: syn::Ident = makro.mac.parse_body()?;
    let method = parse_quote! {
        #[local_region]
        fn #name(&self) -> LocalRegion { unimplemented!() }
    };
    Ok(method)
}

fn check_for_legacy_attributes(param: TypeParam) -> syn::Result<TypeParam> {
    if let Some(attr) = param.attrs.first() {
        Err(syn::Error::new(
            attr.span(),
            "The `#[concrete]` and `#[generic]` attributes are deprecated. To refine specs for specific concrete types, use type-conditional spec refinements instead.",
        ))
    } else {
        Ok(param)
    }
}
