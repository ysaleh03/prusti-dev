//! Processes `#[im_model]` attributed types.
//!
//! Usage documentation can be found in the corresponding macro definition.
//!
//! Given a `#[im_model]` attributed type `T` with fields `f0: Tf0`, `f1: Tf1`,
//! ... `fn: Tfn`, generates a function of type Addr<T> -> Addr<Tf0> for each
//! field. The implementation is `unimplemented!()`, `#[pure]` and `#[trusted]`

use crate::common::HasGenerics;

use super::parse_quote_spanned;
use syn::spanned::Spanned;
use uuid::Uuid;

/// See module level documentation
pub fn rewrite(
    item_struct: &syn::ItemStruct,
) -> syn::Result<(syn::ItemTrait, syn::ItemImpl, syn::ItemImpl)> {
    let item_ident = &item_struct.ident;

    let mut impl_generics_src = item_struct.generics().clone();
    let new_lifetime = generate_lifetime(item_struct);
    impl_generics_src
        .params
        .push(syn::GenericParam::Lifetime(syn::LifetimeDef::new(
            new_lifetime.clone(),
        )));

    let (new_impl_generics, new_ty_generics, _) = impl_generics_src.split_for_impl();
    let (_, ty_generics, where_clause) = item_struct.generics.split_for_impl();

    let trait_ident = generate_trait_ident(item_struct);
    let mut addr_trait: syn::ItemTrait = parse_quote_spanned! {item_struct.span() =>
        trait #trait_ident #new_impl_generics #where_clause {}
    };

    let addr_impl_shared: syn::ItemImpl = parse_quote_spanned! {item_struct.span() =>
        impl #new_impl_generics #trait_ident #new_ty_generics for ::prusti_contracts::Addr<#new_lifetime, &#item_ident #ty_generics> #where_clause {}
    };

    let addr_impl_mut: syn::ItemImpl = parse_quote_spanned! {item_struct.span() =>
        impl #new_impl_generics #trait_ident #new_ty_generics for ::prusti_contracts::Addr<#new_lifetime, &mut #item_ident #ty_generics> #where_clause {}
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

    let mut items = vec![];

    for field in fields {
        let name = field.ident.as_ref().expect("field names checked");
        let field_ty = &field.ty;

        let projection: syn::TraitItem = parse_quote_spanned! {field.span()=>
            #[pure]
            #[trusted]
            fn #name(self) -> ::prusti_contracts::Addr<#new_lifetime, #field_ty> {
                unimplemented!()
            }
        };
        items.push(projection)
    }

    addr_trait.items = items;

    Ok((addr_trait, addr_impl_shared, addr_impl_mut))
}

fn generate_trait_ident(item_struct: &syn::ItemStruct) -> syn::Ident {
    let mut name = item_struct.ident.to_string();

    for param in item_struct.generics.params.iter() {
        if let syn::GenericParam::Type(ty_param) = param {
            name.push_str(ty_param.ident.to_string().as_str());
        }
    }

    let uuid = Uuid::new_v4().simple();

    syn::Ident::new(
        format!("PrustiAddr{name}ImModel{uuid}").as_str(),
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
