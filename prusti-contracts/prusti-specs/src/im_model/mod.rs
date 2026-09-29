//! Processes `#[im_model]` attributed types.
//!
//! Usage documentation can be found in the corresponding macro definition.
//!
//! Given a `#[im_model]` attributed type `T` with fields `f0: Tf0`, `f1: Tf1`,
//! ... `fn: Tfn`, generates a function of type Addr<T> -> Addr<Tf0> for each
//! field. The implementation is `unimplemented!()`, `#[pure]` and `#[trusted]`

use super::parse_quote_spanned;
use proc_macro2::Ident;
use syn::spanned::Spanned;
use uuid::Uuid;

/// See module level documentation
pub fn rewrite(item_struct: &syn::ItemStruct) -> syn::Result<Vec<syn::Item>> {
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

    let ident = &item_struct.ident;
    let marker = Ident::new(&format!("PrustiImModelMarker{ident}"), ident.span());
    let (impl_generics, ty_generics, where_clause) = item_struct.generics.split_for_impl();

    let marker_item: syn::Item = parse_quote_spanned! {ident.span()=>
        #[allow(dead_code)]
        struct #marker;
    };
    let mut items = vec![marker_item];

    for field in fields {
        let name = field.ident.as_ref().expect("field names checked");
        let name_str = name.to_string();

        let field_ty = &field.ty;
        let field_key = field_key(name);

        let projection: syn::Item = parse_quote_spanned! {field.span()=>
            impl #impl_generics ::prusti_contracts::Projection<#field_key, #marker>
                for #ident #ty_generics #where_clause
            {
                type Target = #field_ty;

                #[pure]
                #[trusted]
                #[prusti::im_model_field = #name_str]
                fn project(
                    addr: ::prusti_contracts::Addr<Self>,
                ) -> ::prusti_contracts::Addr<#field_ty> {
                    unimplemented!()
                }
            }
        };
        items.push(projection)
    }

    Ok(items)
}

pub fn field_key(field: &Ident) -> u64 {
    todo!();
}

// TODO: Tests
