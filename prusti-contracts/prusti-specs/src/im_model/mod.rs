//! Processes `#[im_model]` attributed types.
//!
//! Usage documentation can be found in the corresponding macro definition.
//!
//! Given a `#[im_model]` attributed type `T` with fields `f0: Tf0`, `f1: Tf1`,
//! ... `fn: Tfn`, generates a function of type Addr<T> -> Addr<Tf0> for each
//! field. The implementation is `unimplemented!()`, `#[pure]` and `#[trusted]`
use super::parse_quote_spanned;
use syn::{parse_quote, spanned::Spanned};
use uuid::Uuid;

/// See module level documentation
pub fn rewrite(item_struct: &syn::ItemStruct) -> syn::Result<(syn::ItemTrait, syn::ItemImpl)> {
    let item_ident = &item_struct.ident;
    let new_lifetime = generate_lifetime(item_struct);

    let (impl_generics, ty_generics, where_clause) = item_struct.generics.split_for_impl();

    let trait_ident = generate_trait_ident(item_struct);
    let mut new_trait: syn::ItemTrait = parse_quote_spanned! {item_struct.span() =>
        trait #trait_ident #impl_generics #where_clause {}
    };

    let new_impl: syn::ItemImpl = parse_quote_spanned! {item_struct.span() =>
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

    let mut items = vec![];

    let self_ty: syn::Type = parse_quote!(#item_ident #ty_generics);
    items.push(parse_quote! {
        #[pure_memory]
        #[trusted]
        fn this<#new_lifetime>(&self) -> ::prusti_contracts::Addr<#new_lifetime, #self_ty> {
            unimplemented!()
        }
    });

    for field in fields {
        let name = field.ident.as_ref().expect("field names checked");
        let field_ty = &field.ty;

        let projection: syn::TraitItem = parse_quote_spanned! {field.span()=>
            #[pure_memory]
            #[trusted]
            fn #name<#new_lifetime>(&self) -> ::prusti_contracts::Addr<#new_lifetime, #field_ty> {
                unimplemented!()
            }
        };
        items.push(projection)
    }

    new_trait.items = items;

    Ok((new_trait, new_impl))
}

fn generate_trait_ident(item_struct: &syn::ItemStruct) -> syn::Ident {
    let mut name = item_struct.ident.to_string();

    // let uuid = Uuid::new_v4().simple();
    syn::Ident::new(
        format!("Prusti{name}ImModel").as_str(),
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
