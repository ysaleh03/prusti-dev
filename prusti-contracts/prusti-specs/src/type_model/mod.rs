//! Processes `#[type_model]` attributed types.
//!
//! Usage documentation can be found in the corresponding macro definition.
//!
//! Given a `#[type_model]` attributed type `T`, this logic creates the following three items:
//! * A struct `M` which holds the type model's fields
//! * A trait which provides a `type_model` method to be used in specifications
//! * An implementation of the aforementioned trait for `T`.
//!   The implementation is `unimplemented!()`, `#[pure]` and `#[trusted]`
//!
//! The type_model struct `M` must be copyable.
//!
//! # Note
//! This macro always generates a trait with a `type_model` method on the fly for every modelled type.
//! With this design, one can even model external types which are not present in the local crate.

use super::parse_quote_spanned;
use crate::{
    common::add_phantom_data_for_generic_params,
    user_provided_type_params::{
        UserAnnotatedTypeParam, UserAnnotatedTypeParamParser, UserAnnotatedTypeParamParserError,
    },
    SPECS_VERSION,
};
use proc_macro2::{Ident, TokenStream};
use quote::ToTokens;
use syn::{parse_quote, punctuated::Punctuated, spanned::Spanned};
use uuid::Uuid;

/// See module level documentation
pub fn rewrite(item_struct: syn::ItemStruct) -> syn::Result<Vec<syn::Item>> {
    let res = rewrite_internal(item_struct);
    match res {
        Ok(result) => Ok(vec![
            syn::Item::Struct(result.type_model_struct),
            syn::Item::Trait(result.to_type_model_trait),
            syn::Item::Impl(result.type_model_impl),
        ]),
        Err(err) => Err(err.into()),
    }
}

type TypeModelGenerationResult<R> = Result<R, TypeModelGenerationError>;

fn rewrite_internal(item_struct: syn::ItemStruct) -> TypeModelGenerationResult<TypeModel> {
    let idents = GeneratedIdents::generate(&item_struct);

    let type_model_struct = TypeModelStruct::create(&item_struct, &idents)?;
    let to_type_model_trait = ToTypeModelTrait::create(&item_struct, &type_model_struct, &idents);
    let type_model_impl =
        create_type_model_impl(&item_struct, &type_model_struct, &to_type_model_trait)?;

    Ok(TypeModel {
        type_model_struct: type_model_struct.item,
        to_type_model_trait: to_type_model_trait.item,
        type_model_impl,
    })
}

struct TypeModelStruct {
    item: syn::ItemStruct,

    /// The path to the generated struct, e.g. to be used as a return type
    path: syn::Path,
}

impl TypeModelStruct {
    fn create(
        item_struct: &syn::ItemStruct,
        idents: &GeneratedIdents,
    ) -> TypeModelGenerationResult<Self> {
        if item_struct.fields.is_empty() {
            return Err(TypeModelGenerationError::MissingStructFields(
                item_struct.span(),
            ));
        }

        let type_model_struct_ident = &idents.type_model_struct_ident;
        let mut type_model_struct: syn::ItemStruct = parse_quote_spanned! {item_struct.span()=>
            #[derive(Copy, Clone)]
            #[allow(non_camel_case_types)]
            struct #type_model_struct_ident {}
        };

        let params = item_struct
            .parse_user_annotated_type_params()
            .map_err(TypeModelGenerationError::NonParsableTypeParam)?;
        type_model_struct.generics.params.extend(
            params
                .iter()
                .filter_map(UserAnnotatedTypeParam::as_generic_type_param)
                .cloned()
                .map(syn::GenericParam::Type),
        );

        type_model_struct.fields = item_struct.fields.clone();
        add_phantom_data_for_generic_params(&mut type_model_struct);

        let generic_idents =
            type_model_struct.generics.params.iter().filter_map(
                |generic_param| match generic_param {
                    syn::GenericParam::Type(type_param) => Some(&type_param.ident),
                    _ => None,
                },
            );
        let type_model_path: syn::Path = parse_quote!(
            #type_model_struct_ident < #(#generic_idents),* >
        );

        Ok(Self {
            item: type_model_struct,
            path: type_model_path,
        })
    }
}

struct ToTypeModelTrait {
    item: syn::ItemTrait,

    /// The path to the generated trait, e.g. to be used as a return type
    path: syn::Path,
}

impl ToTypeModelTrait {
    fn create(
        item_struct: &syn::ItemStruct,
        type_model_struct: &TypeModelStruct,
        idents: &GeneratedIdents,
    ) -> Self {
        let generic_params: Vec<syn::GenericParam> = type_model_struct
            .item
            .generics
            .params
            .iter()
            .cloned()
            .collect();
        let generic_params_idents: Vec<Ident> = generic_params
            .iter()
            .filter_map(|generic_param| match generic_param {
                syn::GenericParam::Type(type_param) => Some(type_param.ident.clone()),
                _ => None,
            })
            .collect();

        let type_model_path = &type_model_struct.path;

        let to_type_model_trait_ident = &idents.to_type_model_trait_ident;
        let item = parse_quote_spanned! {item_struct.span()=>
            #[allow(non_camel_case_types)]
            trait #to_type_model_trait_ident<#(#generic_params),*> {
                #[pure]
                #[trusted]
                #[prusti::type_type_models_to_type_model_fn]
                fn type_model(&self) -> #type_model_path;
            }
        };

        let path: syn::Path = parse_quote!(
            #to_type_model_trait_ident<#(#generic_params_idents),*>
        );

        Self { item, path }
    }
}

fn create_type_model_impl(
    item_struct: &syn::ItemStruct,
    type_model_struct: &TypeModelStruct,
    to_type_model_trait: &ToTypeModelTrait,
) -> TypeModelGenerationResult<syn::ItemImpl> {
    let ident = &item_struct.ident;

    let mut rewritten_generics: Vec<syn::GenericParam> = Vec::new();
    for param in &item_struct.generics.params {
        match param {
            syn::GenericParam::Lifetime(_) => rewritten_generics.push(parse_quote!('_)),
            syn::GenericParam::Type(type_param) => {
                let mut cloned = type_param.clone();
                cloned.attrs.clear();
                cloned.bounds = Punctuated::default();
                rewritten_generics.push(syn::GenericParam::Type(cloned))
            }
            syn::GenericParam::Const(const_param) => {
                return Err(TypeModelGenerationError::ConstParamDisallowed(
                    const_param.span(),
                ))
            }
        }
    }

    let generic_params: Vec<syn::GenericParam> = type_model_struct
        .item
        .generics
        .params
        .iter()
        .cloned()
        .collect();

    let impl_path: syn::Path = parse_quote!(
        #ident < #(#rewritten_generics),* >
    );

    let to_type_model_trait_path = &to_type_model_trait.path;
    let type_model_struct_path = &type_model_struct.path;
    let to_type_model_trait_str = &to_type_model_trait.item.ident.to_string();

    Ok(parse_quote_spanned! {item_struct.span()=>
        #[prusti::type_type_models_to_type_model_impl]
        #[prusti::specs_version = #SPECS_VERSION]
        impl<#(#generic_params),*> #to_type_model_trait_path for #impl_path {
            #[trusted]
            #[pure]
            #[prusti::type_type_models_to_type_model_fn = #to_type_model_trait_str]
            fn type_model(&self) -> #type_model_struct_path {
                unimplemented!("Models can only be used in specifications")
            }
        }
    })
}

/// [syn::Ident]s which are used for the generated items
struct GeneratedIdents {
    type_model_struct_ident: syn::Ident,
    to_type_model_trait_ident: syn::Ident,
}

impl GeneratedIdents {
    fn generate(item_struct: &syn::ItemStruct) -> Self {
        let mut name = item_struct.ident.to_string();

        for param in item_struct.generics.params.iter() {
            if let syn::GenericParam::Type(ty_param) = param {
                name.push_str(ty_param.ident.to_string().as_str());
            }
        }

        let uuid = Uuid::new_v4().simple();

        GeneratedIdents {
            type_model_struct_ident: Ident::new(
                format!("Prusti{name}Model_{uuid}").as_str(),
                item_struct.ident.span(),
            ),
            to_type_model_trait_ident: Ident::new(
                format!("Prusti{name}ToModel_{uuid}").as_str(),
                item_struct.ident.span(),
            ),
        }
    }
}

/// Errors that can happen during type_model generation.
/// These are mostly wrong usages of the macro by the user.
#[derive(Debug)]
enum TypeModelGenerationError {
    /// Thrown when the type_model contains no fields
    MissingStructFields(proc_macro2::Span),

    /// Thrown when using a const type param in the type_model
    ConstParamDisallowed(proc_macro2::Span),

    /// Thrown when user annotated generics could not be parsed
    NonParsableTypeParam(UserAnnotatedTypeParamParserError),
}

impl std::convert::From<TypeModelGenerationError> for syn::Error {
    fn from(err: TypeModelGenerationError) -> Self {
        match err {
            TypeModelGenerationError::MissingStructFields(span) => {
                syn::Error::new(span, "Type type_model must have at least one field")
            }
            TypeModelGenerationError::ConstParamDisallowed(span) => {
                syn::Error::new(span, "Const generics are disallowed for type_models")
            }
            TypeModelGenerationError::NonParsableTypeParam(parse_err) => parse_err.into(),
        }
    }
}

/// Type to represent generated code during expansion of the `#[type_model]` macro
struct TypeModel {
    /// The struct which represents the type_model
    type_model_struct: syn::ItemStruct,

    /// A trait which will be implemented on the type_modelled type
    /// to return the [TypeModel::type_model_struct]
    to_type_model_trait: syn::ItemTrait,

    /// The implementation of the [TypeModel::type_model_trait] on the type_modelled type.
    type_model_impl: syn::ItemImpl,
}

impl ToTokens for TypeModel {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.to_type_model_trait.to_tokens(tokens);
        self.type_model_struct.to_tokens(tokens);
        self.type_model_impl.to_tokens(tokens);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rewritten_type_model_to_tokens() {
        let to_type_model_trait: syn::ItemTrait = parse_quote!(
            trait PrustiFooToModel {}
        );
        let type_model_struct: syn::ItemStruct = parse_quote!(
            struct Foo {}
        );
        let trait_impl: syn::ItemImpl = parse_quote!(impl ToModel for Foo {});

        let rewritten_type_model = TypeModel {
            to_type_model_trait: to_type_model_trait.clone(),
            type_model_struct: type_model_struct.clone(),
            type_model_impl: trait_impl.clone(),
        };
        let actual_ts = rewritten_type_model.into_token_stream();

        let mut expected_ts = TokenStream::new();
        to_type_model_trait.to_tokens(&mut expected_ts);
        type_model_struct.to_tokens(&mut expected_ts);
        trait_impl.to_tokens(&mut expected_ts);

        assert_eq!(expected_ts.to_string(), actual_ts.to_string());
    }

    #[test]
    fn err_when_no_fields() {
        let input = parse_quote!(
            struct Foo {}
        );
        let result = rewrite_internal(input);
        assert!(matches!(
            result,
            Err(TypeModelGenerationError::MissingStructFields(_))
        ));
    }

    #[test]
    fn ok_generates_type_model_struct_def_with_named_fields() {
        let input = syn::parse_quote!(
            struct Foo {
                fld1: usize,
                fld2: i32,
            }
        );

        let type_model = expect_ok(rewrite_internal(input));

        let type_model_ident = check_type_model_ident(&type_model, "PrustiFooModel");
        let expected: syn::ItemStruct = syn::parse_quote!(
            #[derive(Copy, Clone)]
            #[allow(non_camel_case_types)]
            struct #type_model_ident {
                fld1: usize,
                fld2: i32,
            }
        );
        assert_eq_tokenizable(type_model.type_model_struct, expected);
    }

    #[test]
    fn ok_generates_type_model_struct_def_with_unnamed_fields() {
        let input = parse_quote!(
            struct Foo(i32, u32, usize);
        );

        let type_model = expect_ok(rewrite_internal(input));

        let type_model_ident = check_type_model_ident(&type_model, "PrustiFooModel");

        let expected: syn::ItemStruct = parse_quote!(
            #[derive(Copy, Clone)]
            #[allow(non_camel_case_types)]
            struct #type_model_ident(i32, u32, usize);
        );
        assert_eq_tokenizable(type_model.type_model_struct, expected);
    }

    #[test]
    fn ok_generates_impl_for_to_type_model_trait() {
        let input = parse_quote!(
            struct Foo(i32, u32, usize);
        );
        let type_model = expect_ok(rewrite_internal(input));

        let type_model_ident = check_type_model_ident(&type_model, "PrustiFooModel");
        let trait_ident = check_trait_ident(&type_model, "PrustiFooToModel");
        let trait_ident_str = trait_ident.to_string();

        let expected: syn::ItemImpl = parse_quote!(
            #[prusti::type_type_models_to_type_model_impl]
            #[prusti::specs_version = #SPECS_VERSION]
            impl #trait_ident<> for Foo <> {
                #[trusted]
                #[pure]
                #[prusti::type_type_models_to_type_model_fn = #trait_ident_str]
                fn type_model(&self) -> #type_model_ident<> {
                    unimplemented!("Models can only be used in specifications")
                }
            }
        );

        assert_eq_tokenizable(expected, type_model.type_model_impl);
    }

    #[test]
    fn ok_uses_inferred_lifetime() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo<'a, 'b>(i32, u32, usize);
        );
        let type_model = expect_ok(rewrite_internal(input));

        let type_model_ident = check_type_model_ident(&type_model, "PrustiFooModel");
        let trait_ident = check_trait_ident(&type_model, "PrustiFooToModel");
        let trait_ident_str = trait_ident.to_string();

        let expected_struct: syn::ItemStruct = parse_quote!(
            #[derive(Copy, Clone)]
            #[allow(non_camel_case_types)]
            struct #type_model_ident(i32, u32, usize);
        );
        let expected_impl: syn::ItemImpl = parse_quote!(
            #[prusti::type_type_models_to_type_model_impl]
            #[prusti::specs_version = #SPECS_VERSION]
            impl #trait_ident<> for Foo<'_, '_> {
                #[trusted]
                #[pure]
                #[prusti::type_type_models_to_type_model_fn = #trait_ident_str]
                fn type_model(&self) -> #type_model_ident<> {
                    unimplemented!("Models can only be used in specifications")
                }
            }
        );

        assert_eq_tokenizable(type_model.type_model_struct, expected_struct);
        assert_eq_tokenizable(type_model.type_model_impl, expected_impl);
    }

    #[test]
    fn ok_with_concrete_and_generic_params() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo<#[concrete] i32, #[generic] T, #[concrete] usize, #[generic] U>(i32);
        );
        let type_model = expect_ok(rewrite_internal(input));

        let type_model_ident = check_type_model_ident(&type_model, "PrustiFooi32TusizeUModel");
        let trait_ident = check_trait_ident(&type_model, "PrustiFooi32TusizeUToModel");
        let trait_ident_str = trait_ident.to_string();

        let expected_struct: syn::ItemStruct = parse_quote!(
            #[derive(Copy, Clone)]
            #[allow(non_camel_case_types)]
            struct #type_model_ident<T, U> (i32,::core::marker::PhantomData<T> , ::core::marker::PhantomData<U>);
        );

        let expected_trait: syn::ItemTrait = parse_quote!(
            #[allow(non_camel_case_types)]
            trait #trait_ident<T, U> {
                #[pure]
                #[trusted]
                #[prusti::type_type_models_to_type_model_fn]
                fn type_model(&self) -> #type_model_ident<T, U>;
            }
        );

        let expected_impl: syn::ItemImpl = parse_quote!(
            #[prusti::type_type_models_to_type_model_impl]
            #[prusti::specs_version = #SPECS_VERSION]
            impl<T, U> #trait_ident<T, U> for Foo<i32, T, usize, U> {
                #[trusted]
                #[pure]
                #[prusti::type_type_models_to_type_model_fn = #trait_ident_str]
                fn type_model(&self) -> #type_model_ident<T, U> {
                    unimplemented!("Models can only be used in specifications")
                }
            }
        );

        assert_eq_tokenizable(type_model.type_model_struct, expected_struct);
        assert_eq_tokenizable(type_model.to_type_model_trait, expected_trait);
        assert_eq_tokenizable(type_model.type_model_impl, expected_impl);
    }

    #[test]
    fn ok_defines_to_type_model_trait() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo(i32, u32, usize);
        );

        let type_model = expect_ok(rewrite_internal(input));

        let type_model_ident = check_type_model_ident(&type_model, "PrustiFooModel");
        let trait_ident = check_trait_ident(&type_model, "PrustiFooToModel");

        let actual = type_model.to_type_model_trait;
        let expected: syn::ItemTrait = parse_quote!(
            #[allow(non_camel_case_types)]
            trait #trait_ident {
                #[pure]
                #[trusted]
                #[prusti::type_type_models_to_type_model_fn]
                fn type_model(&self) -> #type_model_ident<>;
            }
        );

        assert_eq_tokenizable(actual, expected);
    }

    #[test]
    fn err_const_generics_disallowed() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo<const PAR: i32>(i32, u32, usize);
        );
        let result = rewrite_internal(input);
        assert!(matches!(
            result,
            Err(TypeModelGenerationError::ConstParamDisallowed(_))
        ));
    }

    #[test]
    fn err_non_annotated_generic() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo<T>(i32, u32, usize);
        );
        let result = rewrite_internal(input);
        assert!(matches!(
            result,
            Err(TypeModelGenerationError::NonParsableTypeParam(
                UserAnnotatedTypeParamParserError::InvalidAnnotation(_)
            ))
        ));
    }

    fn expect_ok(result: Result<TypeModel, TypeModelGenerationError>) -> TypeModel {
        result.expect("Expected Ok result")
    }

    fn assert_eq_tokenizable<T: ToTokens, U: ToTokens>(actual: T, expected: U) {
        assert_eq!(
            actual.into_token_stream().to_string(),
            expected.into_token_stream().to_string()
        );
    }

    fn check_type_model_ident(type_model: &TypeModel, expected_prefix: &str) -> Ident {
        let ident = &type_model.type_model_struct.ident;
        assert!(ident.to_string().starts_with(expected_prefix));
        ident.clone()
    }

    fn check_trait_ident(type_model: &TypeModel, expected_prefix: &str) -> Ident {
        let ident = &type_model.to_type_model_trait.ident;
        assert!(ident.to_string().starts_with(expected_prefix));
        ident.clone()
    }
}
