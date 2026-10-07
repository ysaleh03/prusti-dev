use crate::common::HasMacro;

pub(crate) fn is_capable_macro<T: HasMacro>(makro: &T) -> bool {
    makro
        .mac()
        .path
        .segments
        .last()
        .map(|last| last.ident == "capable")
        .unwrap_or(false)
}

pub(crate) fn generate_im_model_ident(ident: &syn::Ident) -> syn::Ident {
    let name = ident.to_string();
    syn::Ident::new(format!("Prusti{name}ImModel").as_str(), ident.span())
}

pub(crate) fn generate_im_spec_ident(ident: &syn::Ident) -> syn::Ident {
    let name = ident.to_string();
    syn::Ident::new(format!("Prusti{name}ImSpec").as_str(), ident.span())
}
