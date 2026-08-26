use crate::common::HasMacro;

pub(crate) fn is_abstract_ptr_macro<T: HasMacro>(makro: &T) -> bool {
    makro
        .mac()
        .path
        .segments
        .last()
        .map(|last| last.ident == "abstract_ptr")
        .unwrap_or(false)
}

pub(crate) fn is_capable_macro<T: HasMacro>(makro: &T) -> bool {
    makro
        .mac()
        .path
        .segments
        .last()
        .map(|last| last.ident == "capable")
        .unwrap_or(false)
}
