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
