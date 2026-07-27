//! Parsing of `#[mendel_spec]` attributed structures

pub mod impls;
pub mod traits;
mod common;

#[derive(Debug, Clone, Copy)]
pub enum MendelSpecKind {
    InherentImpl,
    TraitImpl,
    Trait,
}

impl MendelSpecKind {
    const INHERENT_IMPL_IDENT: &'static str = "inherent_impl";
    const TRAIT_IMPL_IDENT: &'static str = "trait_impl";
    const TRAIT_IDENT: &'static str = "trait";
}

impl TryFrom<String> for MendelSpecKind {
    type Error = String;

    fn try_from(string: String) -> Result<Self, Self::Error> {
        match string.as_str() {
            Self::INHERENT_IMPL_IDENT => Ok(Self::InherentImpl),
            Self::TRAIT_IMPL_IDENT => Ok(Self::TraitImpl),
            Self::TRAIT_IDENT => Ok(Self::Trait),
            _ => Err(string),
        }
    }
}

impl From<MendelSpecKind> for String {
    fn from(spec_type: MendelSpecKind) -> Self {
        String::from(match spec_type {
            MendelSpecKind::InherentImpl => MendelSpecKind::INHERENT_IMPL_IDENT,
            MendelSpecKind::TraitImpl => MendelSpecKind::TRAIT_IMPL_IDENT,
            MendelSpecKind::Trait => MendelSpecKind::TRAIT_IDENT,
        })
    }
}
