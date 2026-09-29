//! Parsing of `#[im_spec]` attributed structures
pub mod impls;
mod common;

#[derive(Debug, Clone, Copy)]
pub enum MendelSpecKind {
    InherentImpl,
}

impl MendelSpecKind {
    const INHERENT_IMPL_IDENT: &'static str = "inherent_impl";
}

impl TryFrom<String> for MendelSpecKind {
    type Error = String;

    fn try_from(string: String) -> Result<Self, Self::Error> {
        match string.as_str() {
            Self::INHERENT_IMPL_IDENT => Ok(Self::InherentImpl),
            _ => Err(string),
        }
    }
}

impl From<MendelSpecKind> for String {
    fn from(spec_type: MendelSpecKind) -> Self {
        String::from(match spec_type {
            MendelSpecKind::InherentImpl => MendelSpecKind::INHERENT_IMPL_IDENT,
        })
    }
}
