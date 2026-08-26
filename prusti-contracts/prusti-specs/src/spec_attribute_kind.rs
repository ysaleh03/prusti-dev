use std::convert::TryFrom;

/// This type identifies one of the procedural macro attributes of Prusti
#[derive(PartialEq, Eq, Copy, Clone, Debug, PartialOrd, Ord)]
pub enum SpecAttributeKind {
    /// All type specifications that alter its type must be processed before
    /// PrintCounterexample. Currently this only applies to Model.
    Model = 0,
    Requires = 1,
    Ensures = 2,
    AfterExpiry = 3,
    AssertOnExpiry = 4,
    Pure = 5,
    PureUnstable = 6,
    Mendel = 7,
    AbstractPointer = 8,
    GhostFn = 9,
    Modifies = 10,
    Reads = 11,
    Trusted = 12,
    Predicate = 13,
    Invariant = 14,
    RefineSpec = 15,
    Terminates = 16,
    PrintCounterexample = 17,
    Verified = 18,
    Capable = 19,
}

impl TryFrom<String> for SpecAttributeKind {
    type Error = String;

    fn try_from(name: String) -> Result<Self, Self::Error> {
        match name.as_str() {
            "requires" => Ok(SpecAttributeKind::Requires),
            "ensures" => Ok(SpecAttributeKind::Ensures),
            "after_expiry" => Ok(SpecAttributeKind::AfterExpiry),
            "assert_on_expiry" => Ok(SpecAttributeKind::AssertOnExpiry),
            "pure" => Ok(SpecAttributeKind::Pure),
            "pure_unstable" => Ok(SpecAttributeKind::PureUnstable),
            "mendel" => Ok(SpecAttributeKind::Mendel),
            "abstract_ptr" => Ok(SpecAttributeKind::AbstractPointer),
            "ghost_fn" => Ok(SpecAttributeKind::GhostFn),
            "modifies" => Ok(SpecAttributeKind::Modifies),
            // "modifies_none" => Ok(SpecAttributeKind::Modifies),
            "reads" => Ok(SpecAttributeKind::Reads),
            "trusted" => Ok(SpecAttributeKind::Trusted),
            "predicate" => Ok(SpecAttributeKind::Predicate),
            "invariant" => Ok(SpecAttributeKind::Invariant),
            "refine_spec" => Ok(SpecAttributeKind::RefineSpec),
            "model" => Ok(SpecAttributeKind::Model),
            "print_counterexample" => Ok(SpecAttributeKind::PrintCounterexample),
            "verified" => Ok(SpecAttributeKind::Verified),
            "capable" => Ok(SpecAttributeKind::Capable),
            _ => Err(name),
        }
    }
}
