# Scalar append comparison on coend units

The selected comparison `probeAppendOrdinaryModuleIso` is already established. The remaining generator comparison is being redesigned around its value on the source coend unit. `ELVProbeAppendUnits` proposes `probeAppendOrdinaryModuleIso_hom_unit`, computing the same five canonical maps only on unit generators. Generic flattening and unflattening unit formulas avoid arbitrary old Hom coefficients in the intermediate comparison.

This producer and its paired mixed/vacuum consumers are unverified drafts. No new completed comparison theorem is asserted. After the unit identity is checked, the proposed full tensor formula follows from even module naturality, scalar Hom roundtrip, and `BalancedInduction.postcompose_unit`.

The chosen ordinary probe model and the established comparison are retained. The direct old signed-dot unit is independent of this normalization; it does not discharge the full crossing or adjunction comparison obligations.
