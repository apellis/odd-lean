# Canonical content extension and restriction

This supplies the fixed-content realization prerequisite of SwappedVacuumCoordinates §6. `ELVContentSupportedExtension` proves that extension along the full old content inclusion vanishes off that content, and that its established balanced induction counit is an even supermodule isomorphism on every supported module. On matching content its inverse is the fully faithful inclusion unit; elsewhere both components vanish by full-coefficient content conservation.

`ELVContentRestrictionExtension.oldContentRestrictionExtensionIso` identifies extension of the fixed-content restriction with old restriction of the canonical extension. It composes the existing inclusion unit, the literal append/inclusion restriction square, and the supported counit. It applies to both moving parities and arbitrary full coefficient modules, including the vacuum. No flatness or equivalence with arbitrary whole-old-category modules is assumed.

Validation: both producers and paired mixed-parity representable consumers passed direct Lean with warnings as errors and the repository compatibility flags. Consumers audit all 22 and 7 owned declarations respectively against propext, Classical.choice, Quot.sound. Full integrated CI is pending for this topic head.

Remaining scope: compatibility of the canonical induction/restriction comparisons with the action unit, counit, dot and crossing must be established before claiming the fixed-content factor action. This result supplies the restriction comparison, not that completed action.
