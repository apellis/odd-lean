# Parity and the regular coefficient power module

This supplies the parity part of the literal coefficient quotient in
[DeformedReservoirBound, §§1–2](DeformedReservoirBound.md), using the actual
A/T of [CoefficientPowerQuotient](CoefficientPowerQuotient.md). The changed
foundation, its existing consumer, the new producer and occupied consumer
pass scoped Lean checks with warnings as errors and both pinned compatibility
settings. All 56 owned declarations of `ELVCoefficientCategory` and all 25 of
`ELVCoefficientPowerGrading` pass the standard axiom allowlist audit. Full CI
remains the integration gate.

The existing generic homogeneous-quotient proof in
`ELVCoefficientCategory` now has a public forwarding interface: projection
closure of a homogeneous two-sided generator span, its literal quotient
superspace, projection and homogeneous-representative identities, and its
quotient graded algebra. The original private names and proofs are unchanged.
This avoids a second quotient-grading proof or a new flatness assumption.

Every elementary power generating T is even. Thus projection of an element
of T remains in T. Applying the existing quotient construction gives
`coefficientPowerSpace` on the literal carrier A/T and the parity grading
`coefficientPowerParity`. `coefficientPowerGradedAlgebra` proves that its
multiplication respects this grading. The original coefficient quotient
preserves every homogeneous representative and its parity projection.

## The regular coefficient module

`coefficientPowerRegular` is the actual regular left A-action on A/T,
as a superfunctor from the original one-object full coefficient
supercategory to SVec. A coefficient a acts by left multiplication by
its literal quotient class. The categorical multiplication order is kept:
composition in the coefficient category reverses the displayed element
order, exactly as required by the covariant regular module. Additivity,
linearity and preservation of homogeneous map parity are proved.
`coefficientPowerRegular_kills` proves every element of the entire ideal T
acts as zero on every vector.

The connected two-odd-colour consumer at cutoff four with fourth elementary
powers proves both odd coefficient classes survive actual A/T and remain
in its odd part. Their regular operators are proved odd and nonzero by
evaluation on 1. It also checks a defining even fourth power acts as zero
on all regular-module vectors. Thus the parity and regular action are
occupied rather than inferred after exterior specialization.

## Boundary

This is the coefficient regular module, not yet its extension to the old
word category or the swapped action's vacuum. Integer grading and its
compatibility with parity remain separate inputs for the graded reservoir.
No positive-dot nilpotence is inferred from finite dimension alone;
nilpotence requires the stated positive degree and support argument, or
an explicitly transported weighted-category dot bound. The actual vacuum
evaluation kernel and all-height bubble theorem remain open.
