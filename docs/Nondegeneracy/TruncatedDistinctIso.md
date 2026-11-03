# Homogeneous truncated distinct mate inverses

For Brundan–Ellis (1.12), `ELVMixedRectangularMate` identifies the whole
linear map of the two-append rectangular mate with the fixed mixed
coend map before specializing categories. The lower restriction and
induction are `j` and `i`; the upper induction and restriction are
`i` and `j`. Both chosen bending maps are even, and the crossing has
degree `parity i * parity j`.

`ELVTruncatedDistinctIso` uses the proved PBW decoder for the global
`TruncatedCategory` mate, without additional bijectivity or flatness
hypotheses. `truncatedDistinctModuleIso` is the prescribed homogeneous
module isomorphism. `truncatedDistinctFunctorIso` is its isomorphism on
input-module functors. Their forward maps are exactly the positive
rectangular cup-crossing-cap, and both inverses have the crossing degree.

Both producers and their concrete consumer pass scoped strict checks.
The consumer uses parity-shifted modules for both mixed orders and for
distinct odd colours, the zero cutoff and empty representable, both
whole-functor roundtrips, and inverse naturality on an odd parity map.
All 22 owned declarations pass the axiom allowlist audit. Integration
CI remains pending.

Canonical content restriction and original-weight transport remain
next; this result alone does not assert the canonical weight factor action.
