# Distinct mates through coefficient truncation

Brundan–Ellis (1.12) uses the positive crossing of distinct colours. The
mixed coend has short induction endpoint `i`, coefficient restriction
endpoint `j`, and crossing parity `parity i * parity j`. Its coefficient
right action remains ordinary precomposition.

`ELVTruncatedMixedCross` identifies the literal truncated crossing with
the quotient of the old crossing and proves its supernaturality.
`ELVRestrictionCoendCoordinates` fixes the ordinary restriction coend
coordinates before specializing the categories.

`ELVTruncatedDistinctMate` compares the whole prescribed mate with the old
mate using the chosen append quotient isomorphism and the inverse of the
chosen even restriction square. The source chart sends `[g ⊗ b]` to
`[Q(g) ⊗ b]`; the target chart has the same formula. The whole coefficient
`cross(s) ≫ twist_(parity i * parity j)(append_j(g))` projects unchanged.
These crossing, chart and whole-square declarations pass scoped strict
checks.

`truncatedDistinctMateEquivAtOld` constructs the decoder as the inverse
target chart, followed by the old PBW decoder, followed by the source
chart. `truncatedDistinctMateEquivAtOld_hom` identifies its entire forward
linear map with the prescribed positive cup-crossing-cap.
`truncatedDistinctMate_bijective` proves bijectivity for every truncated
object, with only distinctness of the two colours. No flatness or
additional invertibility hypothesis is used.

The three producers and paired concrete consumer pass scoped strict
checks. The consumer covers both mixed orders, distinct odd colours
with crossing parity one, an odd exterior coefficient and its
inhomogeneous identity sum, both decoder roundtrips, and the empty word
at zero cutoff. All 71 declarations owned by the producers pass the
axiom allowlist audit. Full integration CI remains pending.

This is the global `TruncatedCategory` coend inverse. Native truncated
module and input-natural bundling, canonical `ContentModules`
restriction, and original-weight transport remain next. It does not
assert the final canonical weight factor action.
