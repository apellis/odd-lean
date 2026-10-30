# Cyclotomic short-column quotient

## Checked statements

The three modules `ELVCyclotomicCrossingTensor`, `ELVCyclotomicTopQuotient`,
and `ELVCyclotomicTopKernel` implement the diagram-category version of the
right-hand portion of `DeformedCyclotomicTopRow.md` §4.

- `Source` is the existing balanced-induction quotient with old cyclotomic Hom
  factors. Its coefficient functor is the parity-shifted old Hom with the
  total-parity-twisted lower left action.
- `ShortTarget` uses affine Hom spaces in the first factor, and affine lower
  balance with the same cyclotomic coefficient factor.
- `q_shortTensor` is literally `c ⊗ πᵖb ↦ bar(c) ⊗ πᵖb`.
- `q_surjective` uses quotient and tensor generation, not flatness.
- `ker_q` identifies the first-factor cyclotomic ideal relations. The inverse
  is defined from the prescribed cyclotomic balanced source itself.
- `ker_q_eq_movingImage` uses the proved full-ELV ideal sum and annihilation of
  append-old relations by balance. Its generators are `(h W₋) ⊗ πᵖb` in algebra
  order. `movingImage` is a submodule of `ShortTarget`, never a source object.
- `quotientEquiv` identifies that quotient with `Source`.
- `toCyclotomic_q_shortTensor` gives the descended literal crossing word:
  diagram order `append(b) ≫ crossLast ≫ append(c)`, algebra order `c τₙ b`.

All statements retain ordinary commutative ground scalars and the supplied
full scalar data, including its unit hypotheses. There is no commutative-ring
instance on the exterior coefficient algebra, no domain/nonzero-corner
hypothesis, and no finite-colour or height restriction.

## Subsequent source identification and remaining comparison

`ELVCyclotomicPprime` now constructs the epsilon-shifted balanced domain
`Rf ⊗_(S,jL) Π^epsilon(eB)` and its actual map P′, with the full moving-word
transport and prescribed epsilon shift. Its range is `movingImage`, hence
`range P′ = ker q`. `ELVCyclotomicShortColumns` supplies both literal columns
and their whole commutative squares. `ELVCyclotomicAlphaCoordinates` constructs
an actual left inverse for alpha and derives P′ injectivity from that square
and the independently proved `pMap_injective`.

Crossing-column injectivity, fixed-content matrix-algebra identification,
integer-degree identities and the all-height categorical snake remain open.

No injection is claimed for the descended crossing `Source → Old`.

## Verification

The new importing consumer `scripts/NonVacuity/ELVCyclotomicTopKernel.lean`
checks the quotient, kernel, moving generators, crossing formula, and empty
lower word. It audits every declaration owned by the three modules, including
compiler-generated declarations, against the three standard axioms.
The focused warning-as-error build and the importing consumer with default
elaboration settings both pass.
