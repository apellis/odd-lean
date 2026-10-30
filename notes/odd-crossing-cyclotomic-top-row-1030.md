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

## Remaining source identification

The epsilon-shifted balanced domain `Rf ⊗_(S,jL) Π^epsilon(eB)` and its map P′
are not yet constructed. Consequently `ker_q_eq_movingImage` is a concrete
kernel calculation, not yet a theorem `range P′ = ker q` for that named map.
The next step is its lower-balance descent using the moving-word transport
and the prescribed epsilon shift. Then identify its range with `movingImage`
and compare the literal unquotiented short-column maps with the existing
Mackey source and append target. Fixed-content matrix-algebra identification,
integer-degree identities, and the all-height snake conclusion remain open.

No injection is claimed for the descended crossing `Source → Old`.

## Verification

The new importing consumer `scripts/NonVacuity/ELVCyclotomicTopKernel.lean`
checks the quotient, kernel, moving generators, crossing formula, and empty
lower word. It audits every declaration owned by the three modules, including
compiler-generated declarations, against the three standard axioms.
The focused warning-as-error build and the importing consumer with default
elaboration settings both pass.
