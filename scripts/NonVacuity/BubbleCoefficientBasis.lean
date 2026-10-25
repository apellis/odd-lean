import OddMath.SKM.BubbleCoefficientBasis

noncomputable section
open OddMath.SKM
open scoped Classical
variable {I X k : Type} [AddCommGroup X] [CommRing k] (D : Datum I X)

example (i j : {i : I // D.parity i = 1}) (h : i ≠ j) :
    SYM.coefficientWeight D (0, {i, j}) = 2 := by
  simp [SYM.coefficientWeight, h]

/-- Distinct exterior monomials are basis vectors over every nonzero ground ring. -/
example [Nontrivial k] (i j : {i : I // D.parity i = 1}) :
    SYM.coefficientBasis D k (0, {i, j}) ≠ 0 :=
  (SYM.coefficientBasis D k).ne_zero _

example : Function.Injective (fun x : SYM.CoefficientAtMost D k 2 =>
    (SYM.coefficientIdeal D k 3).ringCon.mk' (x : SYM D k)) :=
  SYM.coefficient_weight_quotient_injective D k (by decide)

#print axioms SYM.coefficientBasis
#print axioms SYM.coefficientAtLeast_mul
#print axioms SYM.coefficientIdeal
#print axioms SYM.coefficient_weight_quotient_injective
