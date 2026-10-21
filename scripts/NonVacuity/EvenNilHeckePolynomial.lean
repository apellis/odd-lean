import OddMath

/-! Nonzero polynomial consumers of the even-colour prerequisites to BE2 Lemma 11.1. -/

open OddMath.EvenNilHecke MvPolynomial

example (r : ℕ) : projectorAll r * projectorAll r = projectorAll r :=
  projectorAll_idempotent r
example : projectorAll 0 ≠ 0 := projectorAll_ne_zero 0
example : projectorAll 1 ≠ 0 := projectorAll_ne_zero 1
example : projectorAll 5 ≠ 0 := projectorAll_ne_zero 5
example : polynomialAction ℚ 1 (projector 1) 1 = 1 := polynomialAction_projector_one
example : polynomialAction (ZMod 4) 2 (projector 2) 1 = 1 := polynomialAction_projector_one
example : polynomialAction ℤ 0 (crossing 0 0) (X (0 : Fin 2) ^ 2) = X 0 + X 1 :=
  PolynomialExamples.crossing_square_variable
example : polynomialAction (ZMod 4) 1 (crossing 1 0) (X (2 : Fin 3) * X 0) = X 2 :=
  PolynomialExamples.crossing_spectator
