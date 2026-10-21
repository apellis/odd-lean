import OddMath

/-! Concrete consumers of the polynomial input to BE2 Proposition 11.2.
The categorical split exact sequence is not asserted here. -/

namespace NonVacuity.SerrePolynomial
open OddMath.SKM OddMath.SKM.SerrePolynomial OddMath.SKM.SerrePolynomialExamples

example : datum.parity false = 1 := rfl
example : datum.dn false true = 4 := rfl
example : scalars.s false true 2 2 = 5 := rfl
example : scalars.Homogeneous := homogeneous
example : (symmetrizer.d true : ZMod 2) ≠ datum.parity true := symmetrizer_not_parity

example : serreWindow 4 2 (braidPolynomial scalars false true) =
    Finsupp.single (2, 1, 0) (-2 : ℚ) := mixed_window

example (u v : ℚ) : quadraticValue scalars false true (-u) v =
    quadraticValue scalars false true u v := neg_left u v

example : scalars.s false true 3 2 = 0 :=
  odd_exponent_coefficient_zero scalars (by rfl) true (by decide) 2

example : serreWindow 4 2 (braidTerm 2 2 : OrderedPolynomial ℚ) = 0 :=
  serreWindow_braidTerm_lt (by decide) (by decide) (by decide) 2

example (x z : ℚ) :
    (∑ r ∈ Finset.range 3, (z ^ 2) ^ r * (x ^ 2) ^ (3 - 1 - r)) *
      (z ^ 2 - x ^ 2) = (z ^ 2) ^ 3 - (x ^ 2) ^ 3 :=
  square_difference_factorization z x (Commute.all _ _) 3

#print axioms OddMath.SKM.SerrePolynomial.serreWindow_braidPolynomial
#print axioms OddMath.SKM.SerrePolynomial.quadraticValue_neg_left
#print axioms OddMath.SKM.SerrePolynomial.square_difference_factorization
#print axioms OddMath.SKM.SerrePolynomialExamples.mixed_window

end NonVacuity.SerrePolynomial
