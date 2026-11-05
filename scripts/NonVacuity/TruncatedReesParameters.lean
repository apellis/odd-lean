import OddMath

/-! # Truncated Rees parameters, on a concrete datum

The datum, symmetrizer and transported parameters of
`OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters`, over `ℚ`. The joint-detection
property of the truncations is proved outright; the conjecture for the truncated Rees
parameters is the explicit hypothesis of the reduction, and no instance of the conjecture is
asserted.
-/

noncomputable section
namespace NonVacuity.TruncatedReesParameters
open OddMath OddMath.SKM OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

/-- The truncations `ℚ[h] → ℚ[h]/(h^N)` jointly detect zero. -/
example (r : MvPolynomial Unit ℚ) (h : ∀ N, TruncatedRees.trunc ℚ N r = 0) : r = 0 :=
  TruncatedRees.trunc_separate ℚ r h

/-- The truncated case gives the conjecture for these parameters. -/
example (hT : TruncatedRees.TruncatedReesNondegeneracy datum symmetrizer)
    (cs : CScalars transportedScalars) : NondegeneracyConjecture cs :=
  nondegeneracyConjecture_of_lowerDegree (gradedCoefficientNondegeneracy_of_truncated hT)
    (IsUnit.mk0 _ two_ne_zero) (transported_homogeneous.lowerDegree symmetrizer) cs

#print axioms OddMath.SKM.gradedCoefficientNondegeneracy_of_truncated

end NonVacuity.TruncatedReesParameters
