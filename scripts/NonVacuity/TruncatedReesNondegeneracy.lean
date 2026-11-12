import OddMath.QuiverHecke.TruncatedReesNondegeneracy
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

/-! # The truncated case, on a concrete datum

The datum, symmetrizer and transported parameters of
`OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters`, over `ℚ`, with every hypothesis
proved.
-/

noncomputable section
namespace NonVacuity.TruncatedReesNondegeneracy
open OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

/-- The truncated case for this datum. -/
example : TruncatedRees.TruncatedReesNondegeneracy datum symmetrizer :=
  truncatedReesNondegeneracy datum symmetrizer

/-- The conjecture for the Rees parameters truncated to `ℚ[h]/(h^N)`. -/
example (cs : CScalars transportedScalars) (N : ℕ) :
    NondegeneracyConjecture
      (ScalarChange.cScalars datum (TruncatedRees.trunc ℚ N)
        (ReesParameters.cScalars symmetrizer cs)) :=
  truncatedReesNondegeneracy datum symmetrizer ℚ transportedScalars
    (transported_homogeneous.lowerDegree symmetrizer) cs N

/-- The conjecture over `ℚ` through the graded-coefficient statement. -/
example (cs : CScalars transportedScalars) : NondegeneracyConjecture cs :=
  nondegeneracyConjecture_of_lowerDegree (gradedCoefficientNondegeneracy datum symmetrizer)
    (IsUnit.mk0 _ two_ne_zero) (transported_homogeneous.lowerDegree symmetrizer) cs

#print axioms truncatedReesNondegeneracy
#print axioms gradedCoefficientNondegeneracy

end NonVacuity.TruncatedReesNondegeneracy
