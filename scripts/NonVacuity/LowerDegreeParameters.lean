import OddMath

/-! # Universal lower-degree parameters, on a concrete datum

The all-odd two-colour datum with Cartan entries `-2` and `-4` and symmetrizer `(2, 1)` of
`OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters`, over `ℚ`. Every hypothesis of
the universality, graded-equivalence and field-reduction results is proved here except the
universal or field case of the conjecture, which is their explicit hypothesis; no instance of
the conjecture is asserted.
-/

noncomputable section
namespace NonVacuity.LowerDegreeParameters
open OddMath OddMath.SKM OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

/-- The universal lower-degree parameters are graded homogeneous for the coefficient-degree
grading. -/
example : (LowerDegreeParameters.scalars datum symmetrizer).GradedHomogeneous symmetrizer
    (LowerDegreeParameters.grading datum symmetrizer) :=
  LowerDegreeParameters.gradedHomogeneous datum symmetrizer

/-- Universality applies to the transported parameters over `ℚ`. -/
example (hU : NondegeneracyConjecture (LowerDegreeParameters.normalizations datum symmetrizer))
    (cs : CScalars transportedScalars) : NondegeneracyConjecture cs :=
  LowerDegreeParameters.nondegeneracyConjecture_of_universal symmetrizer hU
    (IsUnit.mk0 _ two_ne_zero) (transported_homogeneous.lowerDegree symmetrizer) cs

/-- The graded-coefficient statement is equivalent to the universal instance. -/
example : GradedCoefficientNondegeneracy.{0, 0, 0} datum symmetrizer ↔
    NondegeneracyConjecture (LowerDegreeParameters.normalizations datum symmetrizer) :=
  LowerDegreeParameters.gradedCoefficientNondegeneracy_iff datum symmetrizer

/-- The field case gives the conjecture for these parameters. -/
example (hK : LowerDegreeParameters.CharZeroFieldLowerDegreeNondegeneracy datum symmetrizer)
    (cs : CScalars transportedScalars) : NondegeneracyConjecture cs :=
  nondegeneracyConjecture_of_lowerDegree (gradedCoefficientNondegeneracy_of_charZeroField hK)
    (IsUnit.mk0 _ two_ne_zero) (transported_homogeneous.lowerDegree symmetrizer) cs

#print axioms OddMath.SKM.LowerDegreeParameters.universal_nondegeneracy
#print axioms OddMath.SKM.LowerDegreeParameters.gradedCoefficientNondegeneracy_iff

end NonVacuity.LowerDegreeParameters
