import OddMath.QuiverHecke.BWWNondegeneracy
import NonVacuity.BWWReesParameters

/-! # The conjecture for Brundan–Wang–Webster parameters, on a concrete datum

On the datum of `NonVacuity.BWWScalars` (two even vertices, Cartan entries `-3`) with
symmetrizer `(1, 1)`: the parameters `Qᵢⱼ(u, v) = u³ + v³ + 1` over `ℚ` have a pure (constant)
coefficient, so they are not Brundan–Ellis parameters; they are lower-degree
(`NonVacuity.BWWReesParameters.constantTerm_lowerDegree`). With the constant normalization
every hypothesis of the headline theorems is proved: the conjecture holds for them over `ℚ`, and
for their graded Rees parameters `u³ + v³ + h⁶` over the `ℕ`-graded ring `ℚ[h]`.
-/

noncomputable section
namespace NonVacuity.BWWNondegeneracy
open OddMath OddMath.SKM OddMath.QuiverHecke
open NonVacuity.BWWScalars NonVacuity.BWWGradedParameters NonVacuity.BWWReesParameters

/-- Constant normalization units for `u³ + v³ + 1` (all `tᵢⱼ = 1`). -/
def cScalars : CScalars constantTerm.toScalars where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [constantTerm, BWWScalars.toScalars]

/-- The truncated Rees case for this datum. -/
example : (BWWParameterProperty.interiorNondegeneracy.{0, 0, 0} datum).TruncatedReesCase
    symmetrizer :=
  bwwTruncatedReesCase datum symmetrizer

/-- The conjecture for `u³ + v³ + 1` over `ℚ`, pure coefficient included. -/
example : NondegeneracyConjecture cScalars :=
  bwwLowerDegreeNondegeneracy datum symmetrizer ℚ (IsUnit.mk0 _ two_ne_zero) constantTerm
    constantTerm_lowerDegree cScalars

/-- The conjecture for the graded parameters `u³ + v³ + h⁶` over `ℚ[h]`, graded by degree. -/
example : NondegeneracyConjecture
    (BWWReesParameters.cScalars symmetrizer cScalars) :=
  bwwGradedNondegeneracy datum symmetrizer (MvPolynomial Unit ℚ)
    (MvPolynomial.homogeneousSubmodule Unit ℚ)
    (by simpa [map_ofNat] using (IsUnit.mk0 (2 : ℚ) two_ne_zero).map
      (MvPolynomial.C : ℚ →+* MvPolynomial Unit ℚ))
    (BWWReesParameters.scalars symmetrizer constantTerm)
    (BWWReesParameters.gradedHomogeneous symmetrizer constantTerm_lowerDegree)
    (BWWReesParameters.cScalars symmetrizer cScalars)

#print axioms bwwLowerDegreeNondegeneracy
#print axioms bwwGradedNondegeneracy

end NonVacuity.BWWNondegeneracy
