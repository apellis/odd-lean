import OddMath.QuiverHecke.UpwardPBWCoordinates
import OddMath.QuiverHecke.CanonicalPBWChoiceComparison
import OddMath.SKM.MixedCrossingLocalExamples

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke OddMath.SKM
open scoped Classical
open OddMath.SKM.MixedCrossingLocalExamples

private def params : Scalars oddDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

private def i : {i : Bool // oddDatum.parity i = 1} := ⟨false, rfl⟩
private def j : {i : Bool // oddDatum.parity i = 1} := ⟨true, rfl⟩

private def identityIndex : NFIdx [false, true] [false, true] := by
  have hc : Categorification.TypeA.canWord 2 1 = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  exact ⟨([], 1), by simp, by simp, by simp [hc, cw]⟩

/-- The affine coordinate extracts the entire product of independent odd
coefficients; there is no single global odd-parameter specialization. -/
example : coefficientPBWCoordinate oddDatum params identityIndex
    (coefficientPBWExpansion oddDatum params [false, true] [false, true]
      (Finsupp.single identityIndex (SYM.delta oddDatum ℚ i * SYM.delta oddDatum ℚ j))) =
    SYM.delta oddDatum ℚ i * SYM.delta oddDatum ℚ j := by simp

#print axioms coefficientPBWExpansion_injective
#print axioms upwardPBWExpansion_injective_of_observations
#print axioms canonicalChoiceIndex_injective
#print axioms canonicalChoice_expansion
#print axioms canonicalChoice_independence
