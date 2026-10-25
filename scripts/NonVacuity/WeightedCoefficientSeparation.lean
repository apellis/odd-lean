import OddMath.QuiverHecke.WeightedCoefficientSeparation
import OddMath.SKM.MixedCrossingLocalExamples

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke
open scoped Classical
variable {I X k : Type} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k)

/-- The full coefficient extension, including distinct exterior products,
is separated at total weight two by the two-strand cutoff five. -/
example (i j : I) :
    Function.Injective (fun x : ExtendedAtMost D Sc [i, j] [j, i] 2 =>
      (WeightedRelationSpan D Sc [i, j] [j, i] 5).mkQ
        (x : coefficientObj D Sc [i, j] ⟶ coefficientObj D Sc [j, i])) :=
  weighted_quotient_injective_on_extendedAtMost D Sc
    (by change 2 + 2 * (2 : ℕ).choose 2 < 5; decide)

private def coefficients (i j : {i : I // D.parity i = 1})
    (r : Fin 6) : OddMath.SKM.SYM D k :=
  if r.val = 5 then 1 else if r.val = 3 then
    OddMath.SKM.SYM.coefficientBasis D k (0, {i, j}) else 0

/-- A genuine monic deformation with a two-colour exterior coefficient:
`x^5 + b_{i,j} x^3`. No exterior variable is identified or discarded. -/
example (i j : {i : I // D.parity i = 1}) (hij : i ≠ j) :
    deformedCyclotomic D Sc [i.1, j.1] 5 (coefficients D i j) ∈
      WeightedRelationSpan D Sc [i.1, j.1] [i.1, j.1] 5 := by
  apply deformedCyclotomic_mem_relationSpan D Sc _ _ _ (by simp)
  intro r
  unfold coefficients
  split_ifs with h5 h3
  · rw [h5]
    exact OddMath.SKM.SYM.mem_coefficientAtLeast_zero D k 1
  · apply Submodule.subset_span
    refine ⟨(0, {i, j}), ?_, rfl⟩
    simp [h3, OddMath.SKM.SYM.coefficientWeight, hij]
  · exact Submodule.zero_mem _

#print axioms extendedScore_comp
#print axioms weightedRelationSpan_le_extendedAtLeast
#print axioms weighted_quotient_injective_on_extendedAtMost
#print axioms deformedCyclotomic_mem_relationSpan
#print axioms weighted_quotients_jointly_detect

namespace Concrete
open OddMath.SKM.MixedCrossingLocalExamples

private def params : OddMath.SKM.Scalars oddDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

private def i : {i : Bool // oddDatum.parity i = 1} := ⟨false, rfl⟩
private def j : {i : Bool // oddDatum.parity i = 1} := ⟨true, rfl⟩
private theorem different : i ≠ j := by decide

example : OddMath.SKM.SYM.coefficientBasis oddDatum ℚ (0, {i, j}) ≠ 0 :=
  (OddMath.SKM.SYM.coefficientBasis oddDatum ℚ).ne_zero _

private def identityIndex : NFIdx [false, true] [false, true] := by
  have hc : Categorification.TypeA.canWord 2 1 = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  exact ⟨([], 1), by simp, by simp, by simp [hc, cw]⟩

private def idx : OddMath.SKM.SYM.CoefficientIndex oddDatum × NFIdx [false, true] [false, true] :=
  ((0, {i, j}), identityIndex)

/-- A specific nonzero independent two-odd coefficient survives the actual
two-strand cutoff-five quotient over the rational numbers. -/
example : (WeightedRelationSpan oddDatum params [false, true] [false, true] 5).mkQ
    (extensionBasis oddDatum params [false, true] [false, true] idx) ≠ 0 := by
  have hmem : extensionBasis oddDatum params [false, true] [false, true] idx ∈
      ExtendedAtMost oddDatum params [false, true] [false, true] 2 := by
    apply Submodule.subset_span
    refine ⟨idx, ?_, rfl⟩
    simp [extensionDegree, idx, identityIndex, OddMath.SKM.SYM.coefficientWeight, different]
  intro hzero
  have hinj := weighted_quotient_injective_on_extendedAtMost oddDatum params
    (t := [false, true]) (t' := [false, true]) (d := 2) (N := 5) (by decide)
  have hz := hinj (a₁ := ⟨_, hmem⟩) (a₂ := 0) (by simpa using hzero)
  exact (extensionBasis oddDatum params [false, true] [false, true]).ne_zero idx
    (congrArg Subtype.val hz)

end Concrete
