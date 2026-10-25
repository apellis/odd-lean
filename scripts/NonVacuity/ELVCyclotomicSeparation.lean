import OddMath.QuiverHecke.ELVCyclotomicSeparation
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

/-- The source odd polynomial at even cutoff two has left coefficient +delta. -/
example : SYM.elvMonicCoefficient oddDatum ℚ i 2 ⟨1, by decide⟩ = SYM.delta oddDatum ℚ i := by
  norm_num [SYM.elvMonicCoefficient, SYM.elvCoefficient, SYM.elvChi]

/-- At odd cutoff three the constant term has the normalized negative sign. -/
example : SYM.elvMonicCoefficient oddDatum ℚ i 3 ⟨0, by decide⟩ =
    -(SYM.delta oddDatum ℚ i * SYM.e oddDatum ℚ false 0) := by
  norm_num [SYM.elvMonicCoefficient, SYM.elvCoefficient, SYM.elvChi, i]
  exact neg_one_smul ℚ (SYM.delta oddDatum ℚ i * SYM.e oddDatum ℚ false 0)

private def identityIndex : NFIdx [false, true] [false, true] := by
  have hc : Categorification.TypeA.canWord 2 1 = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  exact ⟨([], 1), by simp, by simp, by simp [hc, cw]⟩

private def idx : SYM.CoefficientIndex oddDatum × NFIdx [false, true] [false, true] :=
  ((0, {i, j}), identityIndex)

/-- The full explicit coefficient relations and colour-correct cyclotomic
polynomials at cutoff six do not kill a distinct two-odd exterior PBW vector. -/
example : (ELVRelationSpan oddDatum params (fun _ => 6) [false, true] [false, true]).mkQ
    (extensionBasis oddDatum params [false, true] [false, true] idx) ≠ 0 := by
  have hmem : extensionBasis oddDatum params [false, true] [false, true] idx ∈
      ExtendedAtMost oddDatum params [false, true] [false, true] 2 := by
    apply Submodule.subset_span
    refine ⟨idx, ?_, rfl⟩
    have hij : i ≠ j := by decide
    simp [extensionDegree, idx, identityIndex, SYM.coefficientWeight, hij]
  intro hzero
  have hinj := elv_quotient_injective_on_extendedAtMost oddDatum params
    (cutoff := fun _ => 6) (t := [false, true]) (t' := [false, true])
    (d := 2) (N := 6) (fun _ => le_rfl) (by decide)
  have hz := hinj (a₁ := ⟨_, hmem⟩) (a₂ := 0) (by simpa using hzero)
  exact (extensionBasis oddDatum params [false, true] [false, true]).ne_zero idx
    (congrArg Subtype.val hz)

#print axioms SYM.elvMonicCoefficient_top
#print axioms SYM.elvCoefficient_quotient_injective
#print axioms elvGenerator_mem_score
#print axioms elv_quotient_injective_on_extendedAtMost
#print axioms even_elv_quotients_jointly_detect
