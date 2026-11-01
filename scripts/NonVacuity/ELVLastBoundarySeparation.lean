import OddMath.QuiverHecke.ELVLastBoundarySeparation
import Lean.Util.CollectAxioms
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

/-- The literal signed LAST-boundary ideal, including all exterior coefficient
relations, retains the product of two distinct odd generators cofinally. -/
theorem pairExterior_survives (N : ℕ) (hN : 6 ≤ N) :
    (SignedLastELVRelationSpan oddDatum params (fun _ => N) [false, true] [false, true]).mkQ
      (extensionBasis oddDatum params [false, true] [false, true] idx) ≠ 0 := by
  have hmem : extensionBasis oddDatum params [false, true] [false, true] idx ∈
      ExtendedAtMost oddDatum params [false, true] [false, true] 2 := by
    apply Submodule.subset_span
    refine ⟨idx, ?_, rfl⟩
    have hij : i ≠ j := by decide
    simp [extensionDegree, idx, identityIndex, SYM.coefficientWeight, hij]
  intro hzero
  have hinj := signedLastELV_quotient_injective_on_extendedAtMost oddDatum params
    (cutoff := fun _ => N) (t := [false, true]) (t' := [false, true])
    (d := 2) (N := N) (fun _ => le_rfl) (by norm_num at *; omega)
  have hz := hinj (a₁ := ⟨_, hmem⟩) (a₂ := 0) (by simpa using hzero)
  exact (extensionBasis oddDatum params [false, true] [false, true]).ne_zero idx
    (congrArg Subtype.val hz)

/-- Both even and odd cutoff subsequences contain actual nonzero classes. -/
example (m : ℕ) (hm : 3 ≤ m) :
    (SignedLastELVRelationSpan oddDatum params (fun _ => 2 * m)
      [false, true] [false, true]).mkQ
        (extensionBasis oddDatum params [false, true] [false, true] idx) ≠ 0 :=
  pairExterior_survives _ (by omega)

example (m : ℕ) (hm : 3 ≤ m) :
    (SignedLastELVRelationSpan oddDatum params (fun _ => 2 * m + 1)
      [false, true] [false, true]).mkQ
        (extensionBasis oddDatum params [false, true] [false, true] idx) ≠ 0 :=
  pairExterior_survives _ (by omega)

/-- The nonempty prefix places this polynomial at the genuine second strand. -/
example (N : ℕ) :
    signedLastOddPolynomial oddDatum params j [false] N ∈
      ExtendedScore oddDatum params [false, true] [false, true] (N : ℤ) :=
  signedLastOddPolynomial_mem_score oddDatum params j [false] N

/-- Cutoff zero is covered by the same polynomial estimate, not discarded. -/
example :
    signedLastOddPolynomial oddDatum params i [true] 0 ∈
      ExtendedScore oddDatum params [true, false] [true, false] 0 :=
  signedLastOddPolynomial_mem_score oddDatum params i [true] 0

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.ELVLastBoundarySeparation
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
