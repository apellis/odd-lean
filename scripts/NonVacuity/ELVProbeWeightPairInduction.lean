import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightPairInduction
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeWeightPairInductionConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private def M (x : Bool → ℤ) : ProbeOldWeightProduct D Sc m Λ x := fun β => N β.1.toList
private def shifted (x : Bool → ℤ) : ProbeOldWeightProduct D Sc m Λ x := fun β =>
  ⟨supermoduleParityObj ((M x β).obj),
    probeEvaluatesCoefficients_parity D Sc m β.1.toList (M x β).obj (M x β).property⟩
private def oddInput (x : Bool → ℤ) : shifted x ⟶ M x := fun β =>
  ⟨(supermoduleParityIso (M x β).obj).hom⟩
private theorem oddInput_mem (x : Bool → ℤ) : oddInput x ∈ parity (R := ℚ) _ _ 1 :=
  fun β => supermoduleParityIso_hom_mem (M x β).obj
private def w (v : List Bool) : Bool → ℤ := (v.map D.α).sum - Λ
private def base (v : List Bool) : WeightBlocks D Λ (w v) := ⟨v, rfl⟩
private theorem lower (x : Bool → ℤ) (i : Bool) : (x - D.α i) + D.α i = x := sub_add_cancel _ _
private def emptyBlock : WeightBlocks D Λ (-Λ) := ⟨0, by simp⟩
private theorem emptyAbsent (i : Bool) :
    ¬ ∃ β, blockSucc D Λ i (lower (-Λ) i) β = emptyBlock := by
  intro h
  have hi := (exists_blockSucc_iff D Λ i (lower (-Λ) i) emptyBlock).mp h
  simp [emptyBlock] at hi

example (i j : Bool) := probeOldBlockPairInd D Sc m i j Λ rfl rfl (base [i,!i])
example (i j : Bool) := probeOldEFunctor_comp₂_blockSucc D Sc m i j Λ rfl rfl (base [i,!i])

private theorem emptyDoubleAbsent (i j : Bool) :
    ¬ ∃ β, blockSucc₂ D i j Λ (lower (-Λ - D.α i) j) (lower (-Λ) i) β = emptyBlock := by
  intro h
  obtain ⟨β, hβ⟩ := h
  exact emptyAbsent i ⟨blockSucc D Λ j (lower (-Λ - D.α i) j) β, hβ⟩
example (i j : Bool) := probeOldEFunctor_comp₂_isZero D Sc m i j Λ
  (lower (-Λ - D.α i) j) (lower (-Λ) i) emptyBlock (emptyDoubleAbsent i j)
  (M (-Λ - D.α i - D.α j))

private theorem innerAbsent (i j : Bool) :
    ¬ ∃ β, blockSucc₂ D i j Λ (lower (-Λ) j) rfl β = blockSucc D Λ i rfl emptyBlock := by
  intro h
  obtain ⟨β, hβ⟩ := h
  exact emptyAbsent j ⟨β, blockSucc_injective D Λ i rfl hβ⟩
example (i j : Bool) := probeOldEFunctor_comp₂_isZero D Sc m i j Λ
  (lower (-Λ) j) rfl (blockSucc D Λ i rfl emptyBlock) (innerAbsent i j)
  (M (-Λ - D.α j))
end ProbeWeightPairInductionConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightPairInduction
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
