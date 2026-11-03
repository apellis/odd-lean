import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDotUnit
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeWeightDotUnitConsumer
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

/-- The weight source really contains the regular probe vacuum, with its nonzero PBW vector. -/
example : M (w []) (base []) = N [] := by
  change N ((0 : Multiset Bool).toList) = N []
  rw [Multiset.toList_zero]
example : (N []).obj = probeOldVacuumRegular D Sc m := rfl
example : probeOldVacuumVector D Sc m ≠ 0 := probeOldVacuumVector_ne_zero D Sc m

/-- The corresponding actual append coends are occupied in both moving parities. -/
example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide)

/-- Both moving parities have the exact whole signed-dot unit. -/
example (i : Bool) := probeOldActionDot_isUnit D Sc m i Λ (x := w []) rfl
example (i : Bool) := probeOldActionDotIso_inv_mem D Sc m i Λ (x := w []) rfl
example (i : Bool) := probeOldActionDotIso_hom D Sc m i Λ (x := w []) rfl
example (i : Bool) := (probeOldActionDotIso D Sc m i Λ (x := w []) rfl).hom_inv_id
example (i : Bool) := (probeOldActionDotIso D Sc m i Λ (x := w []) rfl).inv_hom_id

/-- The nonempty mixed source and its prescribed stored-target map are retained. -/
example (i : Bool) := probeOldBlockDot_isUnit D Sc m i Λ rfl (base [i,!i])
example (i : Bool) := probeOldActionDot_total_blockSucc D Sc m i Λ rfl
  (M (w [i,!i])) (base [i,!i])
example (i : Bool) := probeOldActionDot_component_isUnit D Sc m i Λ rfl
  (M (w [i,!i])) (blockSucc D Λ i rfl (base [i,!i]))
example (i : Bool) := probeOldActionDot_isUnit D Sc m i Λ (x := w [i,!i]) rfl

/-- The same whole theorem includes the specified absent vacuum component. -/
example (i : Bool) := emptyAbsent i
example (i : Bool) := probeOldActionDot_component_isUnit D Sc m i Λ (lower (-Λ) i)
  (M (-Λ - D.α i)) emptyBlock
example (i : Bool) := probeOldWeightDotComponent_naturality D Sc m i Λ rfl (D.parity i)
  (base []) (oddInput (w [])) (oddInput_mem (w []))
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ProbeWeightDotUnitConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDotUnit
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
