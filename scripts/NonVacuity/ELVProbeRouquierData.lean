import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierData
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeRouquierDataConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 6 else 5
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

example (i : Bool) := probeOldRouquierData_square D Sc m Λ i (a := w [i,!i]) rfl rfl
example (i : Bool) := probeOldRouquierData_braid D Sc m Λ i (a := w [i,!i]) rfl rfl rfl
example (i : Bool) := probeOldRouquierData_dot_isUnit D Sc m Λ i (x := w []) rfl
example (i : Bool) := probeOldRouquierDataAdjunction D Sc m Λ i (x := w []) rfl
example (i : Bool) : (probeOldRouquierData D Sc m Λ).E i (x := w []) rfl =
    probeOldE D Sc m i Λ rfl := rfl
example (i : Bool) : (probeOldRouquierData D Sc m Λ).dot i (x := w []) rfl =
    probeOldActionDot D Sc m i Λ rfl := rfl
example (i : Bool) := probeOldActionCross_equal D Sc m Λ i (a := w [i,!i]) rfl rfl
example := probeOldActionCross_distinct D Sc m Λ true false (by decide)
  (a := w [false,true]) (b := w [false,true] + D.α false)
  (c := w [false,true] + D.α true) rfl rfl rfl (by
    simp only [add_assoc, add_comm (D.α true) (D.α false)])
example := probeOldActionCross_distinct D Sc m Λ false true (by decide)
  (a := w [true,false]) (b := w [true,false] + D.α true)
  (c := w [true,false] + D.α false) rfl rfl rfl (by
    simp only [add_assoc, add_comm (D.α false) (D.α true)])
example (i : Bool) := probeOldRouquierData_braid D Sc m Λ i
  (lower (-Λ - D.α i - D.α i) i) (lower (-Λ - D.α i) i) (lower (-Λ) i)
example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide)
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ProbeRouquierDataConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierData
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
