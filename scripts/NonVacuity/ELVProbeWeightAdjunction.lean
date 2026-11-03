import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightAdjunction
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeWeightAdjunctionConsumer
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

example (i : Bool) := probeOldWeightAdjunction D Sc m i Λ (x := w []) rfl
example (i : Bool) := (probeOldWeightAdjunction D Sc m i Λ (x := w []) rfl).left_triangle_components (M (w []))
example (i : Bool) := (probeOldWeightAdjunction D Sc m i Λ (x := w [i,!i]) rfl).right_triangle_components
  (M (w [i,!i] + D.α i))
example (i : Bool) := (probeOldWeightAdjunction D Sc m i Λ (x := w []) rfl).unit.naturality (oddInput (w []))
example (i : Bool) := (probeOldWeightAdjunction D Sc m i Λ (x := w []) rfl).counit.naturality
  (oddInput (w [] + D.α i))
example (i : Bool) := probeOldWeightUnit_mem D Sc m i Λ (x := w []) rfl (M (w []))
example (i : Bool) := probeOldWeightCounit_mem D Sc m i Λ (x := w []) rfl (M (w [] + D.α i))
example (i : Bool) := (probeOldActionAdjunction D Sc m i Λ (x := w []) rfl).left_triangle
example (i : Bool) := (probeOldActionAdjunction D Sc m i Λ (x := w []) rfl).right_triangle
example (i : Bool) := (probeOldActionAdjunction D Sc m i Λ (x := w []) rfl).unit_mem
example (i : Bool) := (probeOldActionAdjunction D Sc m i Λ (x := w []) rfl).counit_mem
example (i : Bool) := probeOldWeight_right_triangle D Sc m i Λ rfl (base [i,!i])
  (M (w [i,!i] + D.α i))
example (i : Bool) := probeOldWeight_left_triangle D Sc m i Λ rfl (base [i,!i]) (M (w [i,!i]))
end ProbeWeightAdjunctionConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightAdjunction
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
