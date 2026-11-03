import OddMath.QuiverHecke.CyclotomicAction.ELVProbeExtensionParity
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ELVProbeExtensionParity
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private theorem row_parity (i : Bool) :
    (probeCutoff D m i - 1) • D.parity i = (1 : ZMod 2) := by cases i <;> decide
private abbrev N := probeOldVacuumRegular D Sc m
private abbrev J := oldContentInclusion D Sc (probeCutoff D m) []
private abbrev L := BalancedInduction.induced J N
private abbrev t := OldContentCategory.obj (probeOldVacuumObject D Sc m)
private abbrev V (i : Bool) := mateTargetSpace D Sc (probeCutoff D m) i L t

open ProbeExtensionCoefficient

private theorem odd_row (i : Bool) :
    SVec.ofHom (functional D Sc m i (positive i)) ∈
      parity (R := ℚ) (V i) (SVec.unit : SVec ℚ) 1 := by
  simpa only [row_parity] using functional_mem D Sc m i (positive i)

/-- For both positive odd probes, a nonzero odd vector is extracted to one. -/
example (i : Bool) : ∃ z : V i,
    z ≠ 0 ∧ z ∈ (V i).part 1 ∧ functional D Sc m i (positive i) z = (1 : ℚ) := by
  have h := functional_dot_window D Sc m i (positive i) (probeCutoff D m i - 1)
    (by have hp := positive i; omega) (1 : ℚ)
  rw [ite_eq_left (by have hp := positive i; omega)] at h
  obtain ⟨z, hz⟩ : ∃ z : V i, functional D Sc m i (positive i) z = (1 : ℚ) := ⟨_, h⟩
  have hodd := SVec.apply_proj_of_mem (odd_row i) 1 z
  have hrow : functional D Sc m i (positive i) ((V i).proj 1 z) = (1 : ℚ) := by
    simp only [SVec.ofHom_apply, show (1 : ZMod 2) + 1 = 0 by decide, hz] at hodd
    exact hodd.trans (SVec.unit_proj_zero_apply (1 : ℚ))
  refine ⟨(V i).proj 1 z, ?_, SVec.proj_mem_part (V i) 1 z, hrow⟩
  intro h0
  rw [h0, map_zero] at hrow
  norm_num at hrow

example (z : L.obj t) : z ∈ (L.obj t).part 0 := extension_empty_even D Sc m z

end NonVacuity.ELVProbeExtensionParity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeExtensionParity
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
