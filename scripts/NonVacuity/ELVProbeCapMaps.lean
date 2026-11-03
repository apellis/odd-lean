import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapMaps
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVProbeCapMaps
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
example (i : Bool) : ProbeVacuumCap.cap D Sc m i (positive i) ≠ 0 :=
  ProbeVacuumCap.cap_ne_zero D Sc m i (positive i)
example (i : Bool) : Function.Surjective (ProbeVacuumCap.groundRow D Sc m i (positive i)) :=
  ProbeVacuumCap.groundRow_surjective D Sc m i (positive i)
private theorem degree (i : Bool) :
    (probeCutoff D m i - 1) • D.parity i = (1 : ZMod 2) := by cases i <;> decide
example (i : Bool) : ProbeVacuumCap.cap D Sc m i (positive i) ∈ parity (R := ℚ) _ _ 1 := by
  simpa only [degree] using ProbeVacuumCap.cap_mem D Sc m i (positive i)

/-- The native scalar row is occupied on a nonzero odd vector of its actual source. -/
example (i : Bool) : ∃ z : (ProbeVacuumCap.source D Sc m i).obj (probeOldVacuumObject D Sc m),
    z ≠ 0 ∧ z ∈ ((ProbeVacuumCap.source D Sc m i).obj (probeOldVacuumObject D Sc m)).part 1 ∧
      ProbeVacuumCap.groundRow D Sc m i (positive i) z = (1 : ℚ) := by
  obtain ⟨z, hz⟩ := ProbeVacuumCap.groundRow_surjective D Sc m i (positive i) (1 : ℚ)
  have hm := ProbeVacuumCap.groundRow_mem D Sc m i (positive i)
  rw [degree] at hm
  have hp := SVec.apply_proj_of_mem hm 1 z
  simp only [SVec.ofHom_apply, show (1 : ZMod 2) + 1 = 0 by decide, hz] at hp
  have h1 : ProbeVacuumCap.groundRow D Sc m i (positive i)
      (((ProbeVacuumCap.source D Sc m i).obj (probeOldVacuumObject D Sc m)).proj 1 z) = (1 : ℚ) :=
    hp.trans (SVec.unit_proj_zero_apply (1 : ℚ))
  refine ⟨_, ?_, SVec.proj_mem_part _ 1 z, h1⟩
  intro h0
  rw [h0, map_zero] at h1
  norm_num at h1
end NonVacuity.ELVProbeCapMaps
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapMaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
