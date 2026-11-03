import OddMath.QuiverHecke.CyclotomicAction.ELVProbeExtensionRows
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ELVProbeExtensionRows
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide

open ProbeExtensionCoefficient

example (c : ℚ) : scalarCoordinate D Sc m (scalarUnit D Sc m c) = c :=
  scalarCoordinate_unit D Sc m c

/-- Every scalar is recovered from an explicitly dotted unit of the prescribed coend. -/
private theorem row_surjective (i : Bool) : Function.Surjective (functional D Sc m i (positive i)) := by
  intro c
  have h := functional_dot_window D Sc m i (positive i) (probeCutoff D m i - 1)
    (by have hp := positive i; omega) c
  rw [ite_eq_left (by have hp := positive i; omega)] at h
  exact ⟨_, h⟩

example (i : Bool) : Function.Surjective (functional D Sc m i (positive i)) := row_surjective i

/-- These are occupied literal full-old append coends, for probe levels one and two. -/
example (i : Bool) : ∃ z, z ≠ 0 ∧ functional D Sc m i (positive i) z = (1 : ℚ) := by
  obtain ⟨z, hz⟩ := row_surjective i (1 : ℚ)
  refine ⟨z, ?_, hz⟩
  intro h0
  rw [h0, map_zero] at hz
  norm_num at hz

end NonVacuity.ELVProbeExtensionRows

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeExtensionRows
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
