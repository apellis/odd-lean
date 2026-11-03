import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumRows
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVProbeVacuumRows
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem cutoff_false : probeCutoff D m false = 2 := rfl
private theorem cutoff_true : probeCutoff D m true = 4 := rfl
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide

open ProbeVacuumCoefficient

example (c : ℚ) : scalarCoordinate D Sc m (scalarUnit D Sc m c) = c :=
  scalarCoordinate_unit D Sc m c

example (i : Bool) (a : ℕ) (ha : a < probeCutoff D m i) (c : ℚ) :
    functional D Sc m i (positive i) ((appendDot D Sc m i ^ a) (appendUnit D Sc m i c)) =
      if a + 1 = probeCutoff D m i then c else 0 :=
  functional_dot_window D Sc m i (positive i) a ha c

private theorem top_false :
    functional D Sc m false (positive false)
      (appendDot D Sc m false (appendUnit D Sc m false 1)) = 1 := by
  have h := functional_dot_window D Sc m false (positive false) 1 (by rw [cutoff_false]; omega) 1
  simpa only [pow_one, cutoff_false, ↓reduceIte] using h

example :
    functional D Sc m true (positive true)
      ((appendDot D Sc m true ^ 3) (appendUnit D Sc m true (3 : ℚ))) = 3 := by
  have h := functional_dot_window D Sc m true (positive true) 3 (by rw [cutoff_true]; omega) (3 : ℚ)
  simpa only [cutoff_true, ↓reduceIte] using h

example : appendDot D Sc m false (appendUnit D Sc m false 1) ≠ 0 := by
  intro hz
  have h := congrArg (functional D Sc m false (positive false)) hz
  rw [top_false, map_zero] at h
  norm_num at h

end NonVacuity.ELVProbeVacuumRows

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumRows
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
