import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingCapCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ELVProbeMissingCapCoordinates
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private def regular : ProbeEvaluatedModules D Sc m [] :=
  ⟨probeOldVacuumRegular D Sc m, probeOldModule_evaluatesCoefficients D m Sc [] _⟩
private theorem positive (i : Bool) :
    0 < contentUnitCount D (probeCutoff D m) i (([] : List Bool) : Multiset Bool) := by
  rw [VacuumCoefficient.count]
  cases i <;> decide

example (i : Bool) := probeMissingStoredLoc_cap_eq D Sc m [] i
  (List.Perm.refl [i]) (by simp) (positive i)
example (i : Bool) := probeMissingStoredLoc_cap_chart D Sc m [] i
  (List.Perm.refl [i]) (by simp) (positive i)
example (i : Bool) := probeMissingStoredLoc_cap_total_native D Sc m [] i
  (List.Perm.refl [i]) (by simp) (positive i) regular
example (i : Bool) := probeMissingBoundary_regular_cap D Sc m i
  (by cases i <;> decide)
example : probeOldVacuumVector D Sc m ≠ 0 := probeOldVacuumVector_ne_zero D Sc m

end NonVacuity.ELVProbeMissingCapCoordinates
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingCapCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations"
