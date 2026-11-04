import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightVacuumDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.QuiverHecke
open ELVOld CyclotomicAction
namespace NonVacuity.ELVProbeWeightVacuumDot
private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private def raised (i : Bool) : Bool → ℤ := -Λ + D.α i
private theorem edge (i : Bool) : -Λ + D.α i = raised i := rfl
example (i : Bool) (N : ProbeEvaluatedModules D Sc m []) :=
  WeightTensorVacuum.upperLoop_dot D Sc m [] i (List.Perm.refl [i]) N
example (i : Bool) (N : ProbeEvaluatedModules D Sc m []) :=
  WeightTensorVacuum.forgetEmpty_upper_dot D Sc m [] rfl i N
example (i : Bool) := WeightTensorVacuum.vacuumLoopDot_source D Sc m Λ i (edge i)
example (i : Bool) := ProbeVacuumCap.moduleDot_odd_polynomial D Sc m i rfl
example : probeOldVacuumVector D Sc m ≠ 0 := probeOldVacuumVector_ne_zero D Sc m
end NonVacuity.ELVProbeWeightVacuumDot
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightVacuumDot
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations"
