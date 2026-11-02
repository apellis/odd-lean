import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedDoubleAppend
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedDoubleAppendConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i

example (i j : Bool) := doubleInduced_killsWeightedCoefficients D Sc cut 8 i j M
example (i j : Bool) := (weightedInductionFlattening D Sc cut 8 i j M).hom_inv_id
example (i j : Bool) := (weightedInductionFlattening D Sc cut 8 i j M).inv_hom_id
example (i j : Bool) := weightedInductionFlattening_hom_mem D Sc cut 8 i j M
example (i j : Bool) := (doubleWeightedModuleIso D Sc cut 8 i j M).hom_inv_id
example (i j : Bool) := (doubleWeightedModuleIso D Sc cut 8 i j M).inv_hom_id
example (i j : Bool) := doubleWeightedModuleIso_flatten D Sc cut 8 i j M

private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def vacuumModule : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)
example (i j : Bool) := doubleWeightedModuleIso_flatten D Sc cut 8 i j vacuumModule
end WeightedDoubleAppendConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedDoubleAppend
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
