import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedAppendTensorsConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i

/-- Both moving parities, mixed source word and arbitrary old output arrows. -/
example (i : Bool) (w : OldCategory D Sc cut) (g : (J i).obj s ⟶ w)
    (b : M.obj (Q.obj s)) :=
  appendWeightedModuleIso_hom_tensor D Sc cut 8 i M s w g b

/-- The tensor with identity input vector is computed by the selected map. -/
example (i : Bool) (w : OldCategory D Sc cut) (g : (J i).obj s ⟶ w) :=
  appendWeightedModuleIso_hom_tensor D Sc cut 8 i M s w g (𝟙 (Q.obj s))

example (i : Bool) (b : M.obj (Q.obj s)) :=
  appendWeightedModuleIso_hom_unit D Sc cut 8 i M s b

private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def vacuumModule : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)

/-- The literal vacuum unit is included for both moving parities. -/
example (i : Bool) :=
  appendWeightedModuleIso_hom_unit D Sc cut 8 i vacuumModule vacuum (𝟙 (Q.obj vacuum))
end WeightedAppendTensorsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendTensors
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
