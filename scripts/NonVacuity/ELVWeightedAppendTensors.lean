import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedAppendTensorsConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private abbrev M := WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private abbrev R := weightedRestriction D Sc cut 8 M
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i
private abbrev T (i : Bool) := truncatedAppend D Sc cut 8 [i]

/-- Both moving parities, mixed source word and arbitrary old output arrows. -/
example (i : Bool) (w : OldCategory D Sc cut) (g : (J i).obj s ⟶ w)
    (b : M.obj (Q.obj s)) :
    (appendWeightedModuleIso D Sc cut 8 i M).hom.total (Q.obj w)
      (BalancedInduction.tensor (J i) R.toFunctor s g b) =
      BalancedInduction.tensor (T i) M.toFunctor (Q.obj s) (Q.map g) b :=
  appendWeightedModuleIso_hom_tensor D Sc cut 8 i M s w g b

/-- The tensor with identity input vector is computed by the selected map. -/
example (i : Bool) (w : OldCategory D Sc cut) (g : (J i).obj s ⟶ w) :
    (appendWeightedModuleIso D Sc cut 8 i M).hom.total (Q.obj w)
      (BalancedInduction.tensor (J i) R.toFunctor s g (𝟙 (Q.obj s))) =
      BalancedInduction.tensor (T i) M.toFunctor (Q.obj s) (Q.map g) (𝟙 (Q.obj s)) :=
  appendWeightedModuleIso_hom_tensor D Sc cut 8 i M s w g (𝟙 (Q.obj s))

example (i : Bool) (b : M.obj (Q.obj s)) :
    (appendWeightedModuleIso D Sc cut 8 i M).hom.total (Q.obj ((J i).obj s))
      (BalancedInduction.unit (J i) R.toFunctor s b) =
      BalancedInduction.unit (T i) M.toFunctor (Q.obj s) b :=
  appendWeightedModuleIso_hom_unit D Sc cut 8 i M s b

/-- Vacuum input is included; no source-word inhabitation is required. -/
example (i : Bool) :
    let v : OldCategory D Sc cut := ⟨[]⟩
    let L := WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj v)
    (appendWeightedModuleIso D Sc cut 8 i L).hom.total (Q.obj ((J i).obj v))
      (BalancedInduction.unit (J i) (weightedRestriction D Sc cut 8 L).toFunctor
        v (𝟙 (Q.obj v))) =
      BalancedInduction.unit (T i) L.toFunctor (Q.obj v) (𝟙 (Q.obj v)) :=
  appendWeightedModuleIso_hom_unit D Sc cut 8 i _ ⟨[]⟩ (𝟙 _)
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
