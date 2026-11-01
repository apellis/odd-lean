import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendSuperfunctor
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace InductionUnitNaturalityConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev v : OldCategory D Sc cut := ⟨[false,true]⟩
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i
private abbrev H (i : Bool) := oldRepresentable D Sc cut ((J i).obj v)
private abbrev M (i : Bool) := (BalancedInduction.restriction (J i)).obj (H i)
private abbrev f (i : Bool) := (BalancedInduction.adjunctionCounit (J i)).app (H i)

example (i : Bool) (w : OldCategory D Sc cut) (g : (J i).obj v ⟶ w) (b : (M i).obj v) :
    (f i).total w (BalancedInduction.tensor (J i) (M i).toFunctor v g b) =
      (H i).map g ((f i).total ((J i).obj v)
        (BalancedInduction.unit (J i) (M i).toFunctor v b)) :=
  BalancedInduction.moduleMorphism_total_tensor_even (J i) (M i) (f i)
    (BalancedInduction.adjunctionCounit_mem (J i) (H i)) v w g b

example (i : Bool) :
    (f i).total ((J i).obj v)
      (BalancedInduction.tensor (J i) (M i).toFunctor v (𝟙 _) (𝟙 ((J i).obj v))) =
      (H i).map (𝟙 ((J i).obj v))
        ((f i).total ((J i).obj v)
          (BalancedInduction.unit (J i) (M i).toFunctor v (𝟙 ((J i).obj v)))) :=
  BalancedInduction.moduleMorphism_total_tensor_even (J i) (M i) (f i)
    (BalancedInduction.adjunctionCounit_mem (J i) (H i)) v ((J i).obj v) (𝟙 _) (𝟙 _)
end InductionUnitNaturalityConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitNaturality
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
