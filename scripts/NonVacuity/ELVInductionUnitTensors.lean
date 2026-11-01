import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientComparison
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace InductionUnitTensorsConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev v : OldCategory D Sc cut := ⟨[false,true]⟩
private abbrev M := oldRepresentable D Sc cut v
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i
private abbrev Q := oldTruncateFunctor D Sc cut 8

example (i : Bool) (b : M.obj v) :
    ((BalancedInduction.inductionComp (J i) Q).hom.app M).total (Q.obj ((J i).obj v))
      (BalancedInduction.unit Q (BalancedInduction.induced (J i) M).toFunctor
        ((J i).obj v) (BalancedInduction.unit (J i) M.toFunctor v b)) =
      BalancedInduction.unit (J i ⋙ Q) M.toFunctor v b :=
  BalancedInduction.inductionComp_hom_total_unit (J i) Q M v b

example (i : Bool) (b : M.obj v) :
    ((BalancedInduction.inductionComp (J i) Q).inv.app M).total ((J i ⋙ Q).obj v)
      (BalancedInduction.unit (J i ⋙ Q) M.toFunctor v b) =
      BalancedInduction.unit Q (BalancedInduction.induced (J i) M).toFunctor
        ((J i).obj v) (BalancedInduction.unit (J i) M.toFunctor v b) :=
  BalancedInduction.inductionComp_inv_total_unit (J i) Q M v b

private def f : M ⟶ M := -𝟙 M
private theorem f_even : f ∈ parity (R := ℚ) _ _ 0 :=
  Submodule.neg_mem _ (id_mem M)

example (i : Bool) (b : M.obj v) :
    (BalancedInduction.moduleMap (J i) f).total ((J i).obj v)
      (BalancedInduction.tensor (J i) M.toFunctor v (𝟙 _) b) =
      BalancedInduction.tensor (J i) M.toFunctor v (𝟙 _) (f.app 0 v b) :=
  BalancedInduction.moduleMap_total_tensor_even (J i) f f_even ((J i).obj v) v (𝟙 _) b
end InductionUnitTensorsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitTensors
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
