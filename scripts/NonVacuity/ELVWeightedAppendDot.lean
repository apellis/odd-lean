import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendDot
import NonVacuity.ELVWeightedAppendTensors

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedAppendDotConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private abbrev M := WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private abbrev R := weightedRestriction D Sc cut 8 M

/-- Both moving parities are checked with a mixed representable. -/
example (i : Bool) (w : OldCategory D Sc cut) :
    (appendWeightedModuleIso D Sc cut 8 i M).hom.total (Q.obj w) ∘ₗ
        CyclotomicCrossingTensor.actualInductionDot D Sc cut i R w =
      ((moduleInductionDot D Sc cut 8 i).app (D.parity i) M).app
        (D.parity i) (Q.obj w) ∘ₗ
        (appendWeightedModuleIso D Sc cut 8 i M).hom.total (Q.obj w) :=
  appendWeightedModuleIso_hom_dot D Sc cut 8 i M w

example (i : Bool) (w : OldCategory D Sc cut)
    (b : BalancedInduction.Obj (CyclotomicCrossingTensor.append D Sc cut i) R.toFunctor w) :
    (appendWeightedModuleIso D Sc cut 8 i M).hom.total (Q.obj w)
      (CyclotomicCrossingTensor.actualInductionDot D Sc cut i R w b) =
      ((moduleInductionDot D Sc cut 8 i).app (D.parity i) M).app
        (D.parity i) (Q.obj w)
        ((appendWeightedModuleIso D Sc cut 8 i M).hom.total (Q.obj w) b) :=
  LinearMap.congr_fun (appendWeightedModuleIso_hom_dot D Sc cut 8 i M w) b

example (i : Bool) :
    Q.map (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut i s) =
      truncatedAppendComponent D Sc cut 8 (dotE D Sc [i] 0) (Q.obj s) :=
  oldTruncateFunctor_map_appendDot D Sc cut 8 i s

/-- The odd moving dot has the negative twist, while the even colour in
the same connected datum has parity zero. -/
example :
    Q.map (twist ℚ 1 (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut true s)) =
      -Q.map (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut true s) := by
  have hp : CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut true s ∈
      parity (R := ℚ) _ _ 1 :=
    (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cut true).mem s
  rw [twist_of_mem 1 hp]
  simp
end WeightedAppendDotConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendDot
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
