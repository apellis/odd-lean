import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendAdjunction
import NonVacuity.ELVWeightedAppendTensors

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedAppendAdjunctionConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i
private abbrev T (i : Bool) := truncatedAppend D Sc cut 8 [i]

example (i : Bool) :
    (weightedAppendRestrictionIso D Sc cut 8 i M).hom ≫
      (weightedAppendRestrictionIso D Sc cut 8 i M).inv = 𝟙 _ :=
  (weightedAppendRestrictionIso D Sc cut 8 i M).hom_inv_id

example (i : Bool) :
    (weightedAppendRestrictionIso D Sc cut 8 i M).inv ≫
      (weightedAppendRestrictionIso D Sc cut 8 i M).hom = 𝟙 _ :=
  (weightedAppendRestrictionIso D Sc cut 8 i M).inv_hom_id

example (i : Bool) :
    (weightedAppendRestrictionIso D Sc cut 8 i M).hom ∈ parity (R := ℚ) _ _ 0 :=
  weightedAppendRestrictionIso_hom_mem D Sc cut 8 i M

example (i : Bool) (f : M ⟶ M) :
    (BalancedInduction.restriction Q).map ((BalancedInduction.restriction (T i)).map f) ≫
        (weightedAppendRestrictionIso D Sc cut 8 i M).hom =
      (weightedAppendRestrictionIso D Sc cut 8 i M).hom ≫
        (BalancedInduction.restriction (J i)).map ((BalancedInduction.restriction Q).map f) :=
  weightedAppendRestrictionIso_naturality D Sc cut 8 i M f

example (i : Bool) :
    ((weightedAppendRestrictionNaturalIso D Sc cut 8 i).app M).hom ≫
      ((weightedAppendRestrictionNaturalIso D Sc cut 8 i).app M).inv = 𝟙 _ :=
  ((weightedAppendRestrictionNaturalIso D Sc cut 8 i).app M).hom_inv_id

/-- Both moving parities and arbitrary output words retain the selected counit. -/
example (i : Bool) (w : OldCategory D Sc cut) :=
  appendWeightedModuleIso_hom_counit D Sc cut 8 i M w

private abbrev inputModule (i : Bool) :=
  weightedRestriction D Sc cut 8 ((BalancedInduction.restriction (T i)).obj M)

example (i : Bool) (w : OldCategory D Sc cut)
    (b : BalancedInduction.Obj (J i) (inputModule i).toFunctor w) :=
  LinearMap.congr_fun (appendWeightedModuleIso_hom_counit D Sc cut 8 i M w) b
end WeightedAppendAdjunctionConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendAdjunction
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
