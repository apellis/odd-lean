import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMateComparison
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedMateComparisonConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i

/-- Both parities use the fixed ordered old-module mate and chosen source comparison. -/
example (i : Bool) (w : OldCategory D Sc cut) := appendWeightedModuleIso_hom_mate D Sc cut 8 i M w
example (i : Bool) (w : OldCategory D Sc cut) (g : (J i).obj s ⟶ w)
    (b : M.obj (Q.obj ((J i).obj s))) :=
  weightedOldMateLinear_tensor D Sc cut 8 i M s w g b
example (i : Bool) (w : OldCategory D Sc cut) (g : (J i).obj s ⟶ w)
    (b : M.obj (Q.obj ((J i).obj s))) :=
  weightedAppendSourceLinear_tensor D Sc cut 8 i
    ((BalancedInduction.restriction (J i)).obj (weightedRestriction D Sc cut 8 M))
    ((BalancedInduction.restriction (truncatedAppend D Sc cut 8 [i])).obj M)
    (weightedAppendRestrictionIso D Sc cut 8 i M).inv s w g b
example (i : Bool) := oldTruncateFunctor_map_append D Sc cut 8 i s s (𝟙 s)
/-- The odd crossing has odd parity, and its extra sign remains explicit. -/
example : D.parity true * D.parity true = 1 := by decide
example : D.parity false * D.parity false = 0 := by decide
example : (sign ℚ (D.parity true * D.parity true) : ℚ) = -1 := by decide

private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def vacuumModule : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)
example (i : Bool) :=
  appendWeightedModuleIso_hom_mate D Sc cut 8 i vacuumModule vacuum
end WeightedMateComparisonConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMateComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
