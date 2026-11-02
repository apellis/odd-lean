import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendCrossing
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedAppendCrossingConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i

/-- The same prescribed generator occurs for both moving parities. -/
example (i : Bool) := oldTruncateFunctor_map_equalCross D Sc cut 8 i s
example (i : Bool) := truncatedEqualCrossComponent_heq D Sc cut 8 i (Q.obj s)
example (i : Bool) := truncatedEqualCross_supernatural D Sc cut 8 i
example (i : Bool) (w : OldCategory D Sc cut) :=
  pairWeightedModuleIso_hom_crossing D Sc cut 8 i M w
example (i : Bool) (w : OldCategory D Sc cut) :=
  pairWeightedModuleIso_hom_signedCrossing D Sc cut 8 i M w

/-- The odd crossing has odd parity, and its extra sign remains explicit. -/
example : D.parity true * D.parity true = 1 := by decide
example : D.parity false * D.parity false = 0 := by decide
example : (sign ℚ (D.parity true * D.parity true) : ℚ) = -1 := by decide

private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def vacuumModule : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)
example (i : Bool) :=
  pairWeightedModuleIso_hom_signedCrossing D Sc cut 8 i vacuumModule vacuum
end WeightedAppendCrossingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendCrossing
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
