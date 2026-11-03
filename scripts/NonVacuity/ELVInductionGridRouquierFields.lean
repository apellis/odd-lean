import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierFields
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixEntries
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace NonVacuity.InductionGridRouquierFields
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private abbrev J (i : Bool) := oldContentAppend D Sc cut [] i
private abbrev K (i : Bool) := oldContentAppend D Sc cut [i] i
/-- The actual chosen old-content right adjunction retains both triangles. -/
example (i : Bool) := (inductionModuleAdjunction (k := ℚ) (J i)).left_triangle
example (i : Bool) := (inductionModuleAdjunction (k := ℚ) (J i)).right_triangle
/-- Actual signed old dots and negative physical crossings have both moving parities. -/
example (i : Bool) := inductionModuleDot_mem (J i) (oldContentAppendDot_supernatural D Sc cut [] i)
example (i : Bool) := inductionModuleCross_mem (J i) (K i)
  (oldContentMatrixCross_supernatural D Sc cut [] i)
/-- The entire given cup-crossing-cap equals the prescribed matrix principal field,
with no independently supplied mate or inverse compatibility. -/
example (i : Bool) :
    SKM.rouquierMate (inductionModuleAdjunction (k := ℚ) (J i))
      (inductionModuleAdjunction (k := ℚ) (K i))
      (inductionModuleCross (J i) (K i) (oldContentMatrixCross_supernatural D Sc cut [] i)) =
    gridMateTransformation (J i) (K i) (oldContentMatrixCross_supernatural D Sc cut [] i) :=
  inductionModuleMate_eq_grid (J i) (K i) (oldContentMatrixCross_supernatural D Sc cut [] i)
/-- The crossing minus is retained on each actual module, including the odd colour. -/
example (i : Bool) (N : Superfunctor ℚ (OldContentCategory D Sc cut []) (SVec ℚ)) :
    (inductionModuleCross (J i) (K i) (oldContentMatrixCross_supernatural D Sc cut [] i)).app
        (D.parity i) N =
      -gridDoubleCrossComponent (J i) (K i) (oldContentMatrixCross_supernatural D Sc cut [] i) N := by
  simpa only [ite_true] using inductionModuleCross_app (J i) (K i)
    (oldContentMatrixCross_supernatural D Sc cut [] i) (D.parity i) N
end NonVacuity.InductionGridRouquierFields
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierFields
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
