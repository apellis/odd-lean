import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierPowers
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitRows
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace NonVacuity.InductionGridRouquierPowers
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private abbrev J (i : Bool) := oldContentAppend D Sc cut [] i
/-- The actual ordinary unit/dot family, in both moving parities and every power. -/
example (i : Bool) (n : ℕ) := inductionModuleUnitPower_eq (J i)
  (oldContentAppendDot_supernatural D Sc cut [] i) n
/-- The ordinary right counit/dot family is retained, separately from left normalization. -/
example (i : Bool) (n : ℕ) := inductionModuleCapPower_eq (J i)
  (oldContentAppendDot_supernatural D Sc cut [] i) n
/-- Each finite actual Rouquier unit pairs with the constructed prescribed inverse row. -/
example (i : Bool) (N : Superfunctor ℚ (OldContentCategory D Sc cut []) (SVec ℚ))
    (a r : Fin (contentUnitCount D cut i (0 : Multiset Bool))) :
    (SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := ℚ) (J i))
        (inductionModuleDot (J i) (oldContentAppendDot_supernatural D Sc cut [] i)) a.val).total N ≫
      contentMissingUnitRow D Sc cut [] i (by simp) N r = if a = r then 𝟙 N else 0 := by
  rw [inductionModuleUnitPower_eq, gridUnitColumnTransformation_total]
  exact contentMissingUnitColumn_row D Sc cut [] i (by simp) N a r
end NonVacuity.InductionGridRouquierPowers
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierPowers
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
