import OddMath.SKM.RouquierRectangularMonomials
import StringDiagrams.Super.SCat
import StringDiagrams.Super.Superalgebra
import Lean.Util.CollectAxioms

/-! Nonzero scalar crossings in the identity superfunctor of the rational
unit supercategory. Both right adjunctions, homogeneity hypotheses, and
input maps are constructed. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierRectangularMonomials
private abbrev C := SCat.of ℚ (UnitSupercat ℚ)
private abbrev E : C ⟶ C := 𝟙 C
private def A : SuperAdjunction (k := ℚ) E E where
  unit := 𝟙 E
  counit := 𝟙 E
  unit_mem := id_mem _
  counit_mem := id_mem _
  left_triangle := by
    change (𝟙 E) ≫ (𝟙 E) ▷ E ≫ (𝟙 E) ≫ E ◁ (𝟙 E) ≫ (𝟙 E) = 𝟙 E
    simp only [TwoSupercategory.id_whiskerRight (R := ℚ),
      TwoSupercategory.whiskerLeft_id (R := ℚ), Category.id_comp]
    change (𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E) = 𝟙 E
    simp only [Category.id_comp]
  right_triangle := by
    change (𝟙 E) ≫ E ◁ (𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E) ▷ E ≫ (𝟙 E) =
      𝟙 E
    simp only [TwoSupercategory.id_whiskerRight (R := ℚ),
      TwoSupercategory.whiskerLeft_id (R := ℚ), Category.id_comp]
    change (𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E) = 𝟙 E
    simp only [Category.id_comp]


example := rectangularMate_associator E A A

private def x : E ⟶ E := (2 : ℚ) • 𝟙 E
private def y : E ⟶ E := (3 : ℚ) • 𝟙 E
private def z : E ⟶ E := (5 : ℚ) • 𝟙 E

example := rectangularMate_separated E A A x y z

example : (x ≫ y ≫ z).total () ≠ 0 := by
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  change ((5 * 1 + 5 * 0 : ℚ) * (3 * 1 + 3 * 0)) * (2 * 1 + 2 * 0) ≠ 0
  norm_num

end NonVacuity.RouquierRectangularMonomials

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierRectangularMonomials
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
