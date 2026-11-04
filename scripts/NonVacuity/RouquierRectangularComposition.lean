import OddMath.SKM.RouquierRectangularComposition
import StringDiagrams.Super.SCat
import StringDiagrams.Super.Superalgebra
import Lean.Util.CollectAxioms

/-! Nonzero scalar crossings in the identity superfunctor of the rational
unit supercategory. Both right adjunctions, homogeneity hypotheses, and
input maps are constructed. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierRectangularComposition
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


private def t₂ : E ≫ E ⟶ E ≫ E := (2 : ℚ) • 𝟙 E
private def t₃ : E ≫ E ⟶ E ≫ E := (3 : ℚ) • 𝟙 E
private theorem h₂ : t₂ ∈ parity (R := ℚ) _ _ 0 :=
  Submodule.smul_mem _ _ (id_mem E)
private theorem h₃ : t₃ ∈ parity (R := ℚ) _ _ 0 :=
  Submodule.smul_mem _ _ (id_mem E)

example := crossMate_eq_rectangularMate A A E E t₂
example := crossMate_pitchfork_cap A A E E t₂
example := crossMate_mem A A E E t₂ h₂
example := crossMate_comp_crossMate A A A h₂ h₃

example : rectangularMateLinearMap A A E E (t₂ + t₃) =
    rectangularMate A A E E t₂ + rectangularMate A A E E t₃ :=
  map_add (rectangularMateLinearMap A A E E) t₂ t₃

example : t₂.total () ≠ 0 := by
  change (2 : ℚ) * 1 + 2 * 0 ≠ 0
  norm_num

example : t₃.total () ≠ 0 := by
  change (3 : ℚ) * 1 + 3 * 0 ≠ 0
  norm_num

end NonVacuity.RouquierRectangularComposition

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierRectangularComposition
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
