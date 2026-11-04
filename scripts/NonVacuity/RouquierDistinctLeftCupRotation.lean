import OddMath.SKM.RouquierDistinctLeftCupRotation
import StringDiagrams.Super.SCat
import StringDiagrams.Super.Superalgebra
import Lean.Util.CollectAxioms

/-! A nonzero identity-superfunctor fixture discharges every cup-pitchfork
and inverse hypothesis with scalar two. Additional API tests retain the
odd cup/odd crossing sign and the reciprocal scalar. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierDistinctLeftCupRotation
variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
  {c₀ m a₁ b₁ : B} {Ed : c₀ ⟶ m} {Fd : m ⟶ c₀} {Ec : m ⟶ b₁}
  {Eb : c₀ ⟶ a₁} {Ea : a₁ ⟶ b₁} {Fa : b₁ ⟶ a₁}
  (Ad : ShiftedSuperAdjunction (k := ℚ) Fd Ed 1)
  (Aa : ShiftedSuperAdjunction (k := ℚ) Fa Ea 1)
  (T : Ed ≫ Ec ⟶ Eb ≫ Ea) (l : Ec ≫ Fa ⟶ Fd ≫ Eb)
  (s : Fd ≫ Eb ⟶ Ec ≫ Fa) (hl : l ∈ parity (R := ℚ) _ _ 1)
  (hls : l ≫ s = 𝟙 _) (hsl : s ≫ l = 𝟙 _)
  (hcup : (leftUnitor Ec).inv ≫ Ad.unit ▷ Ec ≫ (associator Fd Ed Ec).hom ≫
    Fd ◁ T ≫ (associator Fd Eb Ea).inv =
    (2 : ℚ) • ((rightUnitor Ec).inv ≫ Ec ◁ Aa.unit ≫
      (associator Ec Fa Ea).inv ≫ l ▷ Ea))

example : leftCrossMate Ad Aa T = (-2 : ℚ) • l := by
  simpa using leftCrossMate_eq_of_cup_pitchfork Ad Aa T l hl (2 : ℚ) hcup

private def two : ℚˣ := ⟨2, 1 / 2, by norm_num, by norm_num⟩

example : leftCrossMate Ad Aa T ≫ ((-1 / 2 : ℚ) • s) = 𝟙 _ ∧
    ((-1 / 2 : ℚ) • s) ≫ leftCrossMate Ad Aa T = 𝟙 _ := by
  simpa [two, div_eq_mul_inv] using
    leftCrossMate_inv_products_of_cup_pitchfork Ad Aa T l s hl two hls hsl hcup

example : IsIso (leftCrossMate Ad Aa T) := by
  have : IsIso l := ⟨⟨s, hls, hsl⟩⟩
  exact leftCrossMate_isIso_of_cup_pitchfork Ad Aa T l hl two hcup

end NonVacuity.RouquierDistinctLeftCupRotation

namespace NonVacuity.RouquierDistinctLeftCupRotationConcrete
private abbrev C := SCat.of ℚ (UnitSupercat ℚ)
private abbrev E : C ⟶ C := 𝟙 C
private def A : ShiftedSuperAdjunction (k := ℚ) E E 0 where
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
      koszulSign 0 0 • (𝟙 E)
    simp only [TwoSupercategory.id_whiskerRight (R := ℚ),
      TwoSupercategory.whiskerLeft_id (R := ℚ), Category.id_comp,
      koszulSign_zero_left, one_smul]
    change (𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E) = 𝟙 E
    simp only [Category.id_comp]

private def T : E ≫ E ⟶ E ≫ E := (2 : ℚ) • 𝟙 E
private def two : ℚˣ := ⟨2, 1 / 2, by norm_num, by norm_num⟩
private theorem cup :
    (leftUnitor E).inv ≫ A.unit ▷ E ≫ (associator E E E).hom ≫
      E ◁ T ≫ (associator E E E).inv =
    (2 : ℚ) • ((rightUnitor E).inv ≫ E ◁ A.unit ≫
      (associator E E E).inv ≫ (𝟙 E) ▷ E) := by
  change (𝟙 E) ≫ (𝟙 E) ▷ E ≫ (𝟙 E) ≫ E ◁ ((2 : ℚ) • 𝟙 E) ≫ (𝟙 E) =
    (2 : ℚ) • ((𝟙 E) ≫ E ◁ (𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E) ▷ E)
  simp only [TwoSupercategory.whiskerLeft_smul (R := ℚ),
    TwoSupercategory.id_whiskerRight (R := ℚ), TwoSupercategory.whiskerLeft_id (R := ℚ),
    Category.id_comp]
  change (𝟙 E) ≫ (𝟙 E) ≫ ((2 : ℚ) • 𝟙 E) ≫ (𝟙 E) =
    (2 : ℚ) • ((𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E))
  simp only [Category.id_comp, Category.comp_id]

example : leftCrossMate A A T = (2 : ℚ) • 𝟙 E := by
  simpa using leftCrossMate_eq_of_cup_pitchfork A A T (𝟙 E) (id_mem E) (2 : ℚ) cup

example : leftCrossMate A A T ≫ ((1 / 2 : ℚ) • 𝟙 E) = 𝟙 E ∧
    ((1 / 2 : ℚ) • 𝟙 E) ≫ leftCrossMate A A T = 𝟙 E := by
  have h := leftCrossMate_inv_products_of_cup_pitchfork A A T
    (𝟙 E) (𝟙 E) (id_mem E) two (Category.id_comp _) (Category.id_comp _) cup
  simp only [mul_zero, sign_zero, mul_one] at h
  exact h

example : IsIso (leftCrossMate A A T) :=
  leftCrossMate_isIso_of_cup_pitchfork A A T (𝟙 (E ≫ E)) (id_mem (E ≫ E)) two cup

example : (leftCrossMate A A T).total () ≠ 0 := by
  have h := leftCrossMate_eq_of_cup_pitchfork A A T (𝟙 E) (id_mem E) (2 : ℚ) cup
  simp only [mul_zero, sign_zero, mul_one] at h
  rw [h]
  change (2 : ℚ) * 1 + 2 * 0 ≠ 0
  norm_num

end NonVacuity.RouquierDistinctLeftCupRotationConcrete

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.RouquierDistinctLeftCupRotation then
      for name in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"
