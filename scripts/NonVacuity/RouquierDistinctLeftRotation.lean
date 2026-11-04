import OddMath.SKM.RouquierDistinctLeftRotation
import StringDiagrams.Super.SCat
import StringDiagrams.Super.Superalgebra
import Lean.Util.CollectAxioms

/-! A nonzero identity-superfunctor fixture discharges every cap-pitchfork
and inverse hypothesis with scalar two. Additional API tests retain the
odd cup/odd crossing sign and the reciprocal scalar. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierDistinctLeftRotation
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
  (hcap : (associator Ed Ec Fa).inv ≫ T ▷ Fa ≫
    (associator Eb Ea Fa).hom ≫ Eb ◁ Aa.counit ≫ (rightUnitor Eb).hom =
    (2 : ℚ) • (Ed ◁ l ≫ (associator Ed Fd Eb).inv ≫
      Ad.counit ▷ Eb ≫ (leftUnitor Eb).hom))

example : leftCrossMate Ad Aa T = (-2 : ℚ) • l := by
  simpa using leftCrossMate_eq_of_cap_pitchfork Ad Aa T l hl (2 : ℚ) hcap

private def two : ℚˣ := ⟨2, 1 / 2, by norm_num, by norm_num⟩

example : leftCrossMate Ad Aa T ≫ ((-1 / 2 : ℚ) • s) = 𝟙 _ ∧
    ((-1 / 2 : ℚ) • s) ≫ leftCrossMate Ad Aa T = 𝟙 _ := by
  simpa [two, div_eq_mul_inv] using
    leftCrossMate_inv_products_of_cap_pitchfork Ad Aa T l s hl two hls hsl hcap

example : IsIso (leftCrossMate Ad Aa T) :=
  leftCrossMate_isIso_of_cap_pitchfork Ad Aa T l s hl two hls hsl hcap

end NonVacuity.RouquierDistinctLeftRotation

namespace NonVacuity.RouquierDistinctLeftRotationConcrete
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
private theorem cap :
    (associator E E E).inv ≫ T ▷ E ≫ (associator E E E).hom ≫
      E ◁ A.counit ≫ (rightUnitor E).hom =
    (2 : ℚ) • (E ◁ (𝟙 E) ≫ (associator E E E).inv ≫
      A.counit ▷ E ≫ (leftUnitor E).hom) := by
  change (𝟙 E) ≫ ((2 : ℚ) • 𝟙 E) ▷ E ≫ (𝟙 E) ≫ E ◁ (𝟙 E) ≫ (𝟙 E) =
    (2 : ℚ) • (E ◁ (𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E) ▷ E ≫ (𝟙 E))
  simp only [TwoSupercategory.smul_whiskerRight (R := ℚ),
    TwoSupercategory.id_whiskerRight (R := ℚ), TwoSupercategory.whiskerLeft_id (R := ℚ),
    Category.id_comp]
  change ((2 : ℚ) • 𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E) =
    (2 : ℚ) • ((𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E))
  simp only [Category.comp_id]

example : leftCrossMate A A T = (2 : ℚ) • 𝟙 E := by
  simpa using leftCrossMate_eq_of_cap_pitchfork A A T (𝟙 E) (id_mem E) (2 : ℚ) cap

example : leftCrossMate A A T ≫ ((1 / 2 : ℚ) • 𝟙 E) = 𝟙 E ∧
    ((1 / 2 : ℚ) • 𝟙 E) ≫ leftCrossMate A A T = 𝟙 E := by
  have h := leftCrossMate_inv_products_of_cap_pitchfork A A T
    (𝟙 E) (𝟙 E) (id_mem E) two (Category.id_comp _) (Category.id_comp _) cap
  simp only [mul_zero, sign_zero, mul_one] at h
  exact h

example : IsIso (leftCrossMate A A T) :=
  leftCrossMate_isIso_of_cap_pitchfork A A T (𝟙 E) (𝟙 E) (id_mem E)
    two (Category.id_comp _) (Category.id_comp _) cap

example : (leftCrossMate A A T).total () ≠ 0 := by
  have h := leftCrossMate_eq_of_cap_pitchfork A A T (𝟙 E) (id_mem E) (2 : ℚ) cap
  simp only [mul_zero, sign_zero, mul_one] at h
  rw [h]
  change (2 : ℚ) * 1 + 2 * 0 ≠ 0
  norm_num

end NonVacuity.RouquierDistinctLeftRotationConcrete

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.RouquierDistinctLeftRotation then
      for name in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"
