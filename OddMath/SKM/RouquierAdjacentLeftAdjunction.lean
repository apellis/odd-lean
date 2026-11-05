import OddMath.SKM.RouquierFTriangle

/-! # Shifted left adjunction from adjacent local inverses

The negative-height case of Brundan, Theorem 4.3, already follows from
`RouquierPitchfork` and `RouquierFTriangle`. We package exactly their local
inputs, without a whole weight-indexed Rouquier family. The cap is scaled
by the prescribed involutive scalar; the unit is the given inverse cup.
-/
noncomputable section
namespace OddMath.SKM.SuperRouquierLoc
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
  {E₂ : b ⟶ c} {F₂ : c ⟶ b} {E₃ : c ⟶ d} {F₃ : d ⟶ c}
  {A₁ : SuperAdjunction (k := k) E₁ F₁}
  {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {A₃ : SuperAdjunction (k := k) E₃ F₃}
  {x₁ : End E₁} {x₂ : End E₂} {x₃ : End E₃}
  {t : End (E₁ ≫ E₂)} {t' : End (E₂ ≫ E₃)} {p : ZMod 2} {h : ℤ}
  (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)
  (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t' p (h + 2))
  (hh : h < 0) (hsq : t ≫ t = 0) (hsq' : t' ≫ t' = 0)
  (hB : E₁ ◁ t' ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t' =
    ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t' ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom))

/-- Two adjacent local inverses, signed slides, square-zero crossings and
the equal-colour braid suffice for the negative-height shifted left
adjunction. The `SuperRouquierLoc` inputs carry the slides and inverse fields. -/
def negativeLeftAdjunction : ShiftedSuperAdjunction (k := k) F₂ E₂ (p * ((h : ZMod 2) + 1)) where
  unit := U.cupL
  counit := koszulSign (p * ((h : ZMod 2) + 1)) (p * ((h : ZMod 2) + 1)) • L.capL
  unit_mem := by
    simpa only [Int.cast_add, Int.cast_ofNat, show (2 : ZMod 2) = 0 from rfl, add_zero] using U.cupL_mem
  counit_mem := Submodule.smul_of_tower_mem _ _ L.capL_mem
  left_triangle := by
    have hf := L.leftAdj_triangle_F U rfl hsq hsq' hB
    rw [ite_eq_left hh, mul_one] at hf
    simp only [Int.cast_add, Int.cast_one] at hf
    rw [TwoSupercategory.whiskerLeft_zsmul (R := k), Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Preadditive.comp_zsmul, Preadditive.comp_zsmul,
      hf, smul_smul, koszulSign_mul_self, one_smul]
  right_triangle := by
    have he := L.leftAdj_triangle_E_of_neg U rfl hh hsq hsq' hB
    rw [TwoSupercategory.zsmul_whiskerRight (R := k), Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Preadditive.comp_zsmul, Preadditive.comp_zsmul, he]

end OddMath.SKM.SuperRouquierLoc
