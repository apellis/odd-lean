import OddMath.SKM.RouquierReflectedLocal

/-!
# Canonical cup and cap scalar comparisons under reflection

This checks the corresponding comparison in `SignedFTriangle.md`, §§4–5,
supporting Brundan, arXiv:1501.00350v1, Theorem 4.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
namespace SuperRouquierLoc
variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}
  {p : ZMod 2} {h : ℤ} (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)

/-- Reflection of the canonical inverse crossing. -/
theorem horizontalReflection_sigL :
    L.horizontalReflection.sigL = koszulSign p p • L.sigL := by
  unfold sigL
  split_ifs <;> simp only [horizontalReflection_invPos_f', horizontalReflection_invNeg_f',
    smul_neg]

/-- Reflection of every canonical inverse cup component. -/
theorem horizontalReflection_cupN (n : ℕ) :
    L.horizontalReflection.cupN n = koszulSign p p ^ (n.choose 2) • L.cupN n := by
  unfold cupN
  split_ifs <;> simp only [horizontalReflection_invPos_g', smul_zero]

/-- Reflection of every canonical inverse cap component. -/
theorem horizontalReflection_capN (n : ℕ) :
    L.horizontalReflection.capN n = koszulSign p p ^ (n.choose 2) • L.capN n := by
  unfold capN
  split_ifs <;> simp only [horizontalReflection_invNeg_g', smul_zero]

/-- Reflection of the dotted right cup. -/
theorem horizontalReflection_cupD (n : ℕ) :
    L.horizontalReflection.cupD n = koszulSign p p ^ (n.choose 2) • L.cupD n := by
  change A₂.unit ≫ E₂ ◁ rouquierPower (B := HOpS B) (A₂.rightTranspose A₂ x₂) n = _
  rw [rouquierPower_horizontalOpposite]
  exact L.rightTranspose_cupD n

/-- Reflection of the dotted right cap. -/
theorem horizontalReflection_capD (n : ℕ) :
    L.horizontalReflection.capD n = koszulSign p p ^ (n.choose 2) • L.capD n := by
  change whiskerRight (B := B)
    (rouquierPower (B := HOpS B) (A₁.rightTranspose A₁ x₁) n) E₁ ≫ A₁.counit = _
  rw [rouquierPower_horizontalOpposite]
  exact L.rightTranspose_capD n

/-- The scalar comparison uses the canonical piecewise cup, including height zero. -/
theorem horizontalReflection_cupL :
    L.horizontalReflection.cupL =
      (if 0 < h then koszulSign p p ^ ((h - 1).toNat.choose 2)
       else koszulSign p p * koszulSign p p ^ ((-h).toNat.choose 2)) • L.cupL := by
  unfold cupL
  split_ifs with hh
  · exact L.horizontalReflection_cupN _
  · rw [horizontalReflection_cupD, horizontalReflection_sigL]
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul]

/-- The scalar comparison uses the canonical piecewise cap, including height zero. -/
theorem horizontalReflection_capL :
    L.horizontalReflection.capL =
      (if h < 0 then koszulSign p p ^ ((-h - 1).toNat.choose 2)
       else koszulSign p p * koszulSign p p ^ (h.toNat.choose 2)) • L.capL := by
  unfold capL
  split_ifs with hh
  · exact L.horizontalReflection_capN _
  · rw [horizontalReflection_sigL, horizontalReflection_capD]
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, smul_neg, mul_comm]
end SuperRouquierLoc
end OddMath.SKM
