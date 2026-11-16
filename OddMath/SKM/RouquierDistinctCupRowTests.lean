import OddMath.SKM.RouquierDistinctCupTests
import OddMath.SKM.RouquierDistinctCupRows
import OddMath.SKM.RouquierDistinctPowerSlide
import OddMath.SKM.RouquierRectangularComposition
import OddMath.SKM.Calculus

/-! # The actual finite row tests of the distinct cup words

Brundan–Ellis Lemma 7.1, `Lemma71Cup.pcuL_b_reduce` and `pcu_b`:
the prescribed distinct right mate transports every dotted right cap.
The two interchange/dot-slide signs cancel, leaving the actual
quadratic word evaluated by the strict positive finite rows.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

private theorem rectangularDottedCap {a b c d : B}
    {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : c ⟶ d} {F₂ : d ⟶ c}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (g : a ⟶ c) (h : b ⟶ d) (t : g ≫ E₂ ⟶ E₁ ≫ h)
    (x₁ : End E₁) (x₂ : End E₂) {p q : ZMod 2}
    (hx : x₂ ∈ parity (R := k) _ _ p) (ht : t ∈ parity (R := k) _ _ q)
    (hslide : g ◁ x₂ ≫ t = koszulSign p q • (t ≫ x₁ ▷ h)) :
    crossMate A₁ A₂ t ▷ E₂ ≫ (associator h F₂ E₂).hom ≫
      h ◁ (F₂ ◁ x₂ ≫ A₂.counit) ≫ (rightUnitor h).hom =
    (associator F₁ g E₂).hom ≫ F₁ ◁ t ≫ (associator F₁ E₁ h).inv ≫
      (F₁ ◁ x₁ ≫ A₁.counit) ▷ h ≫ (leftUnitor h).hom := by
  have he := TwoSupercategory.super_interchange (R := k)
    (crossMate_mem A₁ A₂ g h t ht) hx
  rw [koszulSign_comm q p] at he
  have hc := crossMate_pitchfork_cap A₁ A₂ g h t
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k) h F₂ x₂,
    reassoc_of% he]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  rw [hc, TwoSupercategory.associator_naturality_right_assoc (R := k) F₁ g x₂,
    ← reassoc_of% (TwoSupercategory.whiskerLeft_comp (R := k) F₁ (g ◁ x₂) t), hslide]
  simp only [TwoSupercategory.whiskerLeft_zsmul (R := k), Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, koszulSign_smul_smul]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]
  rw [TwoSupercategory.associator_inv_naturality_middle_assoc (R := k) F₁ x₁ h]

private theorem dottedCap_sign (p q : ZMod 2) (n : ℕ) :
    sign k (((n : ZMod 2) * p) * (p * q)) = zsign k (p * q) ^ n := by
  rw [← zsign_natCast_mul]
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    rcases parity_eq_zero_or_one (n : ZMod 2) with hn | hn <;> simp [hn, sign, zsign]

namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) {Sc : Scalars D k}
  (M : RouquierMulticolour T Sc) (i j : I) (hne : i ≠ j)
  {a b c d : X} (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
  (h₃ : a + D.α i = c) (h₄ : c + D.α j = d)

include M hne in
/-- The original distinct right mate transports the actual dotted caps;
the interchange sign is cancelled by the actual upward power slide. -/
theorem distinctCrossMate_dottedCap (n : ℕ) :
    crossMate (T.adj i h₃) (T.adj i h₂) (T.cross i j h₁ h₂ h₃ h₄) ▷ T.E i h₂ ≫
      (associator (T.E j h₄) (T.F i h₂) (T.E i h₂)).hom ≫
      T.E j h₄ ◁ (T.F i h₂ ◁ rouquierPower (T.dot i h₂) n ≫ (T.adj i h₂).counit) ≫
      (rightUnitor (T.E j h₄)).hom =
    (associator (T.F i h₃) (T.E j h₁) (T.E i h₂)).hom ≫
      T.F i h₃ ◁ T.cross i j h₁ h₂ h₃ h₄ ≫
      (associator (T.F i h₃) (T.E i h₃) (T.E j h₄)).inv ≫
      (T.F i h₃ ◁ rouquierPower (T.dot i h₃) n ≫ (T.adj i h₃).counit) ▷ T.E j h₄ ≫
      (leftUnitor (T.E j h₄)).hom := by
  apply rectangularDottedCap (T.adj i h₃) (T.adj i h₂) (T.E j h₁) (T.E j h₄)
    (T.cross i j h₁ h₂ h₃ h₄) (rouquierPower (T.dot i h₃) n)
    (rouquierPower (T.dot i h₂) n) (rouquierPower_mem (T.dot_mem i h₂) n)
    (T.cross_mem i j h₁ h₂ h₃ h₄)
  rw [koszulSign_smul (R := k), dottedCap_sign]
  exact M.slideLeft_power i j hne h₁ h₂ h₃ h₄ n
end RouquierFamily

namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) {Sc : Scalars D k}
  (M : RouquierMulticolour T Sc) {i j : I} (hne : i ≠ j)
  {a b c d e f : X} (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d)
  (hupper : b + D.α i = e) (hnext : d + D.α i = f)

include M hne in
/-- The actual left cup's finite target-chart row is its literal
lower cup, upward double crossing and lower dotted cap. -/
theorem distinctCupLeft_row_reduce (n : ℕ) :
    T.distinctCupLeft hi hj hij hji hupper ≫ T.distinctCupTarget hi hj hij hji ≫
      T.E j hij ◁ (T.loc i hji hnext).capD n ≫ (rightUnitor (T.E j hij)).hom =
    (leftUnitor (T.E j hij)).inv ≫ (T.loc i hi hupper).cupL ▷ T.E j hij ≫
      (associator (T.F i hi) (T.E i hi) (T.E j hij)).hom ≫
      T.F i hi ◁ (T.cross j i hi hij hj hji ≫ T.cross i j hj hji hi hij) ≫
      (associator (T.F i hi) (T.E i hi) (T.E j hij)).inv ≫
      (T.loc i hi hupper).capD n ▷ T.E j hij ≫ (leftUnitor (T.E j hij)).hom := by
  have hc := T.distinctCrossMate_dottedCap M i j hne hj hji hi hij n
  change crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij) ▷ T.E i hji ≫
      (associator (T.E j hij) (T.F i hji) (T.E i hji)).hom ≫
      T.E j hij ◁ (T.loc i hji hnext).capD n ≫ (rightUnitor (T.E j hij)).hom =
    (associator (T.F i hi) (T.E j hj) (T.E i hji)).hom ≫
      T.F i hi ◁ T.cross i j hj hji hi hij ≫
      (associator (T.F i hi) (T.E i hi) (T.E j hij)).inv ≫
      (T.loc i hi hupper).capD n ▷ T.E j hij ≫ (leftUnitor (T.E j hij)).hom at hc
  unfold distinctCupLeft distinctCupTarget
  simp only [Category.assoc]
  rw [hc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, TwoSupercategory.whiskerLeft_comp (R := k)]

include M hne in
/-- The complete actual left finite row in the strict positive range,
with its original leading parameter and shifted boundary index. -/
theorem distinctCupLeft_row_of_gt (hh : D.d i j < D.h i b) (n : ℕ)
    (hn : n < (D.h i d).toNat) :
    T.distinctCupLeft hi hj hij hji hupper ≫ T.distinctCupTarget hi hj hij hji ≫
      T.E j hij ◁ (T.loc i hji hnext).capD n ≫ (rightUnitor (T.E j hij)).hom =
    (Sc.t i j : k) • (if n = (D.h i d - 1).toNat then 𝟙 (T.E j hij) else 0) := by
  rw [T.distinctCupLeft_row_reduce M hne hi hj hij hji hupper hnext n]
  exact T.distinctCupQuadraticRow_of_gt M hne hi hj hij hji hupper hh n hn

/-- The prescribed inverse target chart leaves exactly the upper local
cup-cap Kronecker row at positive shifted height. -/
theorem distinctCupRight_row_of_pos (hh : 0 < D.h i d) (n : ℕ)
    (hn : n < (D.h i d).toNat) :
    T.distinctCupRight M hne hi hj hij hji hnext ≫ T.distinctCupTarget hi hj hij hji ≫
      T.E j hij ◁ (T.loc i hji hnext).capD n ≫ (rightUnitor (T.E j hij)).hom =
    if n = (D.h i d - 1).toNat then 𝟙 (T.E j hij) else 0 := by
  have hk : (T.loc i hji hnext).cupL ≫ (T.loc i hji hnext).capD n =
      if n = (D.h i d - 1).toNat then 𝟙 _ else 0 := by
    simpa only [eq_comm] using (T.loc i hji hnext).cupL_capD hh hn
  have hw := congrArg (fun z => (rightUnitor (T.E j hij)).inv ≫ T.E j hij ◁ z ≫
    (rightUnitor (T.E j hij)).hom) hk
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc] at hw
  rw [reassoc_of% (T.distinctCupRight_target M hne hi hj hij hji hnext)]
  rw [hw]
  split_ifs
  · simp only [TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp, Iso.inv_hom_id]
  · simp only [TwoSupercategory.whiskerLeft_zero (R := k), Limits.comp_zero, Limits.zero_comp]
end RouquierFamily
end OddMath.SKM
