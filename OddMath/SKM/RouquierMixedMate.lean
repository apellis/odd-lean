import OddMath.SKM.RouquierMate

/-!
# Rectangular outer mates for the mixed braid

Composition is diagrammatic. The outer adjunctions need not be adjacent:
`E₁ : a ⟶ b` and `E₃ : c ⟶ d`. All their units and counits are even.
The rectangular transpose retains arbitrary, including odd, Hom morphisms.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- The rectangular outer transpose, using only the two existing Hom adjunctions. -/
def rectangularMate {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₃ : c ⟶ d} {F₃ : d ⟶ c}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₃ : SuperAdjunction (k := k) E₃ F₃)
    (g : a ⟶ c) (h : b ⟶ d) :
    (g ≫ E₃ ⟶ E₁ ≫ h) ≃ (F₁ ≫ g ⟶ h ≫ F₃) :=
  ((homPostAdjunction A₃).homEquiv g (E₁ ≫ h)).trans
    ((Iso.homCongr (Iso.refl g) (associator E₁ h F₃)).trans
      ((homPreAdjunction A₁).homEquiv g (h ≫ F₃)).symm)

/-- Explicit cup–map–cap formula; all four corner objects are independent. -/
theorem rectangularMate_eq {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₃ : c ⟶ d} {F₃ : d ⟶ c}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₃ : SuperAdjunction (k := k) E₃ F₃)
    (g : a ⟶ c) (h : b ⟶ d) (z : g ≫ E₃ ⟶ E₁ ≫ h) :
    rectangularMate A₁ A₃ g h z =
      F₁ ◁ ((rightUnitor g).inv ≫ g ◁ A₃.unit ≫ (associator g E₃ F₃).inv ≫
        z ▷ F₃ ≫ (associator E₁ h F₃).hom) ≫
      (associator F₁ E₁ (h ≫ F₃)).inv ≫ A₁.counit ▷ (h ≫ F₃) ≫
      (leftUnitor (h ≫ F₃)).hom := by
  simp [rectangularMate, CategoryTheory.Adjunction.homEquiv, homPostAdjunction,
    homPreAdjunction, homPostUnit, homPreCounit, homPostId, homPostComp,
    homPreId, homPreComp, homPostTransform, homPreTransform,
    SuperNatTrans.toNatTrans, homPost, homPre, Iso.homCongr, Category.assoc]

/-- Input naturality costs no sign: only an even unit is crossed. -/
theorem rectangularMate_left {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₃ : c ⟶ d} {F₃ : d ⟶ c}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₃ : SuperAdjunction (k := k) E₃ F₃)
    {g g' : a ⟶ c} (h : b ⟶ d) (x : g ⟶ g') (z : g' ≫ E₃ ⟶ E₁ ≫ h) :
    rectangularMate A₁ A₃ g h (x ▷ E₃ ≫ z) =
      F₁ ◁ x ≫ rectangularMate A₁ A₃ g' h z := by
  have h₁ := (homPostAdjunction A₃).homEquiv_naturality_left x z
  have h₂ := (homPreAdjunction A₁).homEquiv_naturality_left_symm x
    ((homPostAdjunction A₃).homEquiv g' (E₁ ≫ h) z ≫ (associator E₁ h F₃).hom)
  have h₃ := congrArg (fun q => ((homPreAdjunction A₁).homEquiv g (h ≫ F₃)).symm
    (q ≫ (associator E₁ h F₃).hom)) h₁
  have h₄ := h₃.trans (by simpa only [Category.assoc] using h₂)
  simpa [rectangularMate, Iso.homCongr, homPreAdjunction, homPostAdjunction,
    CategoryTheory.Adjunction.homEquiv, homPre, homPost, Category.assoc] using h₄

/-- Output naturality costs no sign: only an even counit is crossed. -/
theorem rectangularMate_right {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₃ : c ⟶ d} {F₃ : d ⟶ c}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₃ : SuperAdjunction (k := k) E₃ F₃)
    (g : a ⟶ c) {h h' : b ⟶ d} (y : h ⟶ h') (z : g ≫ E₃ ⟶ E₁ ≫ h) :
    rectangularMate A₁ A₃ g h' (z ≫ E₁ ◁ y) =
      rectangularMate A₁ A₃ g h z ≫ y ▷ F₃ := by
  have h₁ := (homPostAdjunction A₃).homEquiv_naturality_right z (E₁ ◁ y)
  have h₂ := (homPreAdjunction A₁).homEquiv_naturality_right_symm
    ((homPostAdjunction A₃).homEquiv g (E₁ ≫ h) z ≫ (associator E₁ h F₃).hom) (y ▷ F₃)
  have h₃ := congrArg (fun q => ((homPreAdjunction A₁).homEquiv g (h' ≫ F₃)).symm
    (q ≫ (associator E₁ h' F₃).hom)) h₁
  have hmid : ((homPostAdjunction A₃).homEquiv g (E₁ ≫ h) z ≫
      (homPost (k := k) F₃).map (E₁ ◁ y)) ≫ (associator E₁ h' F₃).hom =
    ((homPostAdjunction A₃).homEquiv g (E₁ ≫ h) z ≫ (associator E₁ h F₃).hom) ≫
      (homPre (k := k) E₁).map (y ▷ F₃) := by
    change (_ ≫ (E₁ ◁ y) ▷ F₃) ≫ _ = (_ ≫ _) ≫ E₁ ◁ (y ▷ F₃)
    rw [Category.assoc, TwoSupercategory.associator_naturality_middle (R := k), Category.assoc]
  have h₄ := h₃.trans ((congrArg ((homPreAdjunction A₁).homEquiv g (h' ≫ F₃)).symm hmid).trans h₂)
  simpa [rectangularMate, Iso.homCongr, homPreAdjunction, homPostAdjunction,
    CategoryTheory.Adjunction.homEquiv, homPre, homPost, Category.assoc] using h₄

private theorem rectangularPrefix {C : Type u} [Bicategory.{w,v} C]
    {a b c : C} (F : b ⟶ a) (E : a ⟶ b) (H : b ⟶ c) (K : c ⟶ b) :
    (Bicategory.associator F E (H ≫ K)).hom ≫
      Bicategory.whiskerLeft F (Bicategory.associator E H K).inv ≫
      (Bicategory.associator F (E ≫ H) K).inv =
    (Bicategory.associator (F ≫ E) H K).inv ≫
      Bicategory.whiskerRight (Bicategory.associator F E H).hom K := by
  bicategory

/-- Transposing on the right alone exposes the uncapped pitchfork. -/
theorem rouquierMate_postTranspose {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    rouquierMate A₁ A₂ t = (homPostAdjunction A₂).homEquiv (F₁ ≫ E₁) E₂
      ((associator F₁ E₁ E₂).hom ≫ F₁ ◁ t ≫
        (associator F₁ E₁ E₂).inv ≫ A₁.counit ▷ E₂ ≫ (leftUnitor E₂).hom) := by
  have hp := congrArg Subtype.val (rectangularPrefix
    (Underlying2.hom1 (R := k) F₁) (Underlying2.hom1 (R := k) E₁)
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂))
  change (associator F₁ E₁ (E₂ ≫ F₂)).hom ≫
    F₁ ◁ (associator E₁ E₂ F₂).inv ≫ (associator F₁ (E₁ ≫ E₂) F₂).inv =
    (associator (F₁ ≫ E₁) E₂ F₂).inv ≫ (associator F₁ E₁ E₂).hom ▷ F₂ at hp
  simp only [rouquierMate, CategoryTheory.Adjunction.homEquiv, homPostAdjunction,
    homPostUnit, homPostId, homPostComp, homPostTransform, SuperNatTrans.toNatTrans,
    homPost, Equiv.coe_fn_mk, NatTrans.comp_app, NatIso.ofComponents_inv_app, ite_true,
    TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]
  rw [TwoSupercategory.associator_inv_naturality_middle_assoc (R := k)]
  rw [reassoc_of% hp]

/-- Capping a rightward mate uses the existing E-strand right-adjunction triangle.
There is no assumption about any left adjunction. -/
theorem rouquierMate_pitchfork_cap {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    rouquierMate A₁ A₂ t ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
      E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom =
    (associator F₁ E₁ E₂).hom ≫ F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv ≫
      A₁.counit ▷ E₂ ≫ (leftUnitor E₂).hom := by
  have h := congrArg ((homPostAdjunction A₂).homEquiv (F₁ ≫ E₁) E₂).symm
    (rouquierMate_postTranspose A₁ A₂ t)
  rw [Equiv.symm_apply_apply] at h
  simpa [CategoryTheory.Adjunction.homEquiv, homPostAdjunction, homPostCounit,
    homPostComp, homPostTransform, homPostId, SuperNatTrans.toNatTrans, homPost,
    Category.assoc] using h

/-- Homogeneity follows from the defining even cups and caps, independently of inversion data. -/
theorem rouquierMate_parity {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    {p : ZMod 2} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} (ht : t ∈ parity (R := k) _ _ p) :
    rouquierMate A₁ A₂ t ∈ parity (R := k) _ _ p := by
  rw [rouquierMate_postTranspose]
  have hm := comp_mem (homPostUnit_mem A₂ (F₁ ≫ E₁))
    (TwoSupercategory.whiskerRight_mem (F₂)
      (comp_mem (TwoSupercategory.associator_hom_mem (R := k) F₁ E₁ E₂)
        (comp_mem (TwoSupercategory.whiskerLeft_mem F₁ ht)
          (comp_mem (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) F₁ E₁ E₂))
            (comp_mem (TwoSupercategory.whiskerRight_mem E₂ A₁.counit_mem)
              (TwoSupercategory.leftUnitor_hom_mem (R := k) E₂))))))
  simpa [CategoryTheory.Adjunction.homEquiv, homPostAdjunction, homPost,
    Category.assoc] using hm

/-- The odd–odd move in the two-mate calculation, with its coefficient derived
from the crossing parities rather than imposed as a braid hypothesis. -/
theorem rouquierMate_cross_interchange {a b c d : B}
    {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b} {E₃ : c ⟶ d}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    {p : ZMod 2} {t₁₂ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {t₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃}
    (h₁₂ : t₁₂ ∈ parity (R := k) _ _ p) (h₂₃ : t₂₃ ∈ parity (R := k) _ _ p) :
    rouquierMate A₁ A₂ t₁₂ ▷ (E₂ ≫ E₃) ≫ (E₂ ≫ F₂) ◁ t₂₃ =
      koszulSign p p • ((F₁ ≫ E₁) ◁ t₂₃ ≫ rouquierMate A₁ A₂ t₁₂ ▷ (E₂ ≫ E₃)) :=
  TwoSupercategory.super_interchange (rouquierMate_parity A₁ A₂ h₁₂) h₂₃

end OddMath.SKM
