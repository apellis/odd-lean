import OddMath.SKM.RouquierReflectedLocal

/-!
# Signed reflection of the bracketed three-strand braid

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
namespace SuperAdjunction
variable {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
  {E₂ : b ⟶ c} {F₂ : c ⟶ b} {E₃ : c ⟶ d} {F₃ : d ⟶ c}
  (A₁ : SuperAdjunction (k := k) E₁ F₁)
  (A₂ : SuperAdjunction (k := k) E₂ F₂)
  (A₃ : SuperAdjunction (k := k) E₃ F₃)

/-- Forward associators transpose to forward associators of the reversed string. -/
theorem rightTranspose_associator_hom :
    rightTranspose ((A₁.comp A₂).comp A₃) (A₁.comp (A₂.comp A₃))
      (associator E₁ E₂ E₃).hom = (associator F₃ F₂ F₁).hom := by
  have e := congrArg ((A₁.comp (A₂.comp A₃)).rightTranspose
    (A₁.comp (A₂.comp A₃))) (associator E₁ E₂ E₃).inv_hom_id
  rw [rightTranspose_comp _ ((A₁.comp A₂).comp A₃) _
    (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E₁ E₂ E₃))
    (TwoSupercategory.associator_hom_mem (R := k) E₁ E₂ E₃),
    rightTranspose_associator_inv, rightTranspose_id] at e
  simpa only [koszulSign_zero_left, one_smul, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Category.id_comp] using
    congrArg (· ≫ (associator F₃ F₂ F₁).hom) e

/-- The first bracketed crossing transposes with no associator sign. -/
theorem rightTranspose_bracketed_whiskerRight {p : ZMod 2}
    {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} (ht : t ∈ parity (R := k) _ _ p) :
    rightTranspose (A₁.comp (A₂.comp A₃)) (A₁.comp (A₂.comp A₃))
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) =
    (associator F₃ F₂ F₁).hom ≫
      F₃ ◁ rightTranspose (A₁.comp A₂) (A₁.comp A₂) t ≫
      (associator F₃ F₂ F₁).inv := by
  rw [rightTranspose_comp _ ((A₁.comp A₂).comp A₃) _
    (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E₁ E₂ E₃))
    (comp_mem (TwoSupercategory.whiskerRight_mem E₃ ht)
      (TwoSupercategory.associator_hom_mem (R := k) E₁ E₂ E₃)),
    rightTranspose_comp _ ((A₁.comp A₂).comp A₃) _
      (TwoSupercategory.whiskerRight_mem E₃ ht)
      (TwoSupercategory.associator_hom_mem (R := k) E₁ E₂ E₃),
    rightTranspose_associator_inv, rightTranspose_associator_hom,
    rightTranspose_whiskerRight]
  simp only [koszulSign_zero_left, koszulSign_zero_right, one_smul, Category.assoc]
private theorem rightTranspose_palindrome {a b : B} {E : a ⟶ b} {F : b ⟶ a}
    (A : SuperAdjunction (k := k) E F) {p : ZMod 2} {f g : E ⟶ E}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ p) :
    A.rightTranspose A (f ≫ g ≫ f) =
      koszulSign p p • (A.rightTranspose A f ≫ A.rightTranspose A g ≫ A.rightTranspose A f) := by
  rw [rightTranspose_comp A A A hf (comp_mem hg hf),
    rightTranspose_comp A A A hg hf]
  simp only [koszulSign_add_left, koszulSign_mul_self, one_smul,
    Preadditive.zsmul_comp, Category.assoc]
end SuperAdjunction

namespace SuperRouquierLoc
variable {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
  {E₂ : b ⟶ c} {F₂ : c ⟶ b} {E₃ : c ⟶ d} {F₃ : d ⟶ c}
  {A₁ : SuperAdjunction (k := k) E₁ F₁}
  {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {A₃ : SuperAdjunction (k := k) E₃ F₃}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {x₃ : E₃ ⟶ E₃}
  {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {t' : E₂ ≫ E₃ ⟶ E₂ ≫ E₃}
  {p : ZMod 2} {h h' : ℤ}
  (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)
  (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t' p h')

/-- The bracketed three-strand braid for the prescribed signed reflected crossings. -/
theorem reflectedCross_braid
    (hb : E₁ ◁ t' ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
        (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t' =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
        E₁ ◁ t' ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
          (associator E₁ E₂ E₃).hom)) :
    U.reflectedCross ▷ F₁ ≫ ((associator F₃ F₂ F₁).hom ≫ F₃ ◁ L.reflectedCross ≫
        (associator F₃ F₂ F₁).inv) ≫ U.reflectedCross ▷ F₁ =
      ((associator F₃ F₂ F₁).hom ≫ F₃ ◁ L.reflectedCross ≫
        (associator F₃ F₂ F₁).inv) ≫ U.reflectedCross ▷ F₁ ≫
      ((associator F₃ F₂ F₁).hom ≫ F₃ ◁ L.reflectedCross ≫
        (associator F₃ F₂ F₁).inv) := by
  have hm : (associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom ∈
      parity (R := k) _ _ p := by
    simpa only [zero_add, add_zero] using comp_mem
      (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E₁ E₂ E₃))
      (comp_mem (TwoSupercategory.whiskerRight_mem E₃ L.cross_mem)
        (TwoSupercategory.associator_hom_mem (R := k) E₁ E₂ E₃))
  have hn := TwoSupercategory.whiskerLeft_mem E₁ U.cross_mem
  have e := congrArg ((A₁.comp (A₂.comp A₃)).rightTranspose
    (A₁.comp (A₂.comp A₃))) hb
  rw [SuperAdjunction.rightTranspose_palindrome _ hn hm,
    SuperAdjunction.rightTranspose_palindrome _ hm hn,
    SuperAdjunction.rightTranspose_whiskerLeft,
    SuperAdjunction.rightTranspose_bracketed_whiskerRight _ _ _ L.cross_mem] at e
  simpa only [reflectedCross, TwoSupercategory.zsmul_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_zsmul (R := k), Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, smul_smul, koszulSign_mul_self, mul_one, one_mul,
    Category.assoc] using e
end SuperRouquierLoc
end OddMath.SKM
