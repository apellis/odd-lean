import OddMath.SKM.HorizontalSuperOpposite
import OddMath.SKM.RouquierTransposeComparison

/-!
# The reflected Rouquier mate

Identifies the horizontal-opposite cup–crossing–cap composite with the
inverse partial bend in `SignedFTriangle.md` §3. The argument is an
arbitrary 2-morphism; only the even prefix and suffix use ordinary coherence.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

private theorem reflectedPrefix {C : Type u} [Bicategory.{w,v} C]
    {a b c : C} (F : b ⟶ a) (E : a ⟶ b) (H : b ⟶ c) (K : c ⟶ b)
    (η : 𝟙 b ⟶ H ≫ K) :
    (Bicategory.leftUnitor (F ≫ E)).inv ≫ Bicategory.whiskerRight η (F ≫ E) ≫
      (Bicategory.associator (H ≫ K) F E).inv ≫
      Bicategory.whiskerRight (Bicategory.associator H K F).hom E =
    Bicategory.whiskerRight (Bicategory.leftUnitor F).inv E ≫
      Bicategory.whiskerRight (Bicategory.whiskerRight η F) E ≫
      Bicategory.whiskerRight (Bicategory.associator H K F).hom E := by
  bicategory

private theorem reflectedSuffix {C : Type u} [Bicategory.{w,v} C]
    {a b c : C} (F : b ⟶ a) (E : a ⟶ b) (H : b ⟶ c) (K : c ⟶ b)
    (ε : F ≫ E ⟶ 𝟙 b) :
    (Bicategory.associator H (K ≫ F) E).hom ≫
      Bicategory.whiskerLeft H (Bicategory.associator K F E).hom ≫
      Bicategory.whiskerLeft H (Bicategory.whiskerLeft K ε) ≫
      Bicategory.whiskerLeft H (Bicategory.rightUnitor K).hom =
    Bicategory.whiskerRight (Bicategory.associator H K F).inv E ≫
      (Bicategory.associator (H ≫ K) F E).hom ≫
      Bicategory.whiskerLeft (H ≫ K) ε ≫ (Bicategory.rightUnitor (H ≫ K)).hom := by
  bicategory

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}

/-- Reflection realizes the inverse bend on all maps, including odd crossings. -/
theorem rouquierMate_horizontalOpposite
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (v : F₂ ≫ F₁ ⟶ F₂ ≫ F₁) :
    rouquierMate A₁.horizontalOpposite A₂.horizontalOpposite v =
      (mixedMateBend A₁ A₂).symm v := by
  have hp := congrArg Subtype.val (reflectedPrefix
    (Underlying2.hom1 (R := k) F₁) (Underlying2.hom1 (R := k) E₁)
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂)
    ⟨A₂.unit, A₂.unit_mem⟩)
  have hs := congrArg Subtype.val (reflectedSuffix
    (Underlying2.hom1 (R := k) F₁) (Underlying2.hom1 (R := k) E₁)
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂)
    ⟨A₁.counit, A₁.counit_mem⟩)
  change (leftUnitor (F₁ ≫ E₁)).inv ≫ A₂.unit ▷ (F₁ ≫ E₁) ≫
    (associator (E₂ ≫ F₂) F₁ E₁).inv ≫ (associator E₂ F₂ F₁).hom ▷ E₁ =
    (leftUnitor F₁).inv ▷ E₁ ≫ (A₂.unit ▷ F₁) ▷ E₁ ≫
    (associator E₂ F₂ F₁).hom ▷ E₁ at hp
  change (associator E₂ (F₂ ≫ F₁) E₁).hom ≫
    E₂ ◁ (associator F₂ F₁ E₁).hom ≫ E₂ ◁ (F₂ ◁ A₁.counit) ≫
    E₂ ◁ (rightUnitor F₂).hom =
    (associator E₂ F₂ F₁).inv ▷ E₁ ≫ (associator (E₂ ≫ F₂) F₁ E₁).hom ≫
    (E₂ ≫ F₂) ◁ A₁.counit ≫ (rightUnitor (E₂ ≫ F₂)).hom at hs
  rw [mixedMateBend_symm_apply]
  change (leftUnitor (F₁ ≫ E₁)).inv ≫ A₂.unit ▷ (F₁ ≫ E₁) ≫
    (associator (E₂ ≫ F₂) F₁ E₁).inv ≫ (associator E₂ F₂ F₁).hom ▷ E₁ ≫
    (E₂ ◁ v) ▷ E₁ ≫ (associator E₂ (F₂ ≫ F₁) E₁).hom ≫
    E₂ ◁ (associator F₂ F₁ E₁).hom ≫ E₂ ◁ (F₂ ◁ A₁.counit) ≫
    E₂ ◁ (rightUnitor F₂).hom = _
  rw [hs]
  simp only [← Category.assoc] at hp ⊢
  rw [hp]
  simp only [TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]

end OddMath.SKM
