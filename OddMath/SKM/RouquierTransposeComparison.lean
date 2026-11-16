import OddMath.SKM.RouquierCompositeAdjunction
import OddMath.SKM.RouquierRightTranspose
import OddMath.SKM.RouquierMixedMate

/-!
# Partial mates and composite right transposition

The comparison in `SignedFTriangle`, §3, (8)–(9), needed for the reflection
in Brundan, arXiv:1501.00350v1, Theorem 4.3. All Hom spaces retain odd maps.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

private theorem compositeCap {C : Type u} [Bicategory.{w,v} C]
    {a b c : C} (E₁ : a ⟶ b) (F₁ : b ⟶ a) (E₂ : b ⟶ c) (F₂ : c ⟶ b)
    (ε₁ : F₁ ≫ E₁ ⟶ 𝟙 b) (ε₂ : F₂ ≫ E₂ ⟶ 𝟙 c) :
    (Bicategory.associator (F₂ ≫ F₁) E₁ E₂).hom ≫
      (Bicategory.associator F₂ F₁ (E₁ ≫ E₂)).hom ≫
      Bicategory.whiskerLeft F₂ (Bicategory.associator F₁ E₁ E₂).inv ≫
      Bicategory.whiskerLeft F₂ (Bicategory.whiskerRight ε₁ E₂) ≫
      Bicategory.whiskerLeft F₂ (Bicategory.leftUnitor E₂).hom ≫ ε₂ =
    Bicategory.whiskerRight ((Bicategory.associator F₂ F₁ E₁).hom ≫
      Bicategory.whiskerLeft F₂ ε₁ ≫ (Bicategory.rightUnitor F₂).hom) E₂ ≫ ε₂ := by
  bicategory

private theorem doubleCap {C : Type u} [Bicategory.{w,v} C]
    {b c : C} (E : b ⟶ c) (F : c ⟶ b) (ε : F ≫ E ⟶ 𝟙 c) :
    Bicategory.whiskerRight ((Bicategory.associator F E F).inv ≫
      Bicategory.whiskerRight ε F ≫ (Bicategory.leftUnitor F).hom) E ≫ ε =
    (Bicategory.associator F (E ≫ F) E).hom ≫
      Bicategory.whiskerLeft F ((Bicategory.associator E F E).hom ≫
        Bicategory.whiskerLeft E ε ≫ (Bicategory.rightUnitor E).hom) ≫ ε := by
  calc
    _ = Bicategory.whiskerRight (Bicategory.associator F E F).inv E ≫
        (Bicategory.associator (F ≫ E) F E).hom ≫
        Bicategory.whiskerRight ε (F ≫ E) ≫
        Bicategory.whiskerLeft (𝟙 c) ε ≫ (Bicategory.leftUnitor (𝟙 c)).hom := by
      bicategory
    _ = Bicategory.whiskerRight (Bicategory.associator F E F).inv E ≫
        (Bicategory.associator (F ≫ E) F E).hom ≫
        Bicategory.whiskerLeft (F ≫ E) ε ≫
        Bicategory.whiskerRight ε (𝟙 c) ≫ (Bicategory.leftUnitor (𝟙 c)).hom := by
      rw [← Category.assoc (Bicategory.whiskerRight ε (F ≫ E)),
        ← Bicategory.whisker_exchange, Category.assoc]
    _ = _ := by bicategory

variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
  {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)

/-- The remaining two bends, in the precise weight sectors of the reflection. -/
def mixedMateBend : (F₁ ≫ E₁ ⟶ E₂ ≫ F₂) ≃ (F₂ ≫ F₁ ⟶ F₂ ≫ F₁) :=
  rectangularMate A₂ A₁ F₁ F₂

/-- The inverse is the reflected unit–map–counit composite, with its brackets explicit. -/
theorem mixedMateBend_symm_apply (v : F₂ ≫ F₁ ⟶ F₂ ≫ F₁) :
    (mixedMateBend A₁ A₂).symm v =
      ((leftUnitor F₁).inv ≫ A₂.unit ▷ F₁ ≫ (associator E₂ F₂ F₁).hom ≫
        E₂ ◁ v ≫ (associator E₂ F₂ F₁).inv) ▷ E₁ ≫
      (associator (E₂ ≫ F₂) F₁ E₁).hom ≫ (E₂ ≫ F₂) ◁ A₁.counit ≫
      (rightUnitor (E₂ ≫ F₂)).hom := by
  simp [mixedMateBend, rectangularMate, Iso.homCongr,
    CategoryTheory.Adjunction.homEquiv, homPreAdjunction, homPreUnit,
    homPreId, homPreComp, homPreTransform, homPostAdjunction, homPostCounit,
    homPostId, homPostComp, homPostTransform, SuperNatTrans.toNatTrans,
    homPre, homPost, Category.assoc]

private theorem mixedMateBend_cap (u : F₁ ≫ E₁ ⟶ E₂ ≫ F₂) :
    mixedMateBend A₁ A₂ u ▷ E₁ ≫ (associator F₂ F₁ E₁).hom ≫
      F₂ ◁ A₁.counit ≫ (rightUnitor F₂).hom =
    (associator F₂ F₁ E₁).hom ≫ F₂ ◁ u ≫
      (associator F₂ E₂ F₂).inv ≫ A₂.counit ▷ F₂ ≫ (leftUnitor F₂).hom := by
  have h := congrArg ((homPostAdjunction A₁).homEquiv (F₂ ≫ F₁) F₂).symm
    (rectangularMate_postTranspose A₂ A₁ F₁ F₂ u)
  rw [Equiv.symm_apply_apply] at h
  simpa [mixedMateBend, CategoryTheory.Adjunction.homEquiv, homPostAdjunction,
    homPostCounit, homPostComp, homPostTransform, homPostId,
    SuperNatTrans.toNatTrans, homPost, Category.assoc] using h

private theorem bend_composite_cap (u : F₁ ≫ E₁ ⟶ E₂ ≫ F₂) :
    mixedMateBend A₁ A₂ u ▷ (E₁ ≫ E₂) ≫ (A₁.comp A₂).counit =
    (associator F₂ F₁ (E₁ ≫ E₂)).hom ≫
      F₂ ◁ (associator F₁ E₁ E₂).inv ≫
      F₂ ◁ (u ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
        E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom) ≫ A₂.counit := by
  have hc := congrArg Subtype.val (compositeCap
    (Underlying2.hom1 (R := k) E₁) (Underlying2.hom1 (R := k) F₁)
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂)
    ⟨A₁.counit, A₁.counit_mem⟩ ⟨A₂.counit, A₂.counit_mem⟩)
  change (associator (F₂ ≫ F₁) E₁ E₂).hom ≫
    (associator F₂ F₁ (E₁ ≫ E₂)).hom ≫ F₂ ◁ (associator F₁ E₁ E₂).inv ≫
    F₂ ◁ (A₁.counit ▷ E₂) ≫ F₂ ◁ (leftUnitor E₂).hom ≫ A₂.counit =
    ((associator F₂ F₁ E₁).hom ≫ F₂ ◁ A₁.counit ≫ (rightUnitor F₂).hom) ▷ E₂ ≫
      A₂.counit at hc
  have hd := congrArg Subtype.val (doubleCap
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂)
    ⟨A₂.counit, A₂.counit_mem⟩)
  change ((associator F₂ E₂ F₂).inv ≫ A₂.counit ▷ F₂ ≫ (leftUnitor F₂).hom) ▷ E₂ ≫
    A₂.counit = (associator F₂ (E₂ ≫ F₂) E₂).hom ≫
    F₂ ◁ ((associator E₂ F₂ E₂).hom ≫ E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom) ≫
    A₂.counit at hd
  rw [SuperAdjunction.comp_counit, TwoSupercategory.whiskerRight_comp (R := k)]
  simp only [Category.assoc]
  rw [hc, ← reassoc_of% (TwoSupercategory.comp_whiskerRight (R := k)
    (mixedMateBend A₁ A₂ u ▷ E₁)
    ((associator F₂ F₁ E₁).hom ≫ F₂ ◁ A₁.counit ≫ (rightUnitor F₂).hom) E₂)]
  rw [mixedMateBend_cap]
  simp only [TwoSupercategory.comp_whiskerRight (R := k), Category.assoc] at hd ⊢
  rw [hd, TwoSupercategory.associator_naturality_middle_assoc (R := k)]
  have hp := TwoSupercategory.pentagon (R := k) F₂ F₁ E₁ E₂
  have hp' := congrArg (fun z => (associator (F₂ ≫ F₁) E₁ E₂).inv ≫ z ≫
    F₂ ◁ (associator F₁ E₁ E₂).inv) hp
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    TwoSupercategory.whiskerLeft_hom_inv (R := k), Category.comp_id] at hp'
  rw [← reassoc_of% hp']
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]

/-- The two partial mates are the right transpose for the composite adjunction. -/
theorem mixedMateBend_rouquierMate (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    mixedMateBend A₁ A₂ (rouquierMate A₁ A₂ t) =
      SuperAdjunction.rightTranspose (A₁.comp A₂) (A₁.comp A₂) t := by
  symm
  apply SuperAdjunction.rightTranspose_eq
  rw [bend_composite_cap, rouquierMate_pitchfork_cap, SuperAdjunction.comp_counit]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc,
    TwoSupercategory.whiskerLeft_inv_hom_assoc (R := k)]
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k)]

/-- The inverse remaining bends recover the prescribed mixed cup–map–cap. -/
theorem mixedMateBend_symm_rightTranspose (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    (mixedMateBend A₁ A₂).symm
      (SuperAdjunction.rightTranspose (A₁.comp A₂) (A₁.comp A₂) t) =
      rouquierMate A₁ A₂ t := by
  rw [← mixedMateBend_rouquierMate]
  exact (mixedMateBend A₁ A₂).symm_apply_apply _

end OddMath.SKM
