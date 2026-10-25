import OddMath.SKM.RouquierHomAdjunction

/-!
# The actual super Rouquier mate as a Hom equivalence

Ports the mate calculation underlying
`Categorification/TwoRep/RouqProductKLR.lean`. Both adjunctions act on full
super Hom categories. The resulting bijection is a bijection of Hom spaces,
not a statement that taking mates preserves invertible morphisms.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- The two adjunction transposes and the associator, in their fixed order. -/
def homMateEquiv {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (g : a ⟶ b) (h : b ⟶ c) :
    (g ≫ E₂ ⟶ E₁ ≫ h) ≃ (F₁ ≫ g ⟶ h ≫ F₂) :=
  ((homPostAdjunction A₂).homEquiv g (E₁ ≫ h)).trans
    ((Iso.homCongr (Iso.refl g) (associator E₁ h F₂)).trans
      ((homPreAdjunction A₁).homEquiv g (h ≫ F₂)).symm)

private theorem matePrefix {C : Type u} [Bicategory.{w,v} C]
    {a b c : C} (E : a ⟶ b) (F : b ⟶ a) (H : b ⟶ c) (K : c ⟶ b)
    (η : 𝟙 b ⟶ H ≫ K) :
    (Bicategory.rightUnitor (F ≫ E)).inv ≫ Bicategory.whiskerLeft (F ≫ E) η ≫
      (Bicategory.associator F E (H ≫ K)).hom ≫
      Bicategory.whiskerLeft F (Bicategory.associator E H K).inv =
    Bicategory.whiskerLeft F ((Bicategory.rightUnitor E).inv ≫
      Bicategory.whiskerLeft E η ≫ (Bicategory.associator E H K).inv) := by
  bicategory

private theorem suffix {C : Type u} [Bicategory.{w,v} C]
    {a b c : C} (E : a ⟶ b) (F : b ⟶ a) (H : b ⟶ c) (K : c ⟶ b)
    (ε : F ≫ E ⟶ 𝟙 b) :
    (Bicategory.associator F (E ≫ H) K).inv ≫
      Bicategory.whiskerRight (Bicategory.associator F E H).inv K ≫
      Bicategory.whiskerRight (Bicategory.whiskerRight ε H) K ≫
      Bicategory.whiskerRight (Bicategory.leftUnitor H).hom K =
    Bicategory.whiskerLeft F (Bicategory.associator E H K).hom ≫
      (Bicategory.associator F E (H ≫ K)).inv ≫
      Bicategory.whiskerRight ε (H ≫ K) ≫ (Bicategory.leftUnitor (H ≫ K)).hom := by
  bicategory

/-- The interface's cup–crossing–cap map is this Hom equivalence, including
for odd crossings. Only the even prefix and suffix use ordinary coherence. -/
theorem homMateEquiv_eq {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    homMateEquiv A₁ A₂ E₁ E₂ t = rouquierMate A₁ A₂ t := by
  have hp := congrArg Subtype.val (matePrefix
    (Underlying2.hom1 (R := k) E₁) (Underlying2.hom1 (R := k) F₁)
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂)
    ⟨A₂.unit, A₂.unit_mem⟩)
  have hs := congrArg Subtype.val (suffix
    (Underlying2.hom1 (R := k) E₁) (Underlying2.hom1 (R := k) F₁)
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂)
    ⟨A₁.counit, A₁.counit_mem⟩)
  change (rightUnitor (F₁ ≫ E₁)).inv ≫ (F₁ ≫ E₁) ◁ A₂.unit ≫
    (associator F₁ E₁ (E₂ ≫ F₂)).hom ≫ F₁ ◁ (associator E₁ E₂ F₂).inv =
      F₁ ◁ ((rightUnitor E₁).inv ≫ E₁ ◁ A₂.unit ≫ (associator E₁ E₂ F₂).inv) at hp
  change (associator F₁ (E₁ ≫ E₂) F₂).inv ≫
    (associator F₁ E₁ E₂).inv ▷ F₂ ≫ (A₁.counit ▷ E₂) ▷ F₂ ≫
      (leftUnitor E₂).hom ▷ F₂ =
    F₁ ◁ (associator E₁ E₂ F₂).hom ≫ (associator F₁ E₁ (E₂ ≫ F₂)).inv ≫
      A₁.counit ▷ (E₂ ≫ F₂) ≫ (leftUnitor (E₂ ≫ F₂)).hom at hs
  dsimp [homMateEquiv, CategoryTheory.Adjunction.homEquiv, homPostAdjunction,
    homPreAdjunction, homPostUnit, homPreCounit, homPostId, homPostComp,
    homPreId, homPreComp, homPostTransform, homPreTransform,
    SuperNatTrans.toNatTrans, homPost, homPre, Iso.homCongr]
  unfold rouquierMate
  rw [hs]
  simp only [← Category.assoc] at hp ⊢
  rw [hp]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc,
    Category.id_comp]

/-- Naturality on the input strand; the adjunctions are even, so no extra sign occurs. -/
theorem homMateEquiv_left {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    {g g' : a ⟶ b} (h : b ⟶ c) (x : g ⟶ g') (t : g' ≫ E₂ ⟶ E₁ ≫ h) :
    homMateEquiv A₁ A₂ g h (x ▷ E₂ ≫ t) =
      F₁ ◁ x ≫ homMateEquiv A₁ A₂ g' h t := by
  have h₁ := (homPostAdjunction A₂).homEquiv_naturality_left x t
  have h₂ := (homPreAdjunction A₁).homEquiv_naturality_left_symm x
    ((homPostAdjunction A₂).homEquiv g' (E₁ ≫ h) t ≫ (associator E₁ h F₂).hom)
  have h₃ := congrArg (fun z => ((homPreAdjunction A₁).homEquiv g (h ≫ F₂)).symm
    (z ≫ (associator E₁ h F₂).hom)) h₁
  have h₄ := h₃.trans (by simpa only [Category.assoc] using h₂)
  simpa [homMateEquiv, Iso.homCongr, homPreAdjunction, homPostAdjunction,
    CategoryTheory.Adjunction.homEquiv, homPre, homPost, Category.assoc] using h₄

/-- Naturality on the output strand, before imposing any dot-slide relation. -/
theorem homMateEquiv_right {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (g : a ⟶ b) {h h' : b ⟶ c} (y : h ⟶ h') (t : g ≫ E₂ ⟶ E₁ ≫ h) :
    homMateEquiv A₁ A₂ g h' (t ≫ E₁ ◁ y) =
      homMateEquiv A₁ A₂ g h t ≫ y ▷ F₂ := by
  have h₁ := (homPostAdjunction A₂).homEquiv_naturality_right t (E₁ ◁ y)
  have h₂ := (homPreAdjunction A₁).homEquiv_naturality_right_symm
    ((homPostAdjunction A₂).homEquiv g (E₁ ≫ h) t ≫ (associator E₁ h F₂).hom) (y ▷ F₂)
  have h₃ := congrArg (fun z => ((homPreAdjunction A₁).homEquiv g (h' ≫ F₂)).symm
    (z ≫ (associator E₁ h' F₂).hom)) h₁
  have hmid : ((homPostAdjunction A₂).homEquiv g (E₁ ≫ h) t ≫
      (homPost (k := k) F₂).map (E₁ ◁ y)) ≫ (associator E₁ h' F₂).hom =
    ((homPostAdjunction A₂).homEquiv g (E₁ ≫ h) t ≫ (associator E₁ h F₂).hom) ≫
      (homPre (k := k) E₁).map (y ▷ F₂) := by
    change (_ ≫ (E₁ ◁ y) ▷ F₂) ≫ _ = (_ ≫ _) ≫ E₁ ◁ (y ▷ F₂)
    rw [Category.assoc, TwoSupercategory.associator_naturality_middle (R := k), Category.assoc]
  have h₄ := h₃.trans ((congrArg ((homPreAdjunction A₁).homEquiv g (h' ≫ F₂)).symm hmid).trans h₂)
  simpa [homMateEquiv, Iso.homCongr, homPreAdjunction, homPostAdjunction,
    CategoryTheory.Adjunction.homEquiv, homPre, homPost, Category.assoc] using h₄

private theorem ordinaryMateId {C : Type u} [Bicategory.{w,v} C]
    {a b c : C} (E : a ⟶ b) (F : b ⟶ a) (H : b ⟶ c) (K : c ⟶ b)
    (η : 𝟙 b ⟶ H ≫ K) (ε : F ≫ E ⟶ 𝟙 b) :
    Bicategory.whiskerLeft F ((Bicategory.rightUnitor E).inv ≫ Bicategory.whiskerLeft E η) ≫
      (Bicategory.associator F E (H ≫ K)).inv ≫
      Bicategory.whiskerRight ε (H ≫ K) ≫ (Bicategory.leftUnitor (H ≫ K)).hom = ε ≫ η := by
  calc
    _ = (Bicategory.rightUnitor (F ≫ E)).inv ≫ Bicategory.whiskerLeft (F ≫ E) η ≫
      Bicategory.whiskerRight ε (H ≫ K) ≫ (Bicategory.leftUnitor (H ≫ K)).hom := by
        bicategory
    _ = (Bicategory.rightUnitor (F ≫ E)).inv ≫ Bicategory.whiskerRight ε (𝟙 b) ≫
      Bicategory.whiskerLeft (𝟙 b) η ≫ (Bicategory.leftUnitor (H ≫ K)).hom := by
        rw [Bicategory.whisker_exchange_assoc]
    _ = _ := by bicategory

/-- The identity crossing transposes to the disconnected counit–unit composite. -/
theorem rouquierMate_id {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂) :
    rouquierMate A₁ A₂ (𝟙 (E₁ ≫ E₂)) = A₁.counit ≫ A₂.unit := by
  have h := congrArg Subtype.val (ordinaryMateId
    (Underlying2.hom1 (R := k) E₁) (Underlying2.hom1 (R := k) F₁)
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂)
    ⟨A₂.unit, A₂.unit_mem⟩ ⟨A₁.counit, A₁.counit_mem⟩)
  change F₁ ◁ ((rightUnitor E₁).inv ≫ E₁ ◁ A₂.unit) ≫
    (associator F₁ E₁ (E₂ ≫ F₂)).inv ≫ A₁.counit ▷ (E₂ ≫ F₂) ≫
      (leftUnitor (E₂ ≫ F₂)).hom = A₁.counit ≫ A₂.unit at h
  rw [← homMateEquiv_eq]
  simpa [homMateEquiv, CategoryTheory.Adjunction.homEquiv, homPostAdjunction,
    homPreAdjunction, homPostUnit, homPreCounit, homPostId, homPostComp,
    homPreId, homPreComp, homPostTransform, homPreTransform,
    SuperNatTrans.toNatTrans, homPost, homPre, Iso.homCongr,
    TwoSupercategory.id_whiskerRight (R := k), Category.assoc] using h

/-- The actual mate depends linearly on the crossing; composition order is retained. -/
def rouquierMateLinear {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂) :
    (E₁ ≫ E₂ ⟶ E₁ ≫ E₂) →ₗ[k] (F₁ ≫ E₁ ⟶ E₂ ≫ F₂) where
  toFun := rouquierMate A₁ A₂
  map_add' t s := by
    simp [rouquierMate, TwoSupercategory.add_whiskerRight (R := k),
      TwoSupercategory.whiskerLeft_add (R := k), Preadditive.comp_add, Preadditive.add_comp]
  map_smul' r t := by
    simp [rouquierMate, TwoSupercategory.smul_whiskerRight,
      TwoSupercategory.whiskerLeft_smul, Linear.comp_smul, Linear.smul_comp]

/-- The dot-slide relation for the actual mate at arbitrary local content.
This precedes, but does not replace, the coupled-sector projection calculation. -/
theorem rouquierMate_slide {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (x₁ : E₁ ⟶ E₁) (x₂ : E₂ ⟶ E₂) (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (q : k)
    (hslide : t ≫ E₁ ◁ x₂ - q • (x₁ ▷ E₂ ≫ t) = 𝟙 _) :
    rouquierMate A₁ A₂ t ≫ x₂ ▷ F₂ - q • (F₁ ◁ x₁ ≫ rouquierMate A₁ A₂ t) =
      A₁.counit ≫ A₂.unit := by
  have h := congrArg (rouquierMateLinear A₁ A₂) hslide
  rw [map_sub, map_smul] at h
  change rouquierMate A₁ A₂ (t ≫ E₁ ◁ x₂) -
    q • rouquierMate A₁ A₂ (x₁ ▷ E₂ ≫ t) = rouquierMate A₁ A₂ (𝟙 _) at h
  simp only [← homMateEquiv_eq, homMateEquiv_right, homMateEquiv_left] at h
  simpa only [homMateEquiv_eq, rouquierMate_id] using h

/-- The local super Rouquier datum supplies the signed slide of its actual mate.
The inverse fields are not used in the proof. -/
theorem SuperRouquierLoc.mate_slide {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
    {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}
    {p : ZMod 2} {h : ℤ} (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h) :
    rouquierMate A₁ A₂ t ≫ x₂ ▷ F₂ -
      koszulSign p p • (F₁ ◁ x₁ ≫ rouquierMate A₁ A₂ t) = A₁.counit ≫ A₂.unit := by
  simpa only [Int.cast_smul_eq_zsmul] using
    rouquierMate_slide A₁ A₂ x₁ x₂ t ((koszulSign p p : ℤ) : k)
      (by simpa only [Int.cast_smul_eq_zsmul] using L.slide_right)

end OddMath.SKM
