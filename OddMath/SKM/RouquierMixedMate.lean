import OddMath.SKM.RouquierMate

/-!
# Rectangular outer mates for the mixed braid

Composition is diagrammatic. The outer adjunctions need not be adjacent:
`E₁ : a ⟶ b` and `E₃ : c ⟶ d`. All their units and counits are even.
The rectangular transpose retains arbitrary, including odd, Hom morphisms.
The two-mate expansion has coefficient `koszulSign p p`; rectangular
naturality and the upward braid give the mixed braid with coefficient one.
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

private theorem outerCup {C : Type u} [Bicategory.{w,v} C]
    {a b c d : C} (L : a ⟶ b) (G : b ⟶ c) (E : c ⟶ d) (F : d ⟶ c)
    (η : 𝟙 c ⟶ E ≫ F) :
    Bicategory.whiskerLeft L ((Bicategory.rightUnitor G).inv ≫
      Bicategory.whiskerLeft G η ≫ (Bicategory.associator G E F).inv) =
    (Bicategory.rightUnitor (L ≫ G)).inv ≫ Bicategory.whiskerLeft (L ≫ G) η ≫
      (Bicategory.associator (L ≫ G) E F).inv ≫
      Bicategory.whiskerRight (Bicategory.associator L G E).hom F ≫
      (Bicategory.associator L (G ≫ E) F).hom := by bicategory

private theorem postLeft {a b c d : B} (L : a ⟶ b) (G : b ⟶ c)
    {E : c ⟶ d} {F : d ⟶ c} (A : SuperAdjunction (k := k) E F)
    (H : b ⟶ d) (z : G ≫ E ⟶ H) :
    L ◁ ((homPostAdjunction A).homEquiv G H z) ≫ (associator L H F).inv =
    (homPostAdjunction A).homEquiv (L ≫ G) (L ≫ H)
      ((associator L G E).hom ≫ L ◁ z) := by
  have hp := congrArg Subtype.val (outerCup
    (Underlying2.hom1 (R := k) L) (Underlying2.hom1 (R := k) G)
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) F)
    ⟨A.unit, A.unit_mem⟩)
  change L ◁ ((rightUnitor G).inv ≫ G ◁ A.unit ≫ (associator G E F).inv) =
    (rightUnitor (L ≫ G)).inv ≫ (L ≫ G) ◁ A.unit ≫
      (associator (L ≫ G) E F).inv ≫ (associator L G E).hom ▷ F ≫
      (associator L (G ≫ E) F).hom at hp
  dsimp [CategoryTheory.Adjunction.homEquiv, homPostAdjunction, homPostUnit,
    homPostId, homPostComp, homPostTransform, SuperNatTrans.toNatTrans, homPost]
  change L ◁ (((rightUnitor G).inv ≫ G ◁ A.unit ≫
    (associator G E F).inv) ≫ z ▷ F) ≫ _ =
    ((rightUnitor (L ≫ G)).inv ≫ (L ≫ G) ◁ A.unit ≫
    (associator (L ≫ G) E F).inv) ≫ _
  rw [TwoSupercategory.whiskerLeft_comp (R := k), hp]
  simp only [TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]
  rw [← TwoSupercategory.associator_naturality_middle_assoc (R := k)]
  simp only [Iso.hom_inv_id, Category.comp_id]

private theorem capSuffix {C : Type u} [Bicategory.{w,v} C]
    {a b c : C} (E : a ⟶ b) (F : b ⟶ a) (G : b ⟶ c)
    (ε : F ≫ E ⟶ 𝟙 b) :
    (Bicategory.associator E F (E ≫ G)).hom ≫
      Bicategory.whiskerLeft E (Bicategory.associator F E G).inv ≫
      Bicategory.whiskerLeft E (Bicategory.whiskerRight ε G) ≫
      Bicategory.whiskerLeft E (Bicategory.leftUnitor G).hom =
    (Bicategory.associator (E ≫ F) E G).inv ≫
      Bicategory.whiskerRight ((Bicategory.associator E F E).hom ≫
        Bicategory.whiskerLeft E ε ≫ (Bicategory.rightUnitor E).hom) G := by bicategory

private theorem outerCap {C : Type u} [Bicategory.{w,v} C]
    {a b c d : C} (F : b ⟶ a) (E : a ⟶ b) (H : b ⟶ d) (K : d ⟶ c)
    (ε : F ≫ E ⟶ 𝟙 b) :
    Bicategory.whiskerLeft F (Bicategory.associator E H K).hom ≫
      (Bicategory.associator F E (H ≫ K)).inv ≫
      Bicategory.whiskerRight ε (H ≫ K) ≫ (Bicategory.leftUnitor (H ≫ K)).hom =
    (Bicategory.associator F (E ≫ H) K).inv ≫
      Bicategory.whiskerRight ((Bicategory.associator F E H).inv ≫
        Bicategory.whiskerRight ε H ≫ (Bicategory.leftUnitor H).hom) K := by bicategory

private theorem rectanglePost {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₃ : c ⟶ d} {F₃ : d ⟶ c}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₃ : SuperAdjunction (k := k) E₃ F₃)
    (g : a ⟶ c) (h : b ⟶ d) (z : g ≫ E₃ ⟶ E₁ ≫ h) :
    rectangularMate A₁ A₃ g h z =
      (homPostAdjunction A₃).homEquiv (F₁ ≫ g) h
        ((associator F₁ g E₃).hom ≫ F₁ ◁ z ≫ (associator F₁ E₁ h).inv ≫
          A₁.counit ▷ h ≫ (leftUnitor h).hom) := by
  have hs := congrArg Subtype.val (outerCap
    (Underlying2.hom1 (R := k) F₁) (Underlying2.hom1 (R := k) E₁)
    (Underlying2.hom1 (R := k) h) (Underlying2.hom1 (R := k) F₃)
    ⟨A₁.counit, A₁.counit_mem⟩)
  change F₁ ◁ (associator E₁ h F₃).hom ≫ (associator F₁ E₁ (h ≫ F₃)).inv ≫
    A₁.counit ▷ (h ≫ F₃) ≫ (leftUnitor (h ≫ F₃)).hom =
    (associator F₁ (E₁ ≫ h) F₃).inv ≫
      ((associator F₁ E₁ h).inv ≫ A₁.counit ▷ h ≫ (leftUnitor h).hom) ▷ F₃ at hs
  have hl := postLeft F₁ g A₃ (E₁ ≫ h) z
  have hn := (homPostAdjunction A₃).homEquiv_naturality_right
    ((associator F₁ g E₃).hom ≫ F₁ ◁ z)
    ((associator F₁ E₁ h).inv ≫ A₁.counit ▷ h ≫ (leftUnitor h).hom)
  have he := congrArg (fun q => q ≫
    ((associator F₁ E₁ h).inv ≫ A₁.counit ▷ h ≫ (leftUnitor h).hom) ▷ F₃) hl
  trans F₁ ◁ ((homPostAdjunction A₃).homEquiv g (E₁ ≫ h) z) ≫
    (associator F₁ (E₁ ≫ h) F₃).inv ≫
    ((associator F₁ E₁ h).inv ≫ A₁.counit ▷ h ≫ (leftUnitor h).hom) ▷ F₃
  · rw [rectangularMate_eq]
    change _ = F₁ ◁ (((rightUnitor g).inv ≫ g ◁ A₃.unit ≫
      (associator g E₃ F₃).inv) ≫ z ▷ F₃) ≫
      (associator F₁ (E₁ ≫ h) F₃).inv ≫
      ((associator F₁ E₁ h).inv ≫ A₁.counit ▷ h ≫ (leftUnitor h).hom) ▷ F₃
    simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
    rw [hs]
  · simpa only [homPost, Category.assoc] using he.trans hn.symm

section Expansion
variable {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
  {E₂ : b ⟶ c} {F₂ : c ⟶ b} {E₃ : c ⟶ d} {F₃ : d ⟶ c}
  (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
  (A₃ : SuperAdjunction (k := k) E₃ F₃)
  {p : ZMod 2} {t₁₂ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {t₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃}
  (h₁₂ : t₁₂ ∈ parity (R := k) _ _ p) (h₂₃ : t₂₃ ∈ parity (R := k) _ _ p)

private theorem expandPost :
    rouquierMate A₁ A₂ t₁₂ ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
      E₂ ◁ rouquierMate A₂ A₃ t₂₃ ≫ (associator E₂ E₃ F₃).inv =
    (homPostAdjunction A₃).homEquiv ((F₁ ≫ E₁) ≫ E₂) (E₂ ≫ E₃)
      (((rouquierMate A₁ A₂ t₁₂ ▷ E₂) ≫ (associator E₂ F₂ E₂).hom) ▷ E₃ ≫
        (associator E₂ (F₂ ≫ E₂) E₃).hom ≫
        E₂ ◁ ((associator F₂ E₂ E₃).hom ≫ F₂ ◁ t₂₃ ≫
          (associator F₂ E₂ E₃).inv ≫ A₂.counit ▷ E₃ ≫ (leftUnitor E₃).hom)) := by
  have hl := postLeft E₂ (F₂ ≫ E₂) A₃ E₃
    ((associator F₂ E₂ E₃).hom ≫ F₂ ◁ t₂₃ ≫
      (associator F₂ E₂ E₃).inv ≫ A₂.counit ▷ E₃ ≫ (leftUnitor E₃).hom)
  have hn := (homPostAdjunction A₃).homEquiv_naturality_left
      ((rouquierMate A₁ A₂ t₁₂ ▷ E₂) ≫ (associator E₂ F₂ E₂).hom)
      ((associator E₂ (F₂ ≫ E₂) E₃).hom ≫
        E₂ ◁ ((associator F₂ E₂ E₃).hom ≫ F₂ ◁ t₂₃ ≫
          (associator F₂ E₂ E₃).inv ≫ A₂.counit ▷ E₃ ≫ (leftUnitor E₃).hom))
  have hm := congrArg (fun z => rouquierMate A₁ A₂ t₁₂ ▷ E₂ ≫
    (associator E₂ F₂ E₂).hom ≫ z) hl
  have he := congrArg (fun z => rouquierMate A₁ A₂ t₁₂ ▷ E₂ ≫
    (associator E₂ F₂ E₂).hom ≫ E₂ ◁ z ≫ (associator E₂ E₃ F₃).inv)
    (rouquierMate_postTranspose A₂ A₃ t₂₃)
  exact he.trans (hm.trans (by simpa only [homPost, Category.assoc] using hn.symm))
include h₁₂ h₂₃ in
private theorem innerExpansion :
    (((rouquierMate A₁ A₂ t₁₂ ▷ E₂) ≫ (associator E₂ F₂ E₂).hom) ▷ E₃ ≫
      (associator E₂ (F₂ ≫ E₂) E₃).hom ≫
      E₂ ◁ ((associator F₂ E₂ E₃).hom ≫ F₂ ◁ t₂₃ ≫
        (associator F₂ E₂ E₃).inv ≫ A₂.counit ▷ E₃ ≫ (leftUnitor E₃).hom)) =
    koszulSign p p • ((associator (F₁ ≫ E₁) E₂ E₃).hom ≫
      (F₁ ≫ E₁) ◁ t₂₃ ≫ (associator (F₁ ≫ E₁) E₂ E₃).inv ≫
      ((associator F₁ E₁ E₂).hom ≫ F₁ ◁ t₁₂ ≫ (associator F₁ E₁ E₂).inv ≫
        A₁.counit ▷ E₂ ≫ (leftUnitor E₂).hom) ▷ E₃) := by
  have hs := congrArg Subtype.val (capSuffix
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂)
    (Underlying2.hom1 (R := k) E₃) ⟨A₂.counit, A₂.counit_mem⟩)
  change (associator E₂ F₂ (E₂ ≫ E₃)).hom ≫
    E₂ ◁ (associator F₂ E₂ E₃).inv ≫ E₂ ◁ (A₂.counit ▷ E₃) ≫
    E₂ ◁ (leftUnitor E₃).hom =
    (associator (E₂ ≫ F₂) E₂ E₃).inv ≫
    ((associator E₂ F₂ E₂).hom ≫ E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom) ▷ E₃ at hs
  have hp := TwoSupercategory.pentagon (R := k) E₂ F₂ E₂ E₃
  have hn := TwoSupercategory.associator_naturality_left (R := k)
    (rouquierMate A₁ A₂ t₁₂) E₂ E₃
  simp only [TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [reassoc_of% hp]
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k)]
  rw [hs, reassoc_of% hn]
  rw [reassoc_of% (rouquierMate_cross_interchange A₁ A₂ h₁₂ h₂₃)]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  congr 1
  rw [TwoSupercategory.whiskerRight_comp (R := k)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← TwoSupercategory.comp_whiskerRight (R := k)]
  rw [rouquierMate_pitchfork_cap]
  simp only [TwoSupercategory.comp_whiskerRight (R := k)]
private theorem outerInput :
    (associator F₁ E₁ E₂).hom ▷ E₃ ≫ (associator F₁ (E₁ ≫ E₂) E₃).hom ≫
      F₁ ◁ ((associator E₁ E₂ E₃).hom ≫ E₁ ◁ t₂₃ ≫
        (associator E₁ E₂ E₃).inv ≫ t₁₂ ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      (associator F₁ E₁ (E₂ ≫ E₃)).inv ≫ A₁.counit ▷ (E₂ ≫ E₃) ≫
      (leftUnitor (E₂ ≫ E₃)).hom =
    (associator (F₁ ≫ E₁) E₂ E₃).hom ≫ (F₁ ≫ E₁) ◁ t₂₃ ≫
      (associator (F₁ ≫ E₁) E₂ E₃).inv ≫
      ((associator F₁ E₁ E₂).hom ≫ F₁ ◁ t₁₂ ≫ (associator F₁ E₁ E₂).inv ≫
        A₁.counit ▷ E₂ ≫ (leftUnitor E₂).hom) ▷ E₃ := by
  have hs := congrArg Subtype.val (outerCap
    (Underlying2.hom1 (R := k) F₁) (Underlying2.hom1 (R := k) E₁)
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) E₃)
    ⟨A₁.counit, A₁.counit_mem⟩)
  change F₁ ◁ (associator E₁ E₂ E₃).hom ≫ (associator F₁ E₁ (E₂ ≫ E₃)).inv ≫
    A₁.counit ▷ (E₂ ≫ E₃) ≫ (leftUnitor (E₂ ≫ E₃)).hom =
    (associator F₁ (E₁ ≫ E₂) E₃).inv ≫
      ((associator F₁ E₁ E₂).inv ≫ A₁.counit ▷ E₂ ≫ (leftUnitor E₂).hom) ▷ E₃ at hs
  have hp := TwoSupercategory.pentagon (R := k) F₁ E₁ E₂ E₃
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [hs]
  rw [reassoc_of% hp]
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k)]
  rw [TwoSupercategory.associator_inv_naturality_middle_assoc (R := k)]
  have hc := congrArg (fun z => (associator (F₁ ≫ E₁) E₂ E₃).inv ≫ z ≫
    F₁ ◁ (associator E₁ E₂ E₃).inv ≫ (associator F₁ (E₁ ≫ E₂) E₃).inv) hp
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    TwoSupercategory.whiskerLeft_hom_inv_assoc (R := k), Iso.hom_inv_id,
    Category.comp_id] at hc
  rw [← reassoc_of% hc]
  simp only [TwoSupercategory.comp_whiskerRight (R := k)]
/-- The two rightward mates have precisely one Koszul coefficient. -/
theorem rouquierMate_comp_mate
    (h₁₂ : t₁₂ ∈ parity (R := k) _ _ p) (h₂₃ : t₂₃ ∈ parity (R := k) _ _ p) :
    rouquierMate A₁ A₂ t₁₂ ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
      E₂ ◁ rouquierMate A₂ A₃ t₂₃ =
    koszulSign p p • ((associator F₁ E₁ E₂).hom ≫
      rectangularMate A₁ A₃ (E₁ ≫ E₂) (E₂ ≫ E₃)
        ((associator E₁ E₂ E₃).hom ≫ E₁ ◁ t₂₃ ≫
          (associator E₁ E₂ E₃).inv ≫ t₁₂ ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      (associator E₂ E₃ F₃).hom) := by
  let z := (associator E₁ E₂ E₃).hom ≫ E₁ ◁ t₂₃ ≫
    (associator E₁ E₂ E₃).inv ≫ t₁₂ ▷ E₃ ≫ (associator E₁ E₂ E₃).hom
  let q := (associator F₁ (E₁ ≫ E₂) E₃).hom ≫ F₁ ◁ z ≫
    (associator F₁ E₁ (E₂ ≫ E₃)).inv ≫ A₁.counit ▷ (E₂ ≫ E₃) ≫
    (leftUnitor (E₂ ≫ E₃)).hom
  have ho := congrArg (fun f => (associator F₁ E₁ E₂).hom ≫ f)
    (rectanglePost A₁ A₃ (E₁ ≫ E₂) (E₂ ≫ E₃) z)
  have hn := (homPostAdjunction A₃).homEquiv_naturality_left
    (associator F₁ E₁ E₂).hom q
  have ho' : (associator F₁ E₁ E₂).hom ≫
      rectangularMate A₁ A₃ (E₁ ≫ E₂) (E₂ ≫ E₃) z =
    (homPostAdjunction A₃).homEquiv ((F₁ ≫ E₁) ≫ E₂) (E₂ ≫ E₃)
      ((associator F₁ E₁ E₂).hom ▷ E₃ ≫ q) :=
    ho.trans (by simpa only [q, homPost, Category.assoc] using hn.symm)
  have hi := innerExpansion A₁ A₂ h₁₂ h₂₃
  have hq := outerInput A₁ (t₁₂ := t₁₂) (t₂₃ := t₂₃)
  change (associator F₁ E₁ E₂).hom ▷ E₃ ≫ q = _ at hq
  rw [← hq] at hi
  have he := congrArg ((homPostAdjunction A₃).homEquiv
    ((F₁ ≫ E₁) ≫ E₂) (E₂ ≫ E₃)) hi
  have hs (r : ((F₁ ≫ E₁) ≫ E₂) ≫ E₃ ⟶ E₂ ≫ E₃) :
      (homPostAdjunction A₃).homEquiv ((F₁ ≫ E₁) ≫ E₂) (E₂ ≫ E₃)
        (koszulSign p p • r) = koszulSign p p •
      (homPostAdjunction A₃).homEquiv ((F₁ ≫ E₁) ≫ E₂) (E₂ ≫ E₃) r := by
    change ((rightUnitor _).inv ≫ _ ◁ A₃.unit ≫ (associator _ E₃ F₃).inv) ≫
      (koszulSign p p • r) ▷ F₃ = koszulSign p p •
      (((rightUnitor _).inv ≫ _ ◁ A₃.unit ≫ (associator _ E₃ F₃).inv) ≫ r ▷ F₃)
    rw [TwoSupercategory.zsmul_whiskerRight (R := k), Preadditive.comp_zsmul]
  have hh := (expandPost A₁ A₂ A₃ (t₁₂ := t₁₂) (t₂₃ := t₂₃)).trans
    (he.trans (hs _))
  have hf := congrArg (fun f => f ≫ (associator E₂ E₃ F₃).hom) hh
  have hout := congrArg (fun f => (koszulSign p p • f) ≫ (associator E₂ E₃ F₃).hom) ho'.symm
  simp only [homPost, Category.assoc, Iso.inv_hom_id, Category.comp_id] at hf
  simpa only [z, Preadditive.zsmul_comp, Category.assoc] using hf.trans hout
/-- The Koszul coefficients of the two expansions agree, so the mixed braid
has coefficient one, including at odd parity. -/
theorem rouquierMate_mixed_braid
    (h₁₂ : t₁₂ ∈ parity (R := k) _ _ p) (h₂₃ : t₂₃ ∈ parity (R := k) _ _ p)
    (hB : E₁ ◁ t₂₃ ≫
      ((associator E₁ E₂ E₃).inv ≫ t₁₂ ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t₁₂ ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ ≫
      ((associator E₁ E₂ E₃).inv ≫ t₁₂ ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    ((associator F₁ E₁ E₂).hom ≫ F₁ ◁ t₁₂ ≫ (associator F₁ E₁ E₂).inv) ≫
      (rouquierMate A₁ A₂ t₁₂ ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
        E₂ ◁ rouquierMate A₂ A₃ t₂₃) =
    (rouquierMate A₁ A₂ t₁₂ ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
      E₂ ◁ rouquierMate A₂ A₃ t₂₃) ≫
      (associator E₂ E₃ F₃).inv ≫ t₂₃ ▷ F₃ ≫ (associator E₂ E₃ F₃).hom := by
  let A := (associator E₁ E₂ E₃).inv ≫ t₁₂ ▷ E₃ ≫ (associator E₁ E₂ E₃).hom
  let B' := E₁ ◁ t₂₃
  let M (z : E₁ ≫ (E₂ ≫ E₃) ⟶ E₁ ≫ (E₂ ≫ E₃)) :=
    (associator F₁ E₁ E₂).hom ≫ rectangularMate A₁ A₃ (E₁ ≫ E₂) (E₂ ≫ E₃)
      ((associator E₁ E₂ E₃).hom ≫ z) ≫ (associator E₂ E₃ F₃).hom
  have hl (z : E₁ ≫ (E₂ ≫ E₃) ⟶ E₁ ≫ (E₂ ≫ E₃)) :
      ((associator F₁ E₁ E₂).hom ≫ F₁ ◁ t₁₂ ≫ (associator F₁ E₁ E₂).inv) ≫ M z =
      M (A ≫ z) := by
    simp only [M, A, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    rw [← reassoc_of% (rectangularMate_left A₁ A₃ (E₂ ≫ E₃) t₁₂
      ((associator E₁ E₂ E₃).hom ≫ z))]
  have hr (z : E₁ ≫ (E₂ ≫ E₃) ⟶ E₁ ≫ (E₂ ≫ E₃)) :
      M z ≫ (associator E₂ E₃ F₃).inv ≫ t₂₃ ▷ F₃ ≫ (associator E₂ E₃ F₃).hom =
      M (z ≫ B') := by
    simp only [M, B', Category.assoc, Iso.hom_inv_id_assoc]
    rw [← reassoc_of% (rectangularMate_right A₁ A₃ (E₁ ≫ E₂) t₂₃
      ((associator E₁ E₂ E₃).hom ≫ z))]
  have hp : rouquierMate A₁ A₂ t₁₂ ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
      E₂ ◁ rouquierMate A₂ A₃ t₂₃ = koszulSign p p • M (B' ≫ A) := by
    simpa only [M, B', A, Category.assoc] using rouquierMate_comp_mate A₁ A₂ A₃ h₁₂ h₂₃
  rw [hp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, hl, hr]
  congr 1
  apply congrArg M
  simpa only [A, B', Category.assoc] using hB.symm
end Expansion

end OddMath.SKM
