import OddMath.SKM.RouquierMulticolour
import OddMath.SKM.RouquierMixedMate

/-!
# Rectangular composition of right mates

The mate calculation used in Brundan–Ellis, Lemma 3.3 (3.8), with
independent weight corners and crossing parities. Its downstream use is
the distinct cap-pitchfork test in Lemma 7.1. All bends use the given
even right adjunctions.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

private theorem rectangularPrefix {C : Type u} [Bicategory.{w,v} C]
    {a b c d : C} (F : b ⟶ a) (G : a ⟶ c) (E : c ⟶ d) (K : d ⟶ c)
    (η : 𝟙 c ⟶ E ≫ K) :
    (Bicategory.rightUnitor (F ≫ G)).inv ≫ Bicategory.whiskerLeft (F ≫ G) η ≫
      (Bicategory.associator F G (E ≫ K)).hom ≫
      Bicategory.whiskerLeft F (Bicategory.associator G E K).inv =
    Bicategory.whiskerLeft F ((Bicategory.rightUnitor G).inv ≫
      Bicategory.whiskerLeft G η ≫ (Bicategory.associator G E K).inv) := by bicategory

private theorem rectangularSuffix {C : Type u} [Bicategory.{w,v} C]
    {a b c d : C} (E : a ⟶ b) (F : b ⟶ a) (H : b ⟶ d) (K : d ⟶ c)
    (ε : F ≫ E ⟶ 𝟙 b) :
    (Bicategory.associator F (E ≫ H) K).inv ≫
      Bicategory.whiskerRight (Bicategory.associator F E H).inv K ≫
      Bicategory.whiskerRight (Bicategory.whiskerRight ε H) K ≫
      Bicategory.whiskerRight (Bicategory.leftUnitor H).hom K =
    Bicategory.whiskerLeft F (Bicategory.associator E H K).hom ≫
      (Bicategory.associator F E (H ≫ K)).inv ≫
      Bicategory.whiskerRight ε (H ≫ K) ≫ (Bicategory.leftUnitor (H ≫ K)).hom := by bicategory

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

section Rectangular
variable {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
  {E₂ : c ⟶ d} {F₂ : d ⟶ c}
  (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
  (g : a ⟶ c) (h : b ⟶ d) (t : g ≫ E₂ ⟶ E₁ ≫ h)

/-- The ordered presentation mate is the rectangular Hom equivalence,
with no identification of the four weight corners. -/
theorem crossMate_eq_rectangularMate :
    crossMate A₁ A₂ t = rectangularMate A₁ A₂ g h t := by
  have hp := congrArg Subtype.val (rectangularPrefix
    (Underlying2.hom1 (R := k) F₁) (Underlying2.hom1 (R := k) g)
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂)
    ⟨A₂.unit, A₂.unit_mem⟩)
  have hs := congrArg Subtype.val (rectangularSuffix
    (Underlying2.hom1 (R := k) E₁) (Underlying2.hom1 (R := k) F₁)
    (Underlying2.hom1 (R := k) h) (Underlying2.hom1 (R := k) F₂)
    ⟨A₁.counit, A₁.counit_mem⟩)
  change (rightUnitor (F₁ ≫ g)).inv ≫ (F₁ ≫ g) ◁ A₂.unit ≫
    (associator F₁ g (E₂ ≫ F₂)).hom ≫ F₁ ◁ (associator g E₂ F₂).inv =
    F₁ ◁ ((rightUnitor g).inv ≫ g ◁ A₂.unit ≫ (associator g E₂ F₂).inv) at hp
  change (associator F₁ (E₁ ≫ h) F₂).inv ≫
    (associator F₁ E₁ h).inv ▷ F₂ ≫ (A₁.counit ▷ h) ▷ F₂ ≫ (leftUnitor h).hom ▷ F₂ =
    F₁ ◁ (associator E₁ h F₂).hom ≫ (associator F₁ E₁ (h ≫ F₂)).inv ≫
      A₁.counit ▷ (h ≫ F₂) ≫ (leftUnitor (h ≫ F₂)).hom at hs
  rw [rectangularMate_eq]
  unfold crossMate
  rw [hs]
  simp only [← Category.assoc] at hp ⊢
  rw [hp]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]

/-- Capping the rectangular right mate contracts the upper right adjunction. -/
theorem crossMate_pitchfork_cap :
    crossMate A₁ A₂ t ▷ E₂ ≫ (associator h F₂ E₂).hom ≫
      h ◁ A₂.counit ≫ (rightUnitor h).hom =
    (associator F₁ g E₂).hom ≫ F₁ ◁ t ≫ (associator F₁ E₁ h).inv ≫
      A₁.counit ▷ h ≫ (leftUnitor h).hom := by
  have he := congrArg ((homPostAdjunction A₂).homEquiv (F₁ ≫ g) h).symm
    (rectangularMate_postTranspose A₁ A₂ g h t)
  rw [Equiv.symm_apply_apply] at he
  rw [crossMate_eq_rectangularMate A₁ A₂ g h t]
  simpa [CategoryTheory.Adjunction.homEquiv, homPostAdjunction, homPostCounit,
    homPostComp, homPostTransform, homPostId, SuperNatTrans.toNatTrans, homPost,
    Category.assoc] using he

/-- Right bending retains the degree of the crossing. -/
theorem crossMate_mem {p : ZMod 2} (ht : t ∈ parity (R := k) _ _ p) :
    crossMate A₁ A₂ t ∈ parity (R := k) _ _ p := by
  rw [crossMate_eq_rectangularMate A₁ A₂ g h t,
    rectangularMate_postTranspose A₁ A₂ g h t]
  have hm := comp_mem (homPostUnit_mem A₂ (F₁ ≫ g))
    (TwoSupercategory.whiskerRight_mem F₂
      (comp_mem (TwoSupercategory.associator_hom_mem (R := k) F₁ g E₂)
        (comp_mem (TwoSupercategory.whiskerLeft_mem F₁ ht)
          (comp_mem (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) F₁ E₁ h))
            (comp_mem (TwoSupercategory.whiskerRight_mem h A₁.counit_mem)
              (TwoSupercategory.leftUnitor_hom_mem (R := k) h))))))
  simpa [CategoryTheory.Adjunction.homEquiv, homPostAdjunction, homPost,
    Category.assoc] using hm
end Rectangular

/-- The rectangular mate is linear, so the correction polynomial in the
upward mixed braid is carried term by term to its bent counterpart. -/
def rectangularMateLinearMap {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : c ⟶ d} {F₂ : d ⟶ c}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (g : a ⟶ c) (h : b ⟶ d) :
    (g ≫ E₂ ⟶ E₁ ≫ h) →ₗ[k] (F₁ ≫ g ⟶ h ≫ F₂) where
  toFun := rectangularMate A₁ A₂ g h
  map_add' x y := by
    simp only [rectangularMate_eq, TwoSupercategory.add_whiskerRight (R := k),
      Preadditive.comp_add, Preadditive.add_comp, TwoSupercategory.whiskerLeft_add (R := k)]
  map_smul' z x := by
    simp only [rectangularMate_eq, TwoSupercategory.smul_whiskerRight (R := k),
      Linear.comp_smul, Linear.smul_comp, TwoSupercategory.whiskerLeft_smul (R := k),
      RingHom.id_apply]

private theorem rectangularOuterCup {C : Type u} [Bicategory.{w,v} C]
    {a b c d : C} (L : a ⟶ b) (G : b ⟶ c) (E : c ⟶ d) (F : d ⟶ c)
    (η : 𝟙 c ⟶ E ≫ F) :
    Bicategory.whiskerLeft L ((Bicategory.rightUnitor G).inv ≫
      Bicategory.whiskerLeft G η ≫ (Bicategory.associator G E F).inv) =
    (Bicategory.rightUnitor (L ≫ G)).inv ≫ Bicategory.whiskerLeft (L ≫ G) η ≫
      (Bicategory.associator (L ≫ G) E F).inv ≫
      Bicategory.whiskerRight (Bicategory.associator L G E).hom F ≫
      (Bicategory.associator L (G ≫ E) F).hom := by bicategory

private theorem rectangularPostLeft {a b c d : B} (L : a ⟶ b) (G : b ⟶ c)
    {E : c ⟶ d} {F : d ⟶ c} (A : SuperAdjunction (k := k) E F)
    (H : b ⟶ d) (z : G ≫ E ⟶ H) :
    L ◁ ((homPostAdjunction A).homEquiv G H z) ≫ (associator L H F).inv =
    (homPostAdjunction A).homEquiv (L ≫ G) (L ≫ H)
      ((associator L G E).hom ≫ L ◁ z) := by
  have hp := congrArg Subtype.val (rectangularOuterCup
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

private theorem rectangularCapSuffix {C : Type u} [Bicategory.{w,v} C]
    {a b c d : C} (L : d ⟶ b) (E : a ⟶ b) (F : b ⟶ a) (G : b ⟶ c)
    (ε : F ≫ E ⟶ 𝟙 b) :
    (Bicategory.associator L F (E ≫ G)).hom ≫
      Bicategory.whiskerLeft L (Bicategory.associator F E G).inv ≫
      Bicategory.whiskerLeft L (Bicategory.whiskerRight ε G) ≫
      Bicategory.whiskerLeft L (Bicategory.leftUnitor G).hom =
    (Bicategory.associator (L ≫ F) E G).inv ≫
      Bicategory.whiskerRight ((Bicategory.associator L F E).hom ≫
        Bicategory.whiskerLeft L ε ≫ (Bicategory.rightUnitor L).hom) G := by bicategory

private theorem rectangularOuterCap {C : Type u} [Bicategory.{w,v} C]
    {a b c d : C} (F : b ⟶ a) (E : a ⟶ b) (H : b ⟶ d) (K : d ⟶ c)
    (ε : F ≫ E ⟶ 𝟙 b) :
    Bicategory.whiskerLeft F (Bicategory.associator E H K).hom ≫
      (Bicategory.associator F E (H ≫ K)).inv ≫
      Bicategory.whiskerRight ε (H ≫ K) ≫ (Bicategory.leftUnitor (H ≫ K)).hom =
    (Bicategory.associator F (E ≫ H) K).inv ≫
      Bicategory.whiskerRight ((Bicategory.associator F E H).inv ≫
        Bicategory.whiskerRight ε H ≫ (Bicategory.leftUnitor H).hom) K := by bicategory

section Composition
variable {a b c d e f : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
  {E₂ : c ⟶ d} {F₂ : d ⟶ c} {E₃ : e ⟶ f} {F₃ : f ⟶ e}
  (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
  (A₃ : SuperAdjunction (k := k) E₃ F₃)
  {G₁₂ : a ⟶ c} {H₁₂ : b ⟶ d} {G₂₃ : c ⟶ e} {H₂₃ : d ⟶ f}
  {p q : ZMod 2} {t₁₂ : G₁₂ ≫ E₂ ⟶ E₁ ≫ H₁₂} {t₂₃ : G₂₃ ≫ E₃ ⟶ E₂ ≫ H₂₃}

private theorem rectangularExpandPost :
    crossMate A₁ A₂ t₁₂ ▷ G₂₃ ≫ (associator H₁₂ F₂ G₂₃).hom ≫
      H₁₂ ◁ crossMate A₂ A₃ t₂₃ ≫ (associator H₁₂ H₂₃ F₃).inv =
    (homPostAdjunction A₃).homEquiv ((F₁ ≫ G₁₂) ≫ G₂₃) (H₁₂ ≫ H₂₃)
      (((crossMate A₁ A₂ t₁₂ ▷ G₂₃) ≫ (associator H₁₂ F₂ G₂₃).hom) ▷ E₃ ≫
        (associator H₁₂ (F₂ ≫ G₂₃) E₃).hom ≫
        H₁₂ ◁ ((associator F₂ G₂₃ E₃).hom ≫ F₂ ◁ t₂₃ ≫
          (associator F₂ E₂ H₂₃).inv ≫ A₂.counit ▷ H₂₃ ≫ (leftUnitor H₂₃).hom)) := by
  have hl := rectangularPostLeft H₁₂ (F₂ ≫ G₂₃) A₃ H₂₃
    ((associator F₂ G₂₃ E₃).hom ≫ F₂ ◁ t₂₃ ≫
      (associator F₂ E₂ H₂₃).inv ≫ A₂.counit ▷ H₂₃ ≫ (leftUnitor H₂₃).hom)
  have hn := (homPostAdjunction A₃).homEquiv_naturality_left
    ((crossMate A₁ A₂ t₁₂ ▷ G₂₃) ≫ (associator H₁₂ F₂ G₂₃).hom)
    ((associator H₁₂ (F₂ ≫ G₂₃) E₃).hom ≫
      H₁₂ ◁ ((associator F₂ G₂₃ E₃).hom ≫ F₂ ◁ t₂₃ ≫
        (associator F₂ E₂ H₂₃).inv ≫ A₂.counit ▷ H₂₃ ≫ (leftUnitor H₂₃).hom))
  have hm := congrArg (fun z => crossMate A₁ A₂ t₁₂ ▷ G₂₃ ≫
    (associator H₁₂ F₂ G₂₃).hom ≫ z) hl
  have he := congrArg (fun z => crossMate A₁ A₂ t₁₂ ▷ G₂₃ ≫
    (associator H₁₂ F₂ G₂₃).hom ≫ H₁₂ ◁ z ≫ (associator H₁₂ H₂₃ F₃).inv)
    ((crossMate_eq_rectangularMate A₂ A₃ G₂₃ H₂₃ t₂₃).trans
      (rectangularMate_postTranspose A₂ A₃ G₂₃ H₂₃ t₂₃))
  exact he.trans (hm.trans (by simpa only [homPost, Category.assoc] using hn.symm))

private theorem rectangularInnerExpansion
    (h₁₂ : t₁₂ ∈ parity (R := k) _ _ p) (h₂₃ : t₂₃ ∈ parity (R := k) _ _ q) :
    (((crossMate A₁ A₂ t₁₂ ▷ G₂₃) ≫ (associator H₁₂ F₂ G₂₃).hom) ▷ E₃ ≫
      (associator H₁₂ (F₂ ≫ G₂₃) E₃).hom ≫
      H₁₂ ◁ ((associator F₂ G₂₃ E₃).hom ≫ F₂ ◁ t₂₃ ≫
        (associator F₂ E₂ H₂₃).inv ≫ A₂.counit ▷ H₂₃ ≫ (leftUnitor H₂₃).hom)) =
    koszulSign p q • ((associator (F₁ ≫ G₁₂) G₂₃ E₃).hom ≫
      (F₁ ≫ G₁₂) ◁ t₂₃ ≫ (associator (F₁ ≫ G₁₂) E₂ H₂₃).inv ≫
      ((associator F₁ G₁₂ E₂).hom ≫ F₁ ◁ t₁₂ ≫ (associator F₁ E₁ H₁₂).inv ≫
        A₁.counit ▷ H₁₂ ≫ (leftUnitor H₁₂).hom) ▷ H₂₃) := by
  have hs := congrArg Subtype.val (rectangularCapSuffix
    (Underlying2.hom1 (R := k) H₁₂) (Underlying2.hom1 (R := k) E₂)
    (Underlying2.hom1 (R := k) F₂) (Underlying2.hom1 (R := k) H₂₃)
    ⟨A₂.counit, A₂.counit_mem⟩)
  change (associator H₁₂ F₂ (E₂ ≫ H₂₃)).hom ≫
    H₁₂ ◁ (associator F₂ E₂ H₂₃).inv ≫ H₁₂ ◁ (A₂.counit ▷ H₂₃) ≫
    H₁₂ ◁ (leftUnitor H₂₃).hom =
    (associator (H₁₂ ≫ F₂) E₂ H₂₃).inv ≫
      ((associator H₁₂ F₂ E₂).hom ≫ H₁₂ ◁ A₂.counit ≫ (rightUnitor H₁₂).hom) ▷ H₂₃ at hs
  have hp := TwoSupercategory.pentagon (R := k) H₁₂ F₂ G₂₃ E₃
  have hn := TwoSupercategory.associator_naturality_left (R := k)
    (crossMate A₁ A₂ t₁₂) G₂₃ E₃
  simp only [TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [reassoc_of% hp]
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k)]
  rw [hs, reassoc_of% hn]
  rw [reassoc_of% (TwoSupercategory.super_interchange
    (crossMate_mem A₁ A₂ G₁₂ H₁₂ t₁₂ h₁₂) h₂₃)]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  congr 1
  rw [TwoSupercategory.whiskerRight_comp (R := k)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← TwoSupercategory.comp_whiskerRight (R := k)]
  rw [crossMate_pitchfork_cap]
  simp only [TwoSupercategory.comp_whiskerRight (R := k)]

private theorem rectangularOuterInput :
    (associator F₁ G₁₂ G₂₃).hom ▷ E₃ ≫ (associator F₁ (G₁₂ ≫ G₂₃) E₃).hom ≫
      F₁ ◁ ((associator G₁₂ G₂₃ E₃).hom ≫ G₁₂ ◁ t₂₃ ≫
        (associator G₁₂ E₂ H₂₃).inv ≫ t₁₂ ▷ H₂₃ ≫ (associator E₁ H₁₂ H₂₃).hom) ≫
      (associator F₁ E₁ (H₁₂ ≫ H₂₃)).inv ≫ A₁.counit ▷ (H₁₂ ≫ H₂₃) ≫
      (leftUnitor (H₁₂ ≫ H₂₃)).hom =
    (associator (F₁ ≫ G₁₂) G₂₃ E₃).hom ≫ (F₁ ≫ G₁₂) ◁ t₂₃ ≫
      (associator (F₁ ≫ G₁₂) E₂ H₂₃).inv ≫
      ((associator F₁ G₁₂ E₂).hom ≫ F₁ ◁ t₁₂ ≫ (associator F₁ E₁ H₁₂).inv ≫
        A₁.counit ▷ H₁₂ ≫ (leftUnitor H₁₂).hom) ▷ H₂₃ := by
  have hs := congrArg Subtype.val (rectangularOuterCap
    (Underlying2.hom1 (R := k) F₁) (Underlying2.hom1 (R := k) E₁)
    (Underlying2.hom1 (R := k) H₁₂) (Underlying2.hom1 (R := k) H₂₃)
    ⟨A₁.counit, A₁.counit_mem⟩)
  change F₁ ◁ (associator E₁ H₁₂ H₂₃).hom ≫
    (associator F₁ E₁ (H₁₂ ≫ H₂₃)).inv ≫ A₁.counit ▷ (H₁₂ ≫ H₂₃) ≫
    (leftUnitor (H₁₂ ≫ H₂₃)).hom =
    (associator F₁ (E₁ ≫ H₁₂) H₂₃).inv ≫
      ((associator F₁ E₁ H₁₂).inv ≫ A₁.counit ▷ H₁₂ ≫ (leftUnitor H₁₂).hom) ▷ H₂₃ at hs
  have hp := TwoSupercategory.pentagon (R := k) F₁ G₁₂ G₂₃ E₃
  have hq := TwoSupercategory.pentagon (R := k) F₁ G₁₂ E₂ H₂₃
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [hs, reassoc_of% hp]
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k)]
  rw [TwoSupercategory.associator_inv_naturality_middle_assoc (R := k)]
  have hc := congrArg (fun z => (associator (F₁ ≫ G₁₂) E₂ H₂₃).inv ≫ z ≫
    F₁ ◁ (associator G₁₂ E₂ H₂₃).inv ≫ (associator F₁ (G₁₂ ≫ E₂) H₂₃).inv) hq
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    TwoSupercategory.whiskerLeft_hom_inv_assoc (R := k), Iso.hom_inv_id,
    Category.comp_id] at hc
  rw [← reassoc_of% hc]
  simp only [TwoSupercategory.comp_whiskerRight (R := k)]

/-- Pasting two right mates has one Koszul coefficient, with independent
rectangular weight corners and independent crossing parities. This is
the two-mate expansion needed to bend the corrected multicolour braid. -/
theorem crossMate_comp_crossMate
    (h₁₂ : t₁₂ ∈ parity (R := k) _ _ p) (h₂₃ : t₂₃ ∈ parity (R := k) _ _ q) :
    crossMate A₁ A₂ t₁₂ ▷ G₂₃ ≫ (associator H₁₂ F₂ G₂₃).hom ≫
      H₁₂ ◁ crossMate A₂ A₃ t₂₃ =
    koszulSign p q • ((associator F₁ G₁₂ G₂₃).hom ≫
      rectangularMate A₁ A₃ (G₁₂ ≫ G₂₃) (H₁₂ ≫ H₂₃)
        ((associator G₁₂ G₂₃ E₃).hom ≫ G₁₂ ◁ t₂₃ ≫
          (associator G₁₂ E₂ H₂₃).inv ≫ t₁₂ ▷ H₂₃ ≫ (associator E₁ H₁₂ H₂₃).hom) ≫
      (associator H₁₂ H₂₃ F₃).hom) := by
  let z := (associator G₁₂ G₂₃ E₃).hom ≫ G₁₂ ◁ t₂₃ ≫
    (associator G₁₂ E₂ H₂₃).inv ≫ t₁₂ ▷ H₂₃ ≫ (associator E₁ H₁₂ H₂₃).hom
  let v := (associator F₁ (G₁₂ ≫ G₂₃) E₃).hom ≫ F₁ ◁ z ≫
    (associator F₁ E₁ (H₁₂ ≫ H₂₃)).inv ≫ A₁.counit ▷ (H₁₂ ≫ H₂₃) ≫
    (leftUnitor (H₁₂ ≫ H₂₃)).hom
  have ho := congrArg (fun f => (associator F₁ G₁₂ G₂₃).hom ≫ f)
    (rectangularMate_postTranspose A₁ A₃ (G₁₂ ≫ G₂₃) (H₁₂ ≫ H₂₃) z)
  have hn := (homPostAdjunction A₃).homEquiv_naturality_left
    (associator F₁ G₁₂ G₂₃).hom v
  have ho' : (associator F₁ G₁₂ G₂₃).hom ≫
      rectangularMate A₁ A₃ (G₁₂ ≫ G₂₃) (H₁₂ ≫ H₂₃) z =
    (homPostAdjunction A₃).homEquiv ((F₁ ≫ G₁₂) ≫ G₂₃) (H₁₂ ≫ H₂₃)
      ((associator F₁ G₁₂ G₂₃).hom ▷ E₃ ≫ v) :=
    ho.trans (by simpa only [v, homPost, Category.assoc] using hn.symm)
  have hi := rectangularInnerExpansion A₁ A₂ h₁₂ h₂₃
  have hv := rectangularOuterInput A₁ (t₁₂ := t₁₂) (t₂₃ := t₂₃)
  change (associator F₁ G₁₂ G₂₃).hom ▷ E₃ ≫ v = _ at hv
  rw [← hv] at hi
  have he := congrArg ((homPostAdjunction A₃).homEquiv
    ((F₁ ≫ G₁₂) ≫ G₂₃) (H₁₂ ≫ H₂₃)) hi
  have hs (r : ((F₁ ≫ G₁₂) ≫ G₂₃) ≫ E₃ ⟶ H₁₂ ≫ H₂₃) :
      (homPostAdjunction A₃).homEquiv ((F₁ ≫ G₁₂) ≫ G₂₃) (H₁₂ ≫ H₂₃)
        (koszulSign p q • r) = koszulSign p q •
      (homPostAdjunction A₃).homEquiv ((F₁ ≫ G₁₂) ≫ G₂₃) (H₁₂ ≫ H₂₃) r := by
    change ((rightUnitor _).inv ≫ _ ◁ A₃.unit ≫ (associator _ E₃ F₃).inv) ≫
      (koszulSign p q • r) ▷ F₃ = koszulSign p q •
      (((rightUnitor _).inv ≫ _ ◁ A₃.unit ≫ (associator _ E₃ F₃).inv) ≫ r ▷ F₃)
    rw [TwoSupercategory.zsmul_whiskerRight (R := k), Preadditive.comp_zsmul]
  have hh := (rectangularExpandPost A₁ A₂ A₃ (t₁₂ := t₁₂) (t₂₃ := t₂₃)).trans
    (he.trans (hs _))
  have hf := congrArg (fun f => f ≫ (associator H₁₂ H₂₃ F₃).hom) hh
  have hout := congrArg (fun f => (koszulSign p q • f) ≫ (associator H₁₂ H₂₃ F₃).hom) ho'.symm
  simp only [homPost, Category.assoc, Iso.inv_hom_id, Category.comp_id] at hf
  simpa only [z, Preadditive.zsmul_comp, Category.assoc] using hf.trans hout

end Composition
end OddMath.SKM
