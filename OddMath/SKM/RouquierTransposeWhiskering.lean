import OddMath.SKM.RouquierCompositeAdjunction

/-!
# Composite right-transpose whiskering and associator comparison

The two whiskering laws and reversed associator in `SignedFTriangle.md`, §2,
(6) and the paragraph after (7), needed by the reflection step of Brundan,
arXiv:1501.00350v1, Theorem 4.3. Composition is in execution order, so the
right adjoints reverse order. Source and target composite adjunctions are
explicit; argument maps are unrestricted, including odd and inhomogeneous maps.
Only even counits cross arbitrary arguments. The associator calculation alone
passes through the even underlying bicategory. No left triangle or cyclicity
is assumed.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
namespace SuperAdjunction
variable {a b c : B} {E₁ E₁' : a ⟶ b} {F₁ F₁' : b ⟶ a}
  {E₂ E₂' : b ⟶ c} {F₂ F₂' : c ⟶ b}

/-- Left whiskering transposes to right whiskering by the right adjoint. -/
theorem rightTranspose_whiskerLeft
    (A₁ : SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (A₂' : SuperAdjunction (k := k) E₂' F₂') (g : E₂ ⟶ E₂') :
    rightTranspose (A₁.comp A₂) (A₁.comp A₂') (E₁ ◁ g) =
      rightTranspose A₂ A₂' g ▷ F₁ := by
  apply rightTranspose_eq
  simp only [comp_counit]
  rw [TwoSupercategory.associator_naturality_left_assoc (R := k)]
  rw [reassoc_of% (TwoSupercategory.whisker_exchange_of_even_right
    (rightTranspose A₂ A₂' g) (inv_mem _
      (TwoSupercategory.associator_hom_mem (R := k) F₁ E₁ E₂)))]
  rw [TwoSupercategory.whisker_exchange_of_even_right_assoc
    (rightTranspose A₂ A₂' g) (TwoSupercategory.whiskerRight_mem E₂ A₁.counit_mem)]
  rw [TwoSupercategory.whisker_exchange_of_even_right_assoc
    (rightTranspose A₂ A₂' g) (TwoSupercategory.leftUnitor_hom_mem (R := k) E₂)]
  rw [rightTranspose_counit, TwoSupercategory.associator_naturality_right_assoc (R := k)]
  congr 1
  have h : (associator F₁ E₁ E₂).inv ≫ A₁.counit ▷ E₂ ≫
      (leftUnitor E₂).hom ≫ g =
      F₁ ◁ E₁ ◁ g ≫ (associator F₁ E₁ E₂').inv ≫
        A₁.counit ▷ E₂' ≫ (leftUnitor E₂').hom := by
    rw [TwoSupercategory.associator_inv_naturality_right_assoc (R := k),
      ← TwoSupercategory.whisker_exchange_of_even_left_assoc A₁.counit_mem g,
      TwoSupercategory.leftUnitor_naturality (R := k)]
  simpa only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc] using
    congrArg (fun z => F₂' ◁ z ≫ A₂'.counit) h

/-- Right whiskering transposes to left whiskering, without a parity restriction. -/
theorem rightTranspose_whiskerRight
    (A₁ : SuperAdjunction (k := k) E₁ F₁)
    (A₁' : SuperAdjunction (k := k) E₁' F₁')
    (A₂ : SuperAdjunction (k := k) E₂ F₂) (f : E₁ ⟶ E₁') :
    rightTranspose (A₁.comp A₂) (A₁'.comp A₂) (f ▷ E₂) =
      F₂ ◁ rightTranspose A₁ A₁' f := by
  apply rightTranspose_eq
  simp only [comp_counit]
  rw [TwoSupercategory.associator_naturality_middle_assoc (R := k),
    TwoSupercategory.associator_naturality_right_assoc (R := k)]
  congr 1
  have h : rightTranspose A₁ A₁' f ▷ (E₁ ≫ E₂) ≫
      (associator F₁ E₁ E₂).inv ≫ A₁.counit ▷ E₂ ≫ (leftUnitor E₂).hom =
      F₁' ◁ (f ▷ E₂) ≫ (associator F₁' E₁' E₂).inv ≫
        A₁'.counit ▷ E₂ ≫ (leftUnitor E₂).hom := by
    rw [TwoSupercategory.associator_inv_naturality_left_assoc (R := k),
      TwoSupercategory.associator_inv_naturality_middle_assoc (R := k),
      ← reassoc_of% (TwoSupercategory.comp_whiskerRight (R := k)
        (rightTranspose A₁ A₁' f ▷ E₁) A₁.counit E₂), rightTranspose_counit,
      TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]
  simpa only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc] using
    congrArg (fun z => F₂ ◁ z ≫ A₂.counit) h

private theorem associatorCap {C : Type u} [Bicategory.{w,v} C]
    {a b c d : C} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b} {E₃ : c ⟶ d} {F₃ : d ⟶ c}
    (A₁ : Bicategory.Adjunction E₁ F₁) (A₂ : Bicategory.Adjunction E₂ F₂)
    (A₃ : Bicategory.Adjunction E₃ F₃) :
    Bicategory.whiskerRight (Bicategory.associator F₃ F₂ F₁).inv (E₁ ≫ (E₂ ≫ E₃)) ≫
      (A₁.comp (A₂.comp A₃)).counit =
    Bicategory.whiskerLeft (F₃ ≫ (F₂ ≫ F₁)) (Bicategory.associator E₁ E₂ E₃).inv ≫
      ((A₁.comp A₂).comp A₃).counit := by
  dsimp [Bicategory.Adjunction.comp, Bicategory.Adjunction.compCounit]
  bicategory

/-- Reversal of the bracketed adjoint string transposes the inverse associator. -/
theorem rightTranspose_associator_inv {d : B} {E₃ : c ⟶ d} {F₃ : d ⟶ c}
    (A₁ : SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (A₃ : SuperAdjunction (k := k) E₃ F₃) :
    rightTranspose (A₁.comp (A₂.comp A₃)) ((A₁.comp A₂).comp A₃)
      (associator E₁ E₂ E₃).inv = (associator F₃ F₂ F₁).inv := by
  apply rightTranspose_eq
  exact congrArg Subtype.val (associatorCap A₁.toUnderlying A₂.toUnderlying A₃.toUnderlying)

end SuperAdjunction
end OddMath.SKM
