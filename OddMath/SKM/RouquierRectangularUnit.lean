import OddMath.SKM.RouquierRectangularComposition

/-!
# The rectangular unit pitchfork

Brundan–Ellis (1.11) and the right-adjunction triangle: inserting the
lower unit before the prescribed sideways crossing equals inserting the
upper unit before the inherited upward crossing. This is the unit-side
input to the finite-column cap tests in Lemma 7.1.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : c ⟶ d} {F₂ : d ⟶ c}

/-- The prescribed rectangular right mate contracts against its lower
unit. The crossing can be odd; both bending maps are even. -/
theorem crossMate_pitchfork_unit
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (g : a ⟶ c) (h : b ⟶ d) (t : g ≫ E₂ ⟶ E₁ ≫ h) :
    (leftUnitor g).inv ≫ A₁.unit ▷ g ≫ (associator E₁ F₁ g).hom ≫
      E₁ ◁ crossMate A₁ A₂ t =
    (rightUnitor g).inv ≫ g ◁ A₂.unit ≫ (associator g E₂ F₂).inv ≫
      t ▷ F₂ ≫ (associator E₁ h F₂).hom := by
  have he := congrArg ((homPreAdjunction A₁).homEquiv g (h ≫ F₂))
    (crossMate_eq_rectangularMate A₁ A₂ g h t)
  have hr : rectangularMate A₁ A₂ g h t =
      ((homPreAdjunction A₁).homEquiv g (h ≫ F₂)).symm
        (((homPostAdjunction A₂).homEquiv g (E₁ ≫ h)) t ≫
          (associator E₁ h F₂).hom) := by
    simp [rectangularMate, Iso.homCongr]
    rfl
  rw [hr, Equiv.apply_symm_apply] at he
  simpa [CategoryTheory.Adjunction.homEquiv, homPreAdjunction, homPreUnit,
    homPreId, homPreComp, homPreTransform, homPostAdjunction, homPostUnit,
    homPostId, homPostComp, homPostTransform, SuperNatTrans.toNatTrans,
    homPre, homPost, Category.assoc] using he

end OddMath.SKM
