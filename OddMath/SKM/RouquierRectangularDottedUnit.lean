import OddMath.SKM.RouquierRectangularUnit

/-!
# The dotted rectangular unit pitchfork

The two signs in Brundan–Ellis, Lemma 7.1's finite-column reduction cancel:
one from exchanging the dot and sideways mate, one from the upward dot
slide. This retains the actual inherited crossing and its prescribed mate.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : c ⟶ d} {F₂ : d ⟶ c}

/-- A homogeneous dot slide cancels the interchange sign in the dotted
unit pitchfork. The slide hypothesis is the ordinary distinct relation,
not a new cap compatibility condition. -/
theorem crossMate_pitchfork_unit_dotted
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (g : a ⟶ c) (h : b ⟶ d) (t : g ≫ E₂ ⟶ E₁ ≫ h)
    (x₁ : E₁ ⟶ E₁) (x₂ : E₂ ⟶ E₂) {p q : ZMod 2}
    (hx : x₁ ∈ parity (R := k) _ _ p) (ht : t ∈ parity (R := k) _ _ q)
    (hslide : g ◁ x₂ ≫ t = koszulSign p q • (t ≫ x₁ ▷ h)) :
    (leftUnitor g).inv ≫ (A₁.unit ≫ x₁ ▷ F₁) ▷ g ≫
      (associator E₁ F₁ g).hom ≫ E₁ ◁ crossMate A₁ A₂ t =
    (rightUnitor g).inv ≫ g ◁ (A₂.unit ≫ x₂ ▷ F₂) ≫
      (associator g E₂ F₂).inv ≫ t ▷ F₂ ≫ (associator E₁ h F₂).hom := by
  have hslide' : t ≫ x₁ ▷ h = koszulSign p q • (g ◁ x₂ ≫ t) := by
    rw [hslide, koszulSign_smul_smul]
  have hn₁ := TwoSupercategory.associator_naturality_left (R := k) x₁ F₁ g
  have hn₂ := TwoSupercategory.associator_naturality_left (R := k) x₁ h F₂
  have he := TwoSupercategory.super_interchange hx (crossMate_mem A₁ A₂ g h t ht)
  have hu := crossMate_pitchfork_unit A₁ A₂ g h t
  simp only [TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]
  rw [reassoc_of% hn₁, he]
  simp only [Preadditive.comp_zsmul]
  rw [reassoc_of% hu, ← hn₂]
  rw [← reassoc_of% (TwoSupercategory.comp_whiskerRight (R := k) t (x₁ ▷ h) F₂), hslide']
  simp only [TwoSupercategory.zsmul_whiskerRight (R := k), Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, koszulSign_smul_smul]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]
  rw [TwoSupercategory.whisker_assoc (R := k)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end OddMath.SKM
