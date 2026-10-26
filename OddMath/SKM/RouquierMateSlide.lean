import OddMath.SKM.RouquierMateProjection

/-!
# Normalized and projected mate dot slides

This ports the dot-slide step preceding `rouqSig_eq` in
`Categorification/TwoRep/RouqCoproduct.lean`. Its downstream consumer is the
finite ordered series in `SuperRouquierLoc.MateProjectionFormula`.
The normalization is derived from the cup–crossing–cap mate, not from a
chosen off-diagonal matrix. Sector dot intertwining remains an explicit
hypothesis until the content-shifted Hom comparisons are constructed.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- Normalize the raw mate so that `σ x - q y σ = u v` in conventional
right-to-left notation. No inverse or projected recurrence is assumed. -/
theorem rouquierMate_normalized_slide {a b c : B}
    {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (x₁ : E₁ ⟶ E₁) (x₂ : E₂ ⟶ E₂) (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (p : ZMod 2)
    (hslide : t ≫ E₁ ◁ x₂ - koszulSign p p • (x₁ ▷ E₂ ≫ t) = 𝟙 (E₁ ≫ E₂)) :
    (F₁ ◁ x₁) ≫ (-(koszulSign p p) • rouquierMate A₁ A₂ t) -
      koszulSign p p • ((-(koszulSign p p) • rouquierMate A₁ A₂ t) ≫ x₂ ▷ F₂) =
        A₁.counit ≫ A₂.unit := by
  have h : rouquierMate A₁ A₂ t ≫ x₂ ▷ F₂ -
      koszulSign p p • (F₁ ◁ x₁ ≫ rouquierMate A₁ A₂ t) = A₁.counit ≫ A₂.unit := by
    simpa only [Int.cast_smul_eq_zsmul] using
      rouquierMate_slide A₁ A₂ x₁ x₂ t ((koszulSign p p : ℤ) : k)
        (by simpa only [Int.cast_smul_eq_zsmul] using hslide)
  simpa only [neg_smul, Preadditive.comp_neg, Preadditive.neg_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, smul_neg,
    koszulSign_smul_smul, sub_neg_eq_add, sub_eq_add_neg, neg_neg, add_comm] using h

section Projection
variable {C : Type*} [Category C] [Preadditive C] {S T X Y : C}

/-- Project an ordered dot slide along specified intertwining sector maps.
No cyclic reordering of a cap and cup is used. -/
theorem mate_slide_projection (f b : S ⟶ T) (x : End S) (y : End T)
    (q : ℤ) (h : x ≫ f - q • (f ≫ y) = b)
    (inc : X ⟶ S) (proj : T ⟶ Y) (x' : End X) (y' : End Y)
    (hx : inc ≫ x = x' ≫ inc) (hy : y ≫ proj = proj ≫ y') :
    x' ≫ (inc ≫ f ≫ proj) - q • ((inc ≫ f ≫ proj) ≫ y') = inc ≫ b ≫ proj := by
  have h' := congrArg (fun z => inc ≫ z ≫ proj) h
  simpa only [Preadditive.sub_comp, Preadditive.comp_sub,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    ← Category.assoc inc x, hx, Category.assoc, hy] using h'
end Projection
end OddMath.SKM
