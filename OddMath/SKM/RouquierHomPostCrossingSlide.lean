/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierHomPostPowers

/-!
# The dot slide of the content-shifted postcomposition crossing

The reservoir/reservoir diagonal entry of the upward crossing of the swapped action
(`docs/Nondegeneracy/SwappedActionAssembly.md`, §2) is the content-shifted postcomposition
crossing `homContentPostCrossing`, and its dots are the shifted postcomposition dots
`homContentPostDot`. This file proves the upward slide relation of Brundan–Ellis, *Super
Kac–Moody 2-categories*, arXiv:1701.04133v2, (1.8), for these entries:

  `c ≫ x_outer - q • (x_inner ≫ c) = 1`, `q = (-1)^{p_i}`,

with `x_outer` the dot on the outer letter (applied last) and `x_inner` the dot on the inner
letter (`homContentPostCrossing_slide_app`). This is the orientation of the pre/pre entry
(`homContentCrossing_slide`). The relation is deduced from the factor's slide
`SuperRouquierLoc.slide_right` by the word comparison `homContentPostWordIso`; the two parity
shifts of the comparison contribute cancelling signs (`homShiftConjugationIso_naturality`).
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Shift
variable {k : Type r} [CommRing k]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [PiSupercategory k C]
  {C' : Type u} [Category.{v} C'] [Preadditive C'] [Linear k C'] [Supercategory k C']
  [PiSupercategory k C']

/-- The beta/xi removal of the two shifts around a superfunctor is natural in its argument,
for homogeneous maps of either parity: the two signs cancel. -/
theorem homShiftConjugationIso_naturality (F : C ⥤ C') [F.Additive] [F.Linear k]
    [IsSuperfunctor k F] (p : ZMod 2) {Z Z' : C} {s : ZMod 2} {f : Z ⟶ Z'}
    (hf : f ∈ parity (R := k) Z Z' s) :
    (homParityShift (k := k) p).map (F.map ((homParityShift (k := k) p).map f)) ≫
        (homShiftConjugationIso F p Z').hom =
      (homShiftConjugationIso F p Z).hom ≫ F.map f := by
  rw [homShiftConjugationIso_hom, homShiftConjugationIso_hom, ← Functor.map_comp_assoc,
    ← F.map_comp, (homParityShiftDatum (k := k) p).hom_naturality hf, F.map_smul,
    F.map_comp, Functor.map_smul, Linear.smul_comp, Functor.map_comp, Category.assoc,
    (homParityShiftDatum (k := k) p).hom_naturality (IsSuperfunctor.map_mem (R := k) hf),
    Linear.comp_smul, smul_smul, sign_mul_self, one_smul, Category.assoc]

end Shift

namespace SlideConj
variable {C : Type*} [Category C] [Preadditive C]

/-- A slide identity is transported along an isomorphism that intertwines the dots. -/
theorem conj_slide {A B' : C} (φ : A ≅ B') (c g₁ g₂ : B' ⟶ B') (d₁ d₂ : A ⟶ A) (q : ℤ)
    (h₂ : d₂ ≫ φ.hom = φ.hom ≫ g₂) (h₁ : d₁ ≫ φ.hom = φ.hom ≫ g₁)
    (hs : c ≫ g₂ - q • (g₁ ≫ c) = 𝟙 _) :
    (φ.hom ≫ c ≫ φ.inv) ≫ d₂ - q • (d₁ ≫ φ.hom ≫ c ≫ φ.inv) = 𝟙 _ := by
  have h₂' : φ.inv ≫ d₂ = g₂ ≫ φ.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h₂, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  calc (φ.hom ≫ c ≫ φ.inv) ≫ d₂ - q • (d₁ ≫ φ.hom ≫ c ≫ φ.inv)
      = φ.hom ≫ (c ≫ g₂ - q • (g₁ ≫ c)) ≫ φ.inv := by
        rw [Category.assoc, Category.assoc, h₂', reassoc_of% h₁]
        simp only [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.zsmul_comp,
          Preadditive.comp_zsmul, Category.assoc]
    _ = 𝟙 _ := by rw [hs, Category.id_comp, Iso.hom_inv_id]

end SlideConj

section Hom
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
  (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM rhoM : X}
  (h : muM + D.α i = nuM) (h₂ : nuM + D.α i = rhoM)

/-- The outer dot transported by the word comparison. -/
theorem homContentPostDot_outer_wordIso (Z : homWeightSector T W.obj muP muM) :
    homContentPostDot T W i betaP muP h₂ ((homContentPostE T W i betaP muP h).obj Z) ≫
        (homContentPostWordIso T W i betaP muP h h₂).hom.app Z =
      (homContentPostWordIso T W i betaP muP h h₂).hom.app Z ≫
        Z ◁ (W.E i h ◁ W.dot i h₂) := by
  rw [homContentPostWordIso_hom_app, homContentPostDot]
  have hc := homShiftConjugationIso_supernatural
    (homPost (k := k) (a := T (-muP)) (W.E i h₂)) (homPost (k := k) (W.E i h₂))
    (homContentShift D i betaP) (D.parity i) _
    ((homPostTransform (W.dot i h₂) (W.dot_mem i h₂)).isSupernatural (D.parity i))
    (Z ≫ W.E i h)
  simp only [homPostTransform, ↓reduceIte] at hc
  rw [← Category.assoc]
  erw [hc]
  rw [Category.assoc, Category.assoc]
  congr 1
  exact TwoSupercategory.associator_naturality_right (R := k) Z (W.E i h) (W.dot i h₂)

/-- The inner dot transported by the word comparison. -/
theorem homContentPostDot_inner_wordIso (Z : homWeightSector T W.obj muP muM) :
    (homContentPostE T W i betaP muP h₂).map (homContentPostDot T W i betaP muP h Z) ≫
        (homContentPostWordIso T W i betaP muP h h₂).hom.app Z =
      (homContentPostWordIso T W i betaP muP h h₂).hom.app Z ≫
        Z ◁ (W.dot i h ▷ W.E i h₂) := by
  rw [homContentPostWordIso_hom_app, homContentPostDot]
  have hc := homShiftConjugationIso_naturality
    (homPost (k := k) (a := T (-muP)) (W.E i h₂)) (homContentShift D i betaP)
    (TwoSupercategory.whiskerLeft_mem Z (W.dot_mem i h))
  rw [← Category.assoc]
  erw [hc]
  rw [Category.assoc, Category.assoc]
  congr 1
  exact TwoSupercategory.associator_naturality_middle (R := k) Z (W.dot i h) (W.E i h₂)

/-- The content-shifted postcomposition crossing at `Z`, as an endomorphism of the
two-letter object: the factor crossing conjugated by the word comparison. It is the parity
`p_i` component of `homContentPostCrossing` (`homContentPostCrossing_app`). -/
def homContentPostCrossingApp (Z : homWeightSector T W.obj muP muM) :
    End ((homContentPostE T W i betaP muP h₂).obj ((homContentPostE T W i betaP muP h).obj Z)) :=
  (homContentPostWordIso T W i betaP muP h h₂).hom.app Z ≫
    Z ◁ W.cross i i h h₂ h h₂ ≫ (homContentPostWordIso T W i betaP muP h h₂).inv.app Z

/-- **The post/post slide.** The content-shifted postcomposition crossing, followed by the
outer dot, minus `q` times the inner dot followed by the crossing, is the identity. -/
theorem homContentPostCrossing_slide_app (Z : homWeightSector T W.obj muP muM) :
    homContentPostCrossingApp T W i betaP muP h h₂ Z ≫
        homContentPostDot T W i betaP muP h₂ ((homContentPostE T W i betaP muP h).obj Z) -
      koszulSign (D.parity i) (D.parity i) •
        ((homContentPostE T W i betaP muP h₂).map (homContentPostDot T W i betaP muP h Z) ≫
          homContentPostCrossingApp T W i betaP muP h h₂ Z) = 𝟙 _ := by
  have hs := congrArg (fun g => Z ◁ g) (W.loc i h h₂).slide_right
  rw [sub_eq_add_neg, TwoSupercategory.whiskerLeft_add (R := k),
    TwoSupercategory.whiskerLeft_neg (R := k), TwoSupercategory.whiskerLeft_zsmul (R := k),
    TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.whiskerLeft_id (R := k), ← sub_eq_add_neg] at hs
  exact SlideConj.conj_slide ((homContentPostWordIso T W i betaP muP h h₂).app Z) _ _ _ _ _ _
    (homContentPostDot_outer_wordIso T W i betaP muP h h₂ Z)
    (homContentPostDot_inner_wordIso T W i betaP muP h h₂ Z) hs

end Hom

end OddMath.SKM
