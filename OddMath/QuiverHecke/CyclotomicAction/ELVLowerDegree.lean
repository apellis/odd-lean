/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HomDimension
import OddMath.QuiverHecke.CyclotomicAction.ELVHomGrading

/-! # Cutoff-independent lower degrees of coefficient Homs

For each pair of boundary words, the full ELV coefficient Hom is bounded
below independently of the coefficient cutoff. The bound comes from affine
PBW crossing degrees; all polynomial and exterior coefficient degrees are
nonnegative. This is the source bound needed for low-degree cyclotomic
ideal separation, not an injectivity assertion about the quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous)

/-- Negative coefficient degrees vanish before imposing any ELV relations. -/
theorem coefficientDegreePart_eq_bot_of_neg (n : ℤ) (hn : n < 0) :
    SKM.SYM.coefficientDegreePart D k sy n = ⊥ := by
  unfold SKM.SYM.coefficientDegreePart
  convert Submodule.span_empty
  refine Set.image_eq_empty.mpr (Set.eq_empty_of_forall_notMem fun a ha => ?_)
  have h := SKM.SYM.coefficientDegree_nonneg D sy a
  change SKM.SYM.coefficientDegree D sy a = n at ha
  omega

/-- Quotienting the full coefficient algebra does not introduce negative degrees. -/
theorem elvCoefficientDegree_eq_bot_of_neg (cutoff : I → ℕ) (n : ℤ) (hn : n < 0) :
    SKM.SYM.elvCoefficientDegree (k := k) D sy cutoff n = ⊥ := by
  unfold SKM.SYM.elvCoefficientDegree
  rw [coefficientDegreePart_eq_bot_of_neg D sy n hn, Submodule.map_bot]

include hc in
/-- The affine PBW lower bound works over an arbitrary commutative ground ring. -/
theorem exists_homDegree_lower_bound (v w : List I) :
    ∃ L : ℤ, ∀ n, n < L → homDegree D sy Sc v w n = ⊥ := by
  obtain ⟨L, hL⟩ := exists_le_deg D sy v w
  refine ⟨L, fun n hn => ?_⟩
  change GradedSupercategory.degree (R := k) (C := HGr D Sc sy hc)
    (hObj D Sc sy hc v) (hObj D Sc sy hc w) n = ⊥
  rw [degree_eq_span]
  convert Submodule.span_empty
  refine Set.image_eq_empty.mpr (Set.eq_empty_of_forall_notMem fun a ha => ?_)
  have h := hL a
  change a.deg D sy = n at ha
  omega

/-- A lower bound on affine degrees is unchanged by full ELV coefficients. -/
theorem elvHomDegree_eq_bot_of_lower_bound (v w : List I) (L : ℤ)
    (hL : ∀ n, n < L → homDegree D sy Sc v w n = ⊥)
    (cutoff : I → ℕ) (n : ℤ) (hn : n < L) :
    elvHomDegree D sy Sc hc cutoff v w n = ⊥ := by
  let _ := elvCoefficientCategoryGrading (k := k) D sy cutoff
  let _ := gradedSupercategory D sy Sc hc
  apply bot_unique
  apply BoxProd.homDeg_le_iff.mpr
  intro r s hrs a ha f hf
  by_cases hr : r < 0
  · change a ∈ SKM.SYM.elvCoefficientDegree (k := k) D sy cutoff r at ha
    rw [elvCoefficientDegree_eq_bot_of_neg D sy cutoff r hr] at ha
    have he : a = 0 := ha
    subst a
    simp [BoxProd.tmulHom_def]
  · change f ∈ homDegree D sy Sc v w s at hf
    rw [hL s (by omega)] at hf
    have he : f = 0 := hf
    subst f
    simp [BoxProd.tmulHom_def]

/-- One PBW bound works for every non-uniform coefficient cutoff. -/
theorem exists_elvHomDegree_lower_bound (v w : List I) :
    ∃ L : ℤ, ∀ cutoff : I → ℕ, ∀ n, n < L →
      elvHomDegree D sy Sc hc cutoff v w n = ⊥ := by
  obtain ⟨L, hL⟩ := exists_homDegree_lower_bound D sy Sc hc v w
  exact ⟨L, elvHomDegree_eq_bot_of_lower_bound D sy Sc hc v w L hL⟩

end OddMath.QuiverHecke
