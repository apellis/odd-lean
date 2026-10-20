/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.MixedBoundaryCoefficients
import OddMath.SKM.GraphicalSeries

/-! # BE2 Theorem 10.3 over the generic covering ring

The actual sesquilinear form equals the independently defined finite graphical
expression for arbitrary physical boundary words and both external weights.
Colours are arbitrary and no bar-consistency hypothesis is needed. The
additive-weight and purely-even covering-coefficient conventions are unchanged.
No nondegeneracy hypothesis is used.
-/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord CoveringQuantum
open CoveringQuantum.Coefficients CoveringQuantum.UDot.GenericTensor
open CoveringQuantum.UDot.GenericVerma.MixedGram
open scoped LaurentSeries RatFunc

private theorem covering_eq_of_coeff (x y : Coefficients.Ring)
    (h : ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      (signLaurent σ hσ x).coeff z = (signLaurent σ hσ y).coeff z) : x = y := by
  have hs (σ : ℚ) (hσ : σ ^ 2 = 1) : signLaurent σ hσ x = signLaurent σ hσ y :=
    HahnSeries.ext (funext (h σ hσ))
  apply (eq_iff_specialize_eq x y).mpr
  constructor
  · apply (algebraMap (RatFunc ℚ) (LaurentSeries ℚ)).injective
    simpa only [signLaurent, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, map_one] using hs 1 (by norm_num)
  · apply (algebraMap (RatFunc ℚ) (LaurentSeries ℚ)).injective
    simpa only [signLaurent, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, map_neg, map_one] using hs (-1) (by norm_num)

variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]

/-- Equal-weight BE2 Theorem 10.3, for any complete unique strict representative
family. Distinguished points and serializers are chosen in the proof, not
assumed in the identity. The graphical expression is independent of the form. -/
theorem sesquilinearForm_eq_graphical (D : RootDatum I X)
    (μ : X)
    (a b : List (Letter I)) (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ a b R ∧ StrictReduced₂ a R)
    (hrep : ∀ R, IsMatching₂ a b R → StrictReduced₂ a R →
      ∃ S ∈ M, Iso (pairing₂ a S) (pairing₂ a R))
    (huniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ a R) (pairing₂ a S) → R = S) :
    sesquilinearForm D (algebraWord D μ a) (algebraWord D μ b) =
      GraphicalSeries.expression D μ a b M (fun R hR => (hM R hR).1) huniq := by
  classical
  have hp (R : M) := matching_bounded_points (hM R R.property).1
  choose q hq using hp
  have hd (R : M) (c : MatchingStrand a R.val → ℕ) :=
    exists_decorates₂_of_bounded_points a R.val (q R)
      (fun j hj => (hq R j hj).2) (fun j hj => (hq R j hj).1) c
  choose τ hτ using hd
  apply covering_eq_of_coeff
  intro σ hσ z
  exact (mixed_boundary_labelled_form_coeff D μ a b M hM hrep huniq
    q (fun R j hj => (hq R j hj).2) τ (fun R c => (hτ R c).1) σ hσ z).trans
    (GraphicalSeries.expression_coeff D μ a b M (fun R hR => (hM R hR).1) huniq
      q (fun R j hj => (hq R j hj).2) τ (fun R c => (hτ R c).1) σ hσ z).symm

/-- Unequal external right weights are orthogonal in the actual modified form.
This uses its two-sided blocks, not a mismatch of the words' left endpoints. -/
theorem sesquilinearForm_words_eq_zero_of_right_weight_ne (D : RootDatum I X)
    (ζ μ : X) (hne : ζ ≠ μ)
    (a b : List (Letter I)) :
    sesquilinearForm D (algebraWord D ζ a) (algebraWord D μ b) = 0 := by
  exact sesquilinearForm_orthogonal D (ζ + shift D a) ζ (μ + shift D b) μ
    _ _ (algebraWord_mem_block D ζ a) (algebraWord_mem_block D μ b) (Or.inr hne)

/-- The two-weight graphical identity of BE2, arXiv:1701.04133v2,
Theorem 10.3 (the displayed graphical sum), over the generic covering ring
for arbitrary colours without bar consistency. The indicator is the literal
Kronecker factor on external weights; all words retain physical order. -/
theorem theorem103 (D : RootDatum I X)
    (ζ μ : X)
    (a b : List (Letter I)) (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ a b R ∧ StrictReduced₂ a R)
    (hrep : ∀ R, IsMatching₂ a b R → StrictReduced₂ a R →
      ∃ S ∈ M, Iso (pairing₂ a S) (pairing₂ a R))
    (huniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ a R) (pairing₂ a S) → R = S) :
    sesquilinearForm D (algebraWord D ζ a) (algebraWord D μ b) =
      (if ζ = μ then 1 else 0) *
        GraphicalSeries.expression D ζ a b M (fun R hR => (hM R hR).1) huniq := by
  by_cases h : ζ = μ
  · subst μ
    simpa only [ite_true, one_mul] using
      sesquilinearForm_eq_graphical D ζ a b M hM hrep huniq
  · rw [ite_eq_right h, zero_mul]
    exact sesquilinearForm_words_eq_zero_of_right_weight_ne D ζ μ h a b

end OddMath.SKM
