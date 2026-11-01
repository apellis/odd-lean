/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierHomDistinctMixedPostDotsComp

/-! # Low-degree unit criteria for the post-side mixed mate

The two source polynomials are required to be units, rather than requiring
one nilpotence exponent for a whole weight fibre. Componentwise ELV bounds
can therefore supply the inputs. The dot transport and parity shifts are
exactly those of the existing mixed mate.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

private theorem commute_square_sub {R : Type*} [Ring R] {x y : R}
    (h : Commute x y) :
    (x - y) ^ 2 = x ^ 2 - (x * y + x * y) + y ^ 2 := by
  simp only [pow_two, sub_mul, mul_sub]
  rw [← h.eq]
  abel

section Mate
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)
  {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
  {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0)

local notation "TX" => mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x
local notation "TY" => mixedPostTargetPostDot (k := k) E κ H (F' := F') y
local notation "SX" => mixedPostSourcePreDot (k := k) E κ H (F' := F') x
local notation "SY" => mixedPostSourcePostDot (k := k) E κ H A y

include hx hy

/-- A two-term polynomial moves to its literal source polynomial. -/
theorem homDistinctMixedMateDot_smul_pow_add (c d : k) (n : ℕ) :
    homDistinctMixedMateDot E A κ τ H (c • TX ^ n + d • TY) =
      (c • SX ^ n + d • SY : End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) ≫ homDistinctMixedMate E A κ τ H := by
  have hX := homDistinctMixedMateDot_pow_mul_pow E A κ τ H hx hy n 0
  have hY := homDistinctMixedMateDot_pow_mul_pow E A κ τ H hx hy 0 1
  simp only [pow_zero, mul_one] at hX
  simp only [pow_zero, pow_one, one_mul] at hY
  rw [← homDistinctMixedMateDotLinear_apply, map_add, map_smul, map_smul,
    homDistinctMixedMateDotLinear_apply, homDistinctMixedMateDotLinear_apply,
    hX, hY, ← Linear.smul_comp, ← Linear.smul_comp, ← Preadditive.add_comp]

/-- The square difference moves in front of an arbitrary commuting crossing. -/
theorem homDistinctMixedMateDot_square_sub_comp
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) (h₁ : Commute Φ TY)
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y)) :
    homDistinctMixedMateDot E A κ τ H (((TX - TY) ^ 2 : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) ≫ Φ) =
      ((SX - SY) ^ 2 : End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) ≫ homDistinctMixedMateDot E A κ τ H Φ := by
  have h20 := homDistinctMixedMateDot_pow_mul_pow_comp E A κ τ H hx hy 2 0 Φ h₁ h₂
  have h11 := homDistinctMixedMateDot_pow_mul_pow_comp E A κ τ H hx hy 1 1 Φ h₁ h₂
  have h02 := homDistinctMixedMateDot_pow_mul_pow_comp E A κ τ H hx hy 0 2 Φ h₁ h₂
  simp only [pow_zero, mul_one] at h20
  simp only [pow_one] at h11
  simp only [pow_zero, one_mul] at h02
  rw [commute_square_sub (commute_mixedPostTarget E κ H hx (y := y)),
    commute_square_sub (commute_mixedPostSource E A κ H hx (y := y)),
    Preadditive.add_comp, Preadditive.sub_comp, Preadditive.add_comp,
    ← homDistinctMixedMateDotLinear_apply, map_add, map_sub, map_add,
    homDistinctMixedMateDotLinear_apply, homDistinctMixedMateDotLinear_apply,
    homDistinctMixedMateDotLinear_apply, homDistinctMixedMateDotLinear_apply,
    h20, h11, h02, ← Preadditive.add_comp, ← Preadditive.sub_comp,
    ← Preadditive.add_comp]

/-- Two explicit source-unit inputs imply invertibility of the mixed mate.

No global nilpotence or uniform fibre bound is required. -/
theorem homDistinctMixedMateDot_isIso_of_square_sub_units
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) (h₁ : Commute Φ TY)
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y))
    (c d : k) (n : ℕ)
    (h : ((TX - TY) ^ 2 : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) ≫ Φ = c • TX ^ n + d • TY)
    (hL : IsUnit ((SX - SY) ^ 2 : End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))))
    (hR : IsUnit (c • SX ^ n + d • SY : End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')))) :
    IsIso (homDistinctMixedMateDot E A κ τ H Φ) := by
  have : IsIso (c • SX ^ n + d • SY : End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) := (isUnit_iff_isIso _).mp hR
  have hR' : IsIso (homDistinctMixedMateDot E A κ τ H (c • TX ^ n + d • TY)) := by
    rw [homDistinctMixedMateDot_smul_pow_add E A κ τ H hx hy]
    infer_instance
  rw [← h, homDistinctMixedMateDot_square_sub_comp E A κ τ H hx hy Φ h₁ h₂] at hR'
  have : IsIso ((SX - SY) ^ 2 : End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) := (isUnit_iff_isIso _).mp hL
  exact IsIso.of_isIso_comp_left ((SX - SY) ^ 2 : End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) _

end Mate
section Conj
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)

/-- The literal conjugated crossing satisfies the same source-unit criterion. -/
theorem homDistinctMixedMateDot_isIso_of_conj_units {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0)
    (α : End ((homParityShift (k := k) τ).obj
      ((E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫ E')))
    (h₁ : Commute α (mixedPostJPostDot (k := k) E κ τ H (F' := F') y))
    (h₂ : Commute α (mixedPostJMidDot (k := k) E κ τ H (E' := E')
      ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)))
    (e : ℕ) (β : k)
    (h : α * α * ((mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y) *
        (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y)) =
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ^ e +
        β • mixedPostJPostDot (k := k) E κ τ H (F' := F') y)
    (hL : IsUnit ((mixedPostSourcePreDot (k := k) E κ H (F' := F') x -
      mixedPostSourcePostDot (k := k) E κ H A y) ^ 2))
    (hR : IsUnit ((-1 : k) • mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ e +
      (-β) • mixedPostSourcePostDot (k := k) E κ H A y)) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      ((homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).hom ≫
        (-(α ≫ α ≫
          (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv)))) := by
  have hχ : ∀ f, isoConjRingHom
      (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).symm f =
      (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).hom ≫ f ≫
        (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv :=
    fun f => rfl
  have hX : mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x =
      isoConjRingHom
        (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).symm
        (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) := by
    rw [hχ]
    have h' := homMixedInterchange_pre (k := k) E E' κ τ
      ((homParityShift (k := k) κ).obj H ≫ F') x hx
    rw [koszulSign_zero_right, one_smul] at h'
    rw [← reassoc_of% h', Iso.hom_inv_id, Category.comp_id]
  have hY : mixedPostTargetPostDot (k := k) E κ H (F' := F') y =
      isoConjRingHom
        (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).symm
        (mixedPostJPostDot (k := k) E κ τ H (F' := F') y) := by
    rw [hχ]
    have h' := homMixedInterchange_post (k := k) E E' κ τ
      ((homParityShift (k := k) κ).obj H ≫ F') y hy
    rw [koszulSign_zero_right, one_smul] at h'
    rw [← reassoc_of% h', Iso.hom_inv_id, Category.comp_id]
  have hΓ : mixedPostTargetTransposeDot (k := k) E κ H A y =
      isoConjRingHom
        (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).symm
        (mixedPostJMidDot (k := k) E κ τ H (E' := E')
          ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)) := by
    rw [hχ]
    have h' := homMixedInterchange_naturality_even (k := k) E E' κ τ
      (TwoSupercategory.whiskerLeft_mem ((homParityShift (k := k) κ).obj H)
        (SuperAdjunction.rightTranspose_mem A A hy))
    rw [← reassoc_of% h', Iso.hom_inv_id, Category.comp_id]
  have hΦ : (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).hom ≫
        (-(α ≫ α ≫
          (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv)) =
      isoConjRingHom
        (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).symm
        (-(α * α)) := by
    rw [hχ, End.mul_def]
    erw [Preadditive.neg_comp]
    rw [Preadditive.comp_neg, Category.assoc]
    exact (Preadditive.comp_neg _ _).symm
  refine homDistinctMixedMateDot_isIso_of_square_sub_units E A κ τ H hx hy _ ?_ ?_
    (-1 : k) (-β) e ?_ hL hR
  · rw [hΦ, hY]
    exact ((h₁.mul_left h₁).neg_left).map _
  · rw [hΦ, hΓ]
    exact ((h₂.mul_left h₂).neg_left).map _
  · have key : -(α * α) *
        (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
          mixedPostJPostDot (k := k) E κ τ H (F' := F') y) ^ 2 =
        (-1 : k) • mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ^ e +
          (-β) • mixedPostJPostDot (k := k) E κ τ H (F' := F') y := by
      rw [pow_two, neg_mul, h, neg_add, neg_smul, one_smul, neg_smul]
    have hh := congrArg (isoConjRingHom
      (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).symm) key
    simp only [map_mul, map_neg, map_sub, map_pow, map_add, isoConjRingHom_smul] at hh
    rw [hΦ, hX, hY, ← End.mul_def]
    exact hh

end Conj

end OddMath.SKM
