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
local notation "Target" => E ≫ (homParityShift (k := k) κ).obj
  (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')
local notation "Source" => E ≫ ((homParityShift (k := k) κ).obj H ≫ F')

/-- A two-term polynomial moves to its literal source polynomial. -/
theorem homDistinctMixedMateDot_smul_pow_add (c d : k) (n : ℕ) :
    homDistinctMixedMateDot E A κ τ H (c • TX ^ n + d • TY) =
      (c • SX ^ n + d • SY : End Source) ≫ homDistinctMixedMate E A κ τ H := by
  have hX := homDistinctMixedMateDot_pow_mul_pow E A κ τ H hx hy n 0
  have hY := homDistinctMixedMateDot_pow_mul_pow E A κ τ H hx hy 0 1
  simp only [pow_zero, mul_one] at hX
  simp only [pow_zero, pow_one, one_mul] at hY
  rw [← homDistinctMixedMateDotLinear_apply, map_add, map_smul, map_smul,
    homDistinctMixedMateDotLinear_apply, homDistinctMixedMateDotLinear_apply,
    hX, hY, ← Linear.smul_comp, ← Linear.smul_comp, ← Preadditive.add_comp]

/-- The square difference moves in front of an arbitrary commuting crossing. -/
theorem homDistinctMixedMateDot_square_sub_comp
    (Φ : End Target) (h₁ : Commute Φ TY)
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y)) :
    homDistinctMixedMateDot E A κ τ H (((TX - TY) ^ 2 : End Target) ≫ Φ) =
      ((SX - SY) ^ 2 : End Source) ≫ homDistinctMixedMateDot E A κ τ H Φ := by
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
    (Φ : End Target) (h₁ : Commute Φ TY)
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y))
    (c d : k) (n : ℕ)
    (h : ((TX - TY) ^ 2 : End Target) ≫ Φ = c • TX ^ n + d • TY)
    (hL : IsUnit ((SX - SY) ^ 2 : End Source))
    (hR : IsUnit (c • SX ^ n + d • SY : End Source)) :
    IsIso (homDistinctMixedMateDot E A κ τ H Φ) := by
  have : IsIso (c • SX ^ n + d • SY : End Source) := (isUnit_iff_isIso _).mp hR
  have hR' : IsIso (homDistinctMixedMateDot E A κ τ H (c • TX ^ n + d • TY)) := by
    rw [homDistinctMixedMateDot_smul_pow_add E A κ τ H hx hy]
    infer_instance
  rw [← h, homDistinctMixedMateDot_square_sub_comp E A κ τ H hx hy Φ h₁ h₂] at hR'
  have : IsIso ((SX - SY) ^ 2 : End Source) := (isUnit_iff_isIso _).mp hL
  exact IsIso.of_isIso_comp_left ((SX - SY) ^ 2 : End Source) _

end Mate
end OddMath.SKM
