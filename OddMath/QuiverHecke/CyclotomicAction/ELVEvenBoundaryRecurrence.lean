/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryPolynomial

/-! # Even-moving boundary recurrence

The positive coefficients of the section-defined boundary obey the input-dot
recurrence. The proof uses the actual moving operator, long extraction and
C₀'s constant defect on the original append quotient.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem twistZero (v : List I) (b : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff 0 v v b = b := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  change (ideal D Sc cutoff v v).mkQ (twist k 0 c) = _
  rw [twist_zero]

private theorem moving_eq_signed (i : I) (hi : D.parity i = 0)
    (v : List I) (z : Target D Sc cutoff i v (v ++ [i])) :
    movingPowerTarget D Sc cutoff i v (v ++ [i]) 1 (by simp [hi]) z =
      signedMovingPowerTarget D Sc cutoff i v (v ++ [i]) 1 z := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v (v ++ [i]) z
  rw [movingPowerTarget_projection, signedMovingPowerTarget_projection]

private theorem shift_apply_succ (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (n : ℕ) :
    appendOutputShift D Sc cutoff v v f (n + 1) = f n := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]
  | single m b =>
    simp only [appendOutputShift, Finsupp.lsum_single, Finsupp.lsingle_apply]
    by_cases h : n = m
    · subst n; simp only [Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (by omega), Finsupp.single_eq_of_ne h]

private theorem shift_apply_zero (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) :
    appendOutputShift D Sc cutoff v v f 0 = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, add_zero]
  | single m b => simp [appendOutputShift]

/-- The extracted even moving dot is the ordinary exponent shift on full old
coefficients, for every normalization p. -/
theorem outputLongExtraction_evenDot (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (z : Target D Sc cutoff i v (v ++ [i])) :
    outputLongExtraction D Sc cutoff p i v
      (movingPowerTarget D Sc cutoff i v (v ++ [i]) 1 (by simp [hi]) z) =
    appendOutputShift D Sc cutoff v v (outputLongExtraction D Sc cutoff p i v z) := by
  rw [moving_eq_signed D Sc cutoff i hi]
  ext n
  cases n with
  | zero =>
    rw [outputLongExtraction_apply, outputLongCoordinate_signedMoving_zero D Sc cutoff p i v 1
      (by omega), shift_apply_zero]
  | succ n =>
    rw [shift_apply_succ, outputLongExtraction_apply, outputLongExtraction_apply]
    have h := outputLongCoordinate_signedMoving D Sc cutoff p i v n 1 z
    simpa only [hi, zero_mul, SKM.zsign, zero_ne_one, ↓reduceIte, one_pow,
      one_smul, twistZero, Nat.add_comm] using h

/-- High coefficients of the actual boundary satisfy the even-dot recurrence;
the discarded part is exactly the already constructed constant C₀ defect. -/
theorem evenPolynomialBoundary_shift_high (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (m : ℕ) :
    evenPolynomialBoundary D Sc cutoff p i v (appendOutputShift D Sc cutoff v v f) (m + 1) =
      evenPolynomialBoundary D Sc cutoff p i v f m := by
  let z := outputLongSection D Sc cutoff p i v f
  have h := evenPolynomialBoundary_factor D Sc cutoff p i v
    (movingPowerTarget D Sc cutoff i v (v ++ [i]) 1 (by simp [hi]) z)
  rw [outputLongExtraction_evenDot D Sc cutoff p i hi, outputLongExtraction_section,
    pMap_movingEvenDot D Sc cutoff i hi] at h
  have hd := congrArg (fun g : ℕ →₀ Old D Sc cutoff v v => g (m + 1))
    (appendC0InputDefect_degreeZero D Sc cutoff i v v (pMap D Sc cutoff i v (v ++ [i]) z))
  simp only [appendC0InputDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    Finsupp.sub_apply, Finsupp.single_eq_of_ne (show m + 1 ≠ 0 by omega), sub_eq_zero] at hd
  rw [← h, hd]
  change appendOutputShift D Sc cutoff v v
    (Finsupp.mapRange.linearMap (oldTwist D Sc cutoff (D.parity i) v v)
      (evenPolynomialBoundary D Sc cutoff p i v f)) (m + 1) = _
  rw [shift_apply_succ]
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, hi, twistZero]

end OddMath.QuiverHecke.ELVOld
