import OddMath.QuiverHecke.CyclotomicAction.ELVEvenPolynomialBoundary
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryInputDefect

/-! # Even input-dot recurrence for the polynomial boundary

The parity-zero specialization of DeformedBoundaryDivision (8).
On arbitrary old Homs the actual polynomial boundary commutes with ordinary
coefficient shift up to a polynomial-constant defect. Its iterated high
coordinates therefore telescope exactly. Every exterior old coefficient is
retained; no restriction is imposed on the other colours or their support.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem evenBoundary_twist_zero (v t : List I) (b : Old D Sc cutoff v t) :
    oldTwist D Sc cutoff 0 v t b = b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  change (ideal D Sc cutoff v t).mkQ (twist k 0 b) = _
  rw [twist_zero]

/-- At even moving colour the input shift is the ordinary coefficient shift. -/
theorem appendInputShift_eq_evenLongShift (i : I) (hi : D.parity i = 0)
    (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    appendInputShift D Sc cutoff i v t f = evenLongShift D Sc cutoff v t f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    simp only [appendInputShift, LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, appendOutputShift, Finsupp.lsum_single, Finsupp.lsingle_apply,
      hi, evenBoundary_twist_zero, evenLongShift_single]

theorem evenLongShift_apply_succ (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) (m : ℕ) :
    evenLongShift D Sc cutoff v t f (m + 1) = f m := by
  exact Finsupp.mapDomain_apply_of_injective Nat.succ_injective f m

/-- The only defect of even input-dot compatibility is polynomial-constant. -/
theorem offDiagonalPolynomialBoundary_even_shift (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t (evenLongShift D Sc cutoff v t f) =
      evenLongShift D Sc cutoff v t (offDiagonalPolynomialBoundary D Sc cutoff p i v t f) +
      Finsupp.single 0
        (appendC0InputDefect D Sc cutoff i v t
          (pMap D Sc cutoff i v (t ++ [i]) (offDiagonalLongSection D Sc cutoff p i v t f)) 0) := by
  let z := pMap D Sc cutoff i v (t ++ [i]) (offDiagonalLongSection D Sc cutoff p i v t f)
  have h := appendC0InputDefect_degreeZero D Sc cutoff i v t z
  change appendC0 D Sc cutoff i v t
    (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1 z) -
      appendInputShift D Sc cutoff i v t (appendC0 D Sc cutoff i v t z) = _ at h
  have hp := pMap_movingEvenDot D Sc cutoff i hi v (t ++ [i])
    (offDiagonalLongSection D Sc cutoff p i v t f)
  rw [evenMoving_offDiagonalLongSection D Sc cutoff p i hi] at hp
  rw [← hp] at h
  change offDiagonalPolynomialBoundary D Sc cutoff p i v t (evenLongShift D Sc cutoff v t f) -
    appendInputShift D Sc cutoff i v t (offDiagonalPolynomialBoundary D Sc cutoff p i v t f) = _ at h
  rw [appendInputShift_eq_evenLongShift D Sc cutoff i hi] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- Exact high-coordinate telescoping of all even boundary iterates. -/
theorem offDiagonalPolynomialBoundary_even_iterate_high (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (n m : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t
      ((evenLongShift D Sc cutoff v t)^[n] f) (n + m) =
      offDiagonalPolynomialBoundary D Sc cutoff p i v t f m := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, zero_add]
  | succ n ih =>
    rw [Function.iterate_succ_apply',
      offDiagonalPolynomialBoundary_even_shift D Sc cutoff p i hi]
    have he : n + 1 + m = (n + m) + 1 := by omega
    rw [he, Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega), add_zero,
      evenLongShift_apply_succ, ih]

end OddMath.QuiverHecke.ELVOld
