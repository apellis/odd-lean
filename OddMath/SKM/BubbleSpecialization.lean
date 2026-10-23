/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleTruncation

/-!
# Unit-top specializations of the abstract bubble coefficients

Every finite family in the existing `SYM` is fixed by all sufficiently large
colour-dependent specializations which retain lower elementary generators,
set the top generator to one, kill higher generators, and retain every
exterior generator. The headline theorem is
`SYM.exists_unitCutoff_fixed_coefficients`.

This is the coefficient-side reduction for testing a finite matching relation
in Brundan–Ellis, *Super Kac–Moody 2-categories*, §8. A unit top coefficient
allows an associated monic cyclotomic polynomial to have unit constant term,
without choosing generic roots or proving a separate polynomial/exterior
basis theorem. No representation or compatibility with a vacuum bubble
evaluation is asserted here. The colour set may be infinite.
-/

noncomputable section
open scoped Classical
namespace OddMath.SKM.SYM

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k]

private def unitCutoffGen (cut : I → ℕ) : SYMGen D → SYM D k
  | .inl (i, n) => if n < cut i then e D k i n else if n = cut i then 1 else 0
  | .inr i => delta D k i

private theorem unitCutoff_rel (cut : I → ℕ)
    {x y : FreeAlgebra k (SYMGen D)} (h : SYMRel D k x y) :
    FreeAlgebra.lift k (unitCutoffGen D k cut) x =
      FreeAlgebra.lift k (unitCutoffGen D k cut) y := by
  cases h with
  | polynomial a b =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply, unitCutoffGen]
      split_ifs <;> first
        | exact (e_commute D k a.1 b.1 a.2 b.2).eq
        | simp_all only [zero_mul, mul_zero, one_mul, mul_one]
  | mixed a i =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply, unitCutoffGen]
      split_ifs <;> first
        | exact (e_delta_commute D k a.1 a.2 i).eq
        | simp_all only [zero_mul, mul_zero, one_mul, mul_one]
  | exterior i j =>
      simp only [map_mul, map_neg, FreeAlgebra.lift_ι_apply, unitCutoffGen]
      exact delta_anticommute D k i j
  | square i =>
      simp only [map_pow, map_zero, FreeAlgebra.lift_ι_apply, unitCutoffGen]
      exact delta_sq D k i

/-- Retain elementary generators below a colour-dependent cutoff, send the top
one to 1 and higher ones to 0, and retain every exterior generator. -/
def unitCutoff (cut : I → ℕ) : SYM D k →ₐ[k] SYM D k :=
  RingQuot.liftAlgHom k
    ⟨FreeAlgebra.lift k (unitCutoffGen D k cut), fun _ _ h => unitCutoff_rel D k cut h⟩

@[simp] theorem unitCutoff_e (cut : I → ℕ) (i : I) (n : ℕ) :
    unitCutoff D k cut (e D k i n) =
      if n < cut i then e D k i n else if n = cut i then 1 else 0 := by
  simp only [unitCutoff, e, ι, mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply, unitCutoffGen]

@[simp] theorem unitCutoff_delta (cut : I → ℕ) (i : {i : I // D.parity i = 1}) :
    unitCutoff D k cut (delta D k i) = delta D k i := by
  simp only [unitCutoff, delta, ι, mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply, unitCutoffGen]

@[simp] theorem unitCutoff_top (cut : I → ℕ) (i : I) :
    unitCutoff D k cut (e D k i (cut i)) = 1 := by
  simp

/-- Each finite coefficient expression is fixed by every sufficiently large
colour-dependent unit-top specialization. -/
theorem exists_unitCutoff_fixed (p : SYM D k) :
    ∃ N : ℕ, ∀ cut : I → ℕ, (∀ i, N ≤ cut i) → unitCutoff D k cut p = p := by
  obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective k (SYMRel D k) p
  induction p using FreeAlgebra.induction with
  | grade0 r => exact ⟨0, fun _ _ => by simp only [AlgHom.commutes]⟩
  | grade1 g =>
      cases g with
      | inl a =>
          refine ⟨a.2 + 1, fun cut hcut => ?_⟩
          change unitCutoff D k cut (e D k a.1 a.2) = e D k a.1 a.2
          rw [unitCutoff_e, ite_eq_left (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hcut a.1))]
      | inr i =>
          exact ⟨0, fun _ _ => unitCutoff_delta D k _ i⟩
  | mul p q hp hq =>
      obtain ⟨N, hN⟩ := hp
      obtain ⟨M, hM⟩ := hq
      refine ⟨max N M, fun cut hcut => ?_⟩
      simp only [map_mul,
        hN cut (fun i => (Nat.le_max_left N M).trans (hcut i)),
        hM cut (fun i => (Nat.le_max_right N M).trans (hcut i))]
  | add p q hp hq =>
      obtain ⟨N, hN⟩ := hp
      obtain ⟨M, hM⟩ := hq
      refine ⟨max N M, fun cut hcut => ?_⟩
      simp only [map_add,
        hN cut (fun i => (Nat.le_max_left N M).trans (hcut i)),
        hM cut (fun i => (Nat.le_max_right N M).trans (hcut i))]

/-- A finite family is fixed simultaneously, without a bound on the colour set. -/
theorem exists_unitCutoff_fixed_finset (P : Finset (SYM D k)) :
    ∃ N : ℕ, ∀ cut : I → ℕ, (∀ i, N ≤ cut i) →
      ∀ p ∈ P, unitCutoff D k cut p = p := by
  induction P using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert p P _ ih =>
      obtain ⟨N, hN⟩ := exists_unitCutoff_fixed D k p
      obtain ⟨M, hM⟩ := ih
      refine ⟨max N M, fun cut hcut q hq => ?_⟩
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hN cut (fun i => (Nat.le_max_left N M).trans (hcut i))
      · exact hM cut (fun i => (Nat.le_max_right N M).trans (hcut i)) q hq

/-- Arbitrarily large unit-top specializations preserve every coefficient of a
finite matching expansion. Compatibility with a bubble evaluation is separate. -/
theorem exists_unitCutoff_fixed_coefficients {A : Type*} (c : A →₀ SYM D k) :
    ∃ N : ℕ, ∀ cut : I → ℕ, (∀ i, N ≤ cut i) →
      ∀ a, unitCutoff D k cut (c a) = c a := by
  obtain ⟨N, hN⟩ := exists_unitCutoff_fixed_finset D k (c.support.image c)
  refine ⟨N, fun cut hcut a => ?_⟩
  by_cases ha : a ∈ c.support
  · exact hN cut hcut (c a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  · rw [Finsupp.notMem_support_iff.mp ha, map_zero]

end OddMath.SKM.SYM
