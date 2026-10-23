/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleAlgebra

/-!
# Finite coefficient truncations of the all-colour bubble algebra

Every finite expression in `SYM` uses finitely many polynomial and exterior
coefficients. Setting all other generators to zero defines an algebra
endomorphism, and these finite truncations jointly separate elements.

The headline theorem `SYM.truncations_separate` is the coefficient-side reduction
needed when testing a putative finite matching relation in sufficiently large
cyclotomic representations. It does not identify any truncation with a diagram
or a 2-representation: that compatibility remains a separate obligation in the
Nondegeneracy Conjecture of Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.
No finiteness of the colour set or assumption about the bubble map is used.
-/

noncomputable section
open scoped Classical
namespace OddMath.SKM.SYM

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k]

private def truncateGen (S : Finset (SYMGen D)) (g : SYMGen D) : SYM D k :=
  if g ∈ S then ι D k g else 0

private theorem truncate_rel (S : Finset (SYMGen D))
    {x y : FreeAlgebra k (SYMGen D)} (h : SYMRel D k x y) :
    FreeAlgebra.lift k (truncateGen D k S) x =
      FreeAlgebra.lift k (truncateGen D k S) y := by
  classical
  cases h with
  | polynomial a b =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply, truncateGen]
      split_ifs <;> first
        | exact (e_commute D k a.1 b.1 a.2 b.2).eq
        | simp_all only [zero_mul, mul_zero]
  | mixed a i =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply, truncateGen]
      split_ifs <;> first
        | exact (e_delta_commute D k a.1 a.2 i).eq
        | simp_all only [zero_mul, mul_zero]
  | exterior i j =>
      simp only [map_mul, map_neg, FreeAlgebra.lift_ι_apply, truncateGen]
      split_ifs <;> first
        | exact delta_anticommute D k i j
        | simp_all only [zero_mul, mul_zero, neg_zero]
  | square i =>
      simp only [map_pow, map_zero, FreeAlgebra.lift_ι_apply, truncateGen]
      split_ifs
      · exact delta_sq D k i
      · simp

/-- Set generators outside the finite set `S` to zero, retaining both parities. -/
def truncate (S : Finset (SYMGen D)) : SYM D k →ₐ[k] SYM D k :=
  RingQuot.liftAlgHom k
    ⟨FreeAlgebra.lift k (truncateGen D k S), fun _ _ h => truncate_rel D k S h⟩

@[simp] theorem truncate_ι (S : Finset (SYMGen D)) (g : SYMGen D) :
    truncate D k S (ι D k g) = if g ∈ S then ι D k g else 0 := by
  classical
  simp only [truncate, ι, mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply, truncateGen]

/-- Every coefficient is fixed by all truncations containing a finite set of generators. -/
theorem exists_truncate_fixed (p : SYM D k) :
    ∃ S : Finset (SYMGen D), ∀ T, S ⊆ T → truncate D k T p = p := by
  classical
  obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective k (SYMRel D k) p
  induction p using FreeAlgebra.induction with
  | grade0 r =>
      exact ⟨∅, fun _ _ => by simp only [AlgHom.commutes]⟩
  | grade1 g =>
      refine ⟨{g}, fun T hT => ?_⟩
      change truncate D k T (ι D k g) = ι D k g
      rw [truncate_ι, ite_eq_left (hT (Finset.mem_singleton_self g))]
  | mul p q hp hq =>
      obtain ⟨S, hS⟩ := hp
      obtain ⟨T, hT⟩ := hq
      refine ⟨S ∪ T, fun U hU => ?_⟩
      simp only [map_mul, hS U (Finset.subset_union_left.trans hU),
        hT U (Finset.subset_union_right.trans hU)]
  | add p q hp hq =>
      obtain ⟨S, hS⟩ := hp
      obtain ⟨T, hT⟩ := hq
      refine ⟨S ∪ T, fun U hU => ?_⟩
      simp only [map_add, hS U (Finset.subset_union_left.trans hU),
        hT U (Finset.subset_union_right.trans hU)]

/-- A single finite truncation fixes every element of a prescribed finite family. -/
theorem exists_truncate_fixed_finset (P : Finset (SYM D k)) :
    ∃ S : Finset (SYMGen D), ∀ T, S ⊆ T → ∀ p ∈ P, truncate D k T p = p := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | @insert p P _ ih =>
      obtain ⟨S, hS⟩ := exists_truncate_fixed D k p
      obtain ⟨T, hT⟩ := ih
      refine ⟨S ∪ T, fun U hU q hq => ?_⟩
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hS U (Finset.subset_union_left.trans hU)
      · exact hT U (Finset.subset_union_right.trans hU) q hq

/-- The coefficient family of a finite matching expansion is fixed by one truncation. -/
theorem exists_truncate_fixed_coefficients {A : Type*} (c : A →₀ SYM D k) :
    ∃ S : Finset (SYMGen D), ∀ a, truncate D k S (c a) = c a := by
  classical
  obtain ⟨S, hS⟩ := exists_truncate_fixed_finset D k (c.support.image c)
  refine ⟨S, fun a => ?_⟩
  by_cases ha : a ∈ c.support
  · exact hS S (fun _ h => h) (c a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  · rw [Finsupp.notMem_support_iff.mp ha, map_zero]

/-- Finite truncations jointly separate coefficients, including exterior products. -/
theorem truncations_separate {p q : SYM D k}
    (h : ∀ S : Finset (SYMGen D), truncate D k S p = truncate D k S q) : p = q := by
  classical
  obtain ⟨S, hS⟩ := exists_truncate_fixed D k p
  obtain ⟨T, hT⟩ := exists_truncate_fixed D k q
  simpa only [hS (S ∪ T) Finset.subset_union_left,
    hT (S ∪ T) Finset.subset_union_right] using h (S ∪ T)

/-- Some finite truncation detects every nonzero coefficient. -/
theorem exists_truncate_ne_zero {p : SYM D k} (hp : p ≠ 0) :
    ∃ S : Finset (SYMGen D), truncate D k S p ≠ 0 := by
  obtain ⟨S, hS⟩ := exists_truncate_fixed D k p
  exact ⟨S, by simpa only [hS S (fun _ h => h)] using hp⟩

end OddMath.SKM.SYM
