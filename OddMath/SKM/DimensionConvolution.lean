/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.LaurentSeries

/-!
# Laurent-series convolution for BE2 (dum)

This module proves the finite coefficient convolution used in Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 12.1,
equation (dum). A degree-enumerating Laurent series multiplied by a series
supported in nonnegative degrees has coefficients given by finite sums over
bounded-degree labels. No positivity assumption on the label weights is needed.
-/

noncomputable section

namespace OddMath.SKM

open scoped BigOperators

/-- Multiplication by a series supported in nonnegative degrees preserves
agreement of coefficients through a fixed degree. -/
theorem laurentSeries_mul_coeff_congr (f f' g : LaurentSeries ℚ) (n : ℤ)
    (hf : ∀ k ≤ n, f.coeff k = f'.coeff k)
    (hg : ∀ k < 0, g.coeff k = 0) :
    (f * g).coeff n = (f' * g).coeff n := by
  have hz : ((f - f') * g).coeff n = 0 := by
    rw [HahnSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have hmem := Finset.mem_antidiagonal.mp hij
    have hnonneg : 0 ≤ ij.2 := by
      by_contra h
      exact hmem.2.1 (hg ij.2 (lt_of_not_ge h))
    have hle : ij.1 ≤ n := by omega
    rw [HahnSeries.coeff_sub, hf ij.1 hle, sub_self, zero_mul]
  simpa only [sub_mul, HahnSeries.coeff_sub, sub_eq_zero] using hz

/-- The coefficient of a product is a finite sum over labels whose degree is
at most the requested degree. The coefficients of `f` enumerate the degree
fibers with arbitrary rational weights, and `g` vanishes in negative degrees.
Since `f` is already a Laurent series, no separate lower-bound hypothesis is
needed here. -/
theorem laurentSeries_coeff_mul_eq_sum_bounded {α : Type*}
    (d : α → ℤ) (w : α → ℚ)
    (hfinite : ∀ n : ℤ, Set.Finite {a | d a ≤ n})
    (f g : LaurentSeries ℚ)
    (hf : ∀ n : ℤ, f.coeff n =
      ∑ a ∈ ((hfinite n).subset (show {a | d a = n} ⊆ {a | d a ≤ n} from
        fun _ h => h.le)).toFinset, w a)
    (hg : ∀ k < 0, g.coeff k = 0) (n : ℤ) :
    (f * g).coeff n =
      ∑ a ∈ (hfinite n).toFinset, w a * g.coeff (n - d a) := by
  classical
  let t : LaurentSeries ℚ :=
    ∑ a ∈ (hfinite n).toFinset, HahnSeries.single (d a) (w a)
  have ht : ∀ k ≤ n, f.coeff k = t.coeff k := by
    intro k hk
    rw [hf k]
    change _ = (∑ a ∈ (hfinite n).toFinset,
      HahnSeries.single (d a) (w a) : LaurentSeries ℚ).coeff k
    rw [HahnSeries.coeff_sum]
    calc
      _ = ∑ a ∈ ((hfinite k).subset (show {a | d a = k} ⊆ {a | d a ≤ k} from
          fun _ h => h.le)).toFinset,
          (HahnSeries.single (d a) (w a) : LaurentSeries ℚ).coeff k := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha' : d a = k := by simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using ha
        simp [ha']
      _ = _ := by
        apply Finset.sum_subset
        · intro a ha
          have ha' : d a = k := by simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using ha
          simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ha'] using hk
        · intro a _ ha
          have ha' : k ≠ d a := by
            intro heq
            apply ha
            simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using heq.symm
          exact HahnSeries.coeff_single_of_ne ha'
  rw [laurentSeries_mul_coeff_congr f t g n ht hg]
  simp only [t, Finset.sum_mul, HahnSeries.coeff_sum, HahnSeries.coeff_single_mul]

end OddMath.SKM
