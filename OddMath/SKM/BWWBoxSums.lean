/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Box sums of Brundan–Wang–Webster coefficients

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2: the polynomial
`Qᵢⱼ(u, v) = Σ_{p ≤ dᵢⱼ, q ≤ dⱼᵢ} cᵢⱼ(p, q) u^p v^q`, compared with the Brundan–Ellis shape
of arXiv:1701.04133v2, (1.3), in which every monomial other than the two corners has
`p > 0` and `q > 0`.

The relation-level consequences of the quadratic relation for distinct colours (the bubble
slides of Brundan–Ellis, Proposition 7.3(iii), (7.11)–(7.12)) are sums over the box of the
coefficients `c p q` against a family `f p q` of morphisms, where `f p q` carries `q` dots on
the second strand. This file records the coefficient-level identities that are used when the
Brundan–Ellis monomials are replaced by an arbitrary coefficient function on the box.

* `boxSum c a b f`: the sum `Σ_{p ≤ a, q ≤ b} c p q • f p q`.
* `boxSum_eq_row_add`: the box sum is its row `q = 0` plus the part with `q > 0`.
* `boxSum_sub_row_mem`: if every `f p q` with `q > 0` lies in a submodule `P` (for instance
  the morphisms with at least one dot on the second strand), the box sum is its row `q = 0`
  modulo `P`.
* `row_eq_corner_add_pure`: if `c a q = 0` for `q > 0`, the row is the corner term
  `c a 0 • f a 0` plus the pure terms `c r 0 • f r 0` with `r < a`.
* `boxSum_sub_corner_mem`: when the pure terms vanish (Brundan–Ellis parameters), the box sum
  is the corner term modulo `P`. With pure terms the corner term must be replaced by the
  whole row (`boxSum_sub_corner_sub_pure_mem`).
-/

namespace OddMath.SKM.BWWBox

open Finset

variable {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]

/-- The box sum `Σ_{p ≤ a, q ≤ b} c p q • f p q`. -/
def boxSum (c : ℕ → ℕ → k) (a b : ℕ) (f : ℕ → ℕ → M) : M :=
  ∑ p ∈ range (a + 1), ∑ q ∈ range (b + 1), c p q • f p q

/-- The row `q = 0` of a box sum: `Σ_{p ≤ a} c p 0 • f p 0`. -/
def row (c : ℕ → ℕ → k) (a : ℕ) (f : ℕ → ℕ → M) : M :=
  ∑ p ∈ range (a + 1), c p 0 • f p 0

/-- The part of a box sum with `q > 0`. -/
def upper (c : ℕ → ℕ → k) (a b : ℕ) (f : ℕ → ℕ → M) : M :=
  ∑ p ∈ range (a + 1), ∑ q ∈ Ioc 0 b, c p q • f p q

theorem sum_range_succ_eq_zero_add_Ioc {N : Type*} [AddCommMonoid N] (b : ℕ) (g : ℕ → N) :
    ∑ q ∈ range (b + 1), g q = g 0 + ∑ q ∈ Ioc 0 b, g q := by
  have h : Ioc 0 b = Ico 1 (b + 1) := by ext q; simp only [mem_Ioc, mem_Ico]; omega
  rw [h, range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos b)]

theorem boxSum_eq_row_add (c : ℕ → ℕ → k) (a b : ℕ) (f : ℕ → ℕ → M) :
    boxSum c a b f = row c a f + upper c a b f := by
  simp only [boxSum, row, upper, sum_range_succ_eq_zero_add_Ioc b, sum_add_distrib]

/-- Modulo a submodule containing every `f p q` with `q > 0`, a box sum is its row `q = 0`. -/
theorem boxSum_sub_row_mem (c : ℕ → ℕ → k) (a b : ℕ) (f : ℕ → ℕ → M) (P : Submodule k M)
    (hP : ∀ p q, 0 < q → f p q ∈ P) : boxSum c a b f - row c a f ∈ P := by
  rw [boxSum_eq_row_add, add_sub_cancel_left]
  exact sum_mem fun p _ => sum_mem fun q hq =>
    Submodule.smul_mem _ _ (hP p q (Finset.mem_Ioc.mp hq).1)

/-- The row `q = 0` is the corner term plus the pure terms `c r 0 • f r 0`, `r < a`. -/
theorem row_eq_corner_add_pure (c : ℕ → ℕ → k) (a : ℕ) (f : ℕ → ℕ → M) :
    row c a f = c a 0 • f a 0 + ∑ r ∈ range a, c r 0 • f r 0 := by
  rw [row, sum_range_succ, add_comm]

/-- If the pure terms `c r 0`, `r < a`, vanish (as for Brundan–Ellis parameters), the row is
the corner term. -/
theorem row_eq_corner (c : ℕ → ℕ → k) (a : ℕ) (f : ℕ → ℕ → M)
    (hc : ∀ r < a, c r 0 = 0) : row c a f = c a 0 • f a 0 := by
  rw [row_eq_corner_add_pure, sum_eq_zero fun r hr => by
    rw [hc r (Finset.mem_range.mp hr), zero_smul], add_zero]

/-- Modulo `P`, a box sum is its corner term plus its pure terms in the first variable. -/
theorem boxSum_sub_corner_sub_pure_mem (c : ℕ → ℕ → k) (a b : ℕ) (f : ℕ → ℕ → M)
    (P : Submodule k M) (hP : ∀ p q, 0 < q → f p q ∈ P) :
    boxSum c a b f - c a 0 • f a 0 - ∑ r ∈ range a, c r 0 • f r 0 ∈ P := by
  have h := boxSum_sub_row_mem c a b f P hP
  rwa [row_eq_corner_add_pure, ← sub_sub] at h

/-- Without pure terms in the first variable, a box sum is its corner term modulo `P`. -/
theorem boxSum_sub_corner_mem (c : ℕ → ℕ → k) (a b : ℕ) (f : ℕ → ℕ → M) (P : Submodule k M)
    (hP : ∀ p q, 0 < q → f p q ∈ P) (hc : ∀ r < a, c r 0 = 0) :
    boxSum c a b f - c a 0 • f a 0 ∈ P := by
  have h := boxSum_sub_row_mem c a b f P hP
  rwa [row_eq_corner c a f hc] at h

/-- The corner term alone is not correct modulo `P` when a pure term is present: the family
`f p q = δ_{p r} δ_{q 0} • x` with `r < a` vanishes at the corner `(a, 0)`, and its box sum is
`c r 0 • x`. -/
theorem boxSum_single_pure (c : ℕ → ℕ → k) {a r : ℕ} (b : ℕ) (hr : r < a) (x : M) :
    boxSum c a b (fun p q => if p = r ∧ q = 0 then x else 0) = c r 0 • x := by
  rw [boxSum, Finset.sum_eq_single r]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro q _ hq; simp [hq]
    · intro h; simp at h
  · intro p _ hp
    exact Finset.sum_eq_zero fun q _ => by simp [hp]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

end OddMath.SKM.BWWBox
