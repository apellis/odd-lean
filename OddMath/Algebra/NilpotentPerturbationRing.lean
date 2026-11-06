/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Algebra.Basic

/-!
# Nilpotent perturbations of units in an algebra

The ring form of `OddMath.Algebra.isIso_add_of_mem_smul`. Let `R` be an algebra over a
commutative ring `k` and `J` an ideal of `k` with `J^N = 0`. Then every element of `J • R` is
nilpotent, and a unit perturbed by an element of `J • R` is a unit:
`u + n = u (1 + u⁻¹ n)`.

The application is to the parameters of Brundan–Wang–Webster (arXiv:2505.22929v2, §2.2):
`Qᵢⱼ(u, 0) = tᵢⱼ u^{dᵢⱼ} + Σ_{r<dᵢⱼ} cᵢⱼ(r, 0) u^r`, where the lower coefficients have
positive coefficient degree and so lie in a nilpotent ideal over a truncated Rees base.
`isUnit_smul_pow_add_sum` states that such a polynomial in a unit `u` is a unit.

* `mul_mem_pow_smul_top`: `(J^m • R) (J^n • R) ⊆ J^{m+n} • R`.
* `isNilpotent_of_mem_smul_top`: elements of `J • R` are nilpotent.
* `isUnit_add_of_mem_smul_top`: the perturbation statement.
* `sum_smul_mem_smul_top`: a combination with coefficients in `J` lies in `J • R`.
* `isUnit_smul_pow_add_sum`: `t u^d + Σ_{p<d} c_p u^p` is a unit for `t` a unit of `k`,
  `u` a unit of `R` and every `c_p ∈ J`.
-/

namespace OddMath.Algebra

variable {k : Type*} [CommRing k] {R : Type*} [Ring R] [Algebra k R]

/-- Multiplication multiplies the ideal levels of elements divisible by an ideal. -/
theorem mul_mem_pow_smul_top (J : Ideal k) {m n : ℕ} {a b : R}
    (ha : a ∈ (J ^ m) • (⊤ : Submodule k R)) (hb : b ∈ (J ^ n) • (⊤ : Submodule k R)) :
    a * b ∈ (J ^ (m + n)) • (⊤ : Submodule k R) := by
  refine Submodule.smul_induction_on ha ?_ ?_
  · intro r hr x _
    refine Submodule.smul_induction_on hb ?_ ?_
    · intro s hs y _
      rw [smul_mul_smul_comm, pow_add]
      exact Submodule.smul_mem_smul (Ideal.mul_mem_mul hr hs) Submodule.mem_top
    · intro y y' hy hy'
      rw [mul_add]
      exact Submodule.add_mem _ hy hy'
  · intro x x' hx hx'
    rw [add_mul]
    exact Submodule.add_mem _ hx hx'

/-- Every element lies in `J^0 • R`. -/
theorem mem_pow_zero_smul_top (J : Ideal k) (a : R) : a ∈ (J ^ 0) • (⊤ : Submodule k R) := by
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  exact Submodule.mem_top

/-- An element divisible by a nilpotent ideal of the base ring is nilpotent. -/
theorem isNilpotent_of_mem_smul_top (J : Ideal k) {N : ℕ} (hJ : J ^ N = ⊥) {a : R}
    (ha : a ∈ J • (⊤ : Submodule k R)) : IsNilpotent a := by
  have key : ∀ n : ℕ, a ^ n ∈ (J ^ n) • (⊤ : Submodule k R) := by
    intro n
    induction n with
    | zero => exact mem_pow_zero_smul_top J _
    | succ n ih =>
      rw [pow_succ a n]
      exact mul_mem_pow_smul_top J (n := 1) ih (by rwa [pow_one])
  refine ⟨N, ?_⟩
  have h := key N
  rw [hJ, Submodule.bot_smul] at h
  exact (Submodule.mem_bot k).mp h

/-- **Nilpotent perturbation of a unit.** A unit perturbed by an element divisible by a
nilpotent ideal of the base ring is a unit. -/
theorem isUnit_add_of_mem_smul_top (J : Ideal k) {N : ℕ} (hJ : J ^ N = ⊥) {u n : R}
    (hu : IsUnit u) (hn : n ∈ J • (⊤ : Submodule k R)) : IsUnit (u + n) := by
  obtain ⟨v, rfl⟩ := hu
  have h : ((v⁻¹ : Rˣ) : R) * n ∈ J • (⊤ : Submodule k R) := by
    have h₀ := mul_mem_pow_smul_top J (m := 0) (n := 1) (a := ((v⁻¹ : Rˣ) : R)) (b := n)
      (mem_pow_zero_smul_top J _) (by rwa [pow_one])
    rwa [zero_add, pow_one] at h₀
  have e : (v : R) + n = v * (1 + ((v⁻¹ : Rˣ) : R) * n) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  rw [e]
  exact v.isUnit.mul (isNilpotent_of_mem_smul_top J hJ h).isUnit_one_add

/-- A linear combination with coefficients in `J` lies in `J • R`. -/
theorem sum_smul_mem_smul_top (J : Ideal k) {ι : Type*} (s : Finset ι) (c : ι → k)
    (x : ι → R) (hc : ∀ p ∈ s, c p ∈ J) :
    ∑ p ∈ s, c p • x p ∈ J • (⊤ : Submodule k R) :=
  Submodule.sum_mem _ fun p hp => Submodule.smul_mem_smul (hc p hp) Submodule.mem_top

/-- The polynomial `t u^d + Σ_{p<d} c_p u^p` in a unit `u`, with `t` a unit of `k` and lower
coefficients in a nilpotent ideal, is a unit. This is `Qᵢⱼ(u, 0)` for parameters of
Brundan–Wang–Webster over a base where the pure coefficients are nilpotent. -/
theorem isUnit_smul_pow_add_sum (J : Ideal k) {N : ℕ} (hJ : J ^ N = ⊥) {u : R}
    (hu : IsUnit u) (t : kˣ) (d : ℕ) (c : ℕ → k) (hc : ∀ p < d, c p ∈ J) :
    IsUnit ((t : k) • u ^ d + ∑ p ∈ Finset.range d, c p • u ^ p) := by
  refine isUnit_add_of_mem_smul_top J hJ ?_
    (sum_smul_mem_smul_top J _ c _ fun p hp => hc p (Finset.mem_range.mp hp))
  rw [Algebra.smul_def]
  exact (t.isUnit.map (algebraMap k R)).mul (hu.pow d)

end OddMath.Algebra
