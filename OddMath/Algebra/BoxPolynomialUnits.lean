/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.Algebra.NilpotentPerturbationRing

/-!
# Box polynomials with a unit leading term

A polynomial `Q(u, v) = Σ_{p ≤ d, q ≤ d'} c(p, q) u^p v^q` in two elements of an algebra `R`
over `k` splits as `Q(u, 0)` plus a multiple of `v`:

    Q(u, v) = (c(d, 0) u^d + Σ_{p<d} c(p, 0) u^p) + R v.

This is the shape of `Qᵢⱼ` for the parameters of Brundan–Wang–Webster (arXiv:2505.22929v2,
§2.2), with `d = dᵢⱼ`, `d' = dⱼᵢ`, corner coefficient `c(d, 0) = tᵢⱼ` a unit and pure terms
`c(p, 0)`, `p < d`, of positive coefficient degree. If the pure coefficients lie in a nilpotent
ideal and `u` is a unit, the first summand is a unit (`isUnit_smul_pow_add_sum`). The two
remainder forms `U + R v` and `U + v R'` are those consumed by the distinct-colour mixed
crossing arguments; the left form uses a signed slide `u^p v = ε^p (v u^p)`.

No order or commutation of `u`, `v` is assumed except in the left form.

* `sum_box_split`: the splitting of the box sum, for coefficients in any module.
* `sum_box_eq_add_mul`, `sum_box_eq_add_mul_left`: the right and left remainders.
* `exists_isUnit_box_remainders`: `Q(u, v) = U + R v = U + v R'` with `U` a unit.
-/

namespace OddMath.Algebra

open Finset

variable {k : Type*} [CommRing k]

/-- The box sum splits into its `q = 0` row and the rows with `q ≥ 1`, with the corner
`(d, 0)` separated. -/
theorem sum_box_split {M : Type*} [AddCommMonoid M] [Module k M] (c : ℕ → ℕ → k) (d d' : ℕ)
    (f : ℕ → ℕ → M) :
    ∑ p ∈ range (d + 1), ∑ q ∈ range (d' + 1), c p q • f p q =
      (c d 0 • f d 0 + ∑ p ∈ range d, c p 0 • f p 0) +
        ∑ p ∈ range (d + 1), ∑ q ∈ range d', c p (q + 1) • f p (q + 1) := by
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_range_succ' (fun q => c p q • f p q) d',
    Finset.sum_add_distrib, Finset.sum_range_succ (fun p => c p 0 • f p 0) d, add_comm,
    add_comm (∑ p ∈ range d, c p 0 • f p 0)]

variable {R : Type*} [Ring R] [Algebra k R]

/-- The right remainder: `Q(u, v) = Q(u, 0) + R v`. -/
theorem sum_box_eq_add_mul (c : ℕ → ℕ → k) (d d' : ℕ) (u v : R) :
    ∑ p ∈ range (d + 1), ∑ q ∈ range (d' + 1), c p q • (u ^ p * v ^ q) =
      (c d 0 • u ^ d + ∑ p ∈ range d, c p 0 • u ^ p) +
        (∑ p ∈ range (d + 1), ∑ q ∈ range d', c p (q + 1) • (u ^ p * v ^ q)) * v := by
  rw [sum_box_split c d d' fun p q => u ^ p * v ^ q]
  simp only [pow_zero, mul_one, Finset.sum_mul, smul_mul_assoc, mul_assoc, ← pow_succ]

/-- The left remainder: `Q(u, v) = Q(u, 0) + v R'`, when `u^p v = ε^p (v u^p)`. -/
theorem sum_box_eq_add_mul_left (c : ℕ → ℕ → k) (d d' : ℕ) {u v : R} (ε : k)
    (hslide : ∀ p : ℕ, u ^ p * v = ε ^ p • (v * u ^ p)) :
    ∑ p ∈ range (d + 1), ∑ q ∈ range (d' + 1), c p q • (u ^ p * v ^ q) =
      (c d 0 • u ^ d + ∑ p ∈ range d, c p 0 • u ^ p) +
        v * ∑ p ∈ range (d + 1), ∑ q ∈ range d', (c p (q + 1) * ε ^ p) • (u ^ p * v ^ q) := by
  rw [sum_box_split c d d' fun p q => u ^ p * v ^ q]
  simp only [pow_zero, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [pow_succ', ← mul_assoc, hslide p, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]

/-- **The two remainder forms with a unit leading part.** If `u` is a unit, the corner
coefficient `c(d, 0)` is a unit and the pure coefficients `c(p, 0)`, `p < d`, lie in a
nilpotent ideal, then `Q(u, v) = U + R v = U + v R'` with `U` a unit. -/
theorem exists_isUnit_box_remainders (J : Ideal k) {N : ℕ} (hJ : J ^ N = ⊥)
    (c : ℕ → ℕ → k) (d d' : ℕ) (t : kˣ) (ht : c d 0 = t) (hc : ∀ p < d, c p 0 ∈ J)
    {u v : R} (hu : IsUnit u) (ε : k) (hslide : ∀ p : ℕ, u ^ p * v = ε ^ p • (v * u ^ p)) :
    ∃ U Rr Rl : R, IsUnit U ∧
      ∑ p ∈ range (d + 1), ∑ q ∈ range (d' + 1), c p q • (u ^ p * v ^ q) = U + Rr * v ∧
      ∑ p ∈ range (d + 1), ∑ q ∈ range (d' + 1), c p q • (u ^ p * v ^ q) = U + v * Rl := by
  refine ⟨_, _, _, ?_, sum_box_eq_add_mul c d d' u v, sum_box_eq_add_mul_left c d d' ε hslide⟩
  rw [ht]
  exact isUnit_smul_pow_add_sum J hJ hu t d (fun p => c p 0) hc

end OddMath.Algebra
