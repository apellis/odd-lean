/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.CoupledBubbleEvaluation

/-! # Triangular recovery of reservoir bubble coefficients

Algebraic part of C1 in `docs/Nondegeneracy/GeneralRoute.md`. A categorical
bubble convolution is still a hypothesis. The inverse is finite in every
coefficient, works over rings with zero divisors, and does not assert that a
substitution preserves a finite cyclotomic ideal. Apply it separately to each
colour's even series; all odd coefficients must remain in the same reservoir.
-/
namespace OddMath.SKM

/-- Ordered multiplication of coefficient series. -/
def reservoirConvolution {R : Type*} [Ring R] (A P : ℕ → R) (n : ℕ) : R :=
  ∑ r ∈ Finset.range (n + 1), A (n - r) * P r

/-- Recover one coefficient at a time by subtracting the already known lower
coefficients. No infinite sum and no division by an exterior element is used. -/
def reservoirDeconvolution {R : Type*} [Ring R] (C P : ℕ → R) (n : ℕ) : R :=
  C n - ∑ r : Fin n, reservoirDeconvolution C P (n - (r.val + 1)) * P (r.val + 1)
termination_by n
decreasing_by have := r.isLt; omega

end OddMath.SKM
