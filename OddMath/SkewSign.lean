import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation

/-!
# Increasing-index skew-monomial signs

For exponent vectors `a b : Fin n → ℕ`, multiplying the ordered words
`x₁^a₀ ⋯ xₙ^aₙ₋₁` and `x₁^b₀ ⋯ xₙ^bₙ₋₁` requires `a i * b j`
interchanges for each `j < i`. Distinct generators anticommute in EKL,
arXiv:1111.1320v1, §2.1.1, (2.1), p.3. The index order is locked by
the sign convention and the translation table.

This module proves the natural crossing-count cocycle and its integer sign
consequence. It does NOT construct the quotient algebra or prove a PBW theorem.
-/

namespace OddMath

/-- Number of out-of-order pairs between two increasing-index monomials.
Equal indices do not cross: in particular this imposes no exterior square law. -/
def crossingCount {n : ℕ} (a b : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j < i), a i * b j

/-- Integer coefficient assigned to normal-ordering the concatenation. -/
def skewSign {n : ℕ} (a b : Fin n → ℕ) : ℤ :=
  (-1 : ℤ) ^ crossingCount a b

/-- Additivity in the left exponent vector, with pointwise vector addition. -/
theorem crossingCount_add_left {n : ℕ} (a b c : Fin n → ℕ) :
    crossingCount (a + b) c = crossingCount a c + crossingCount b c := by
  simp only [crossingCount, Pi.add_apply, Nat.add_mul, Finset.sum_add_distrib]

/-- Additivity in the right exponent vector. -/
theorem crossingCount_add_right {n : ℕ} (a b c : Fin n → ℕ) :
    crossingCount a (b + c) = crossingCount a b + crossingCount a c := by
  simp only [crossingCount, Pi.add_apply, Nat.mul_add, Finset.sum_add_distrib]

/-- Universal natural-number cocycle, uniform in rank and all exponents. -/
theorem crossingCount_cocycle {n : ℕ} (a b c : Fin n → ℕ) :
    crossingCount a b + crossingCount (a + b) c =
      crossingCount b c + crossingCount a (b + c) := by
  rw [crossingCount_add_left, crossingCount_add_right]
  ac_rfl

/-- The corresponding integer sign identity: no truncation or parity hypothesis. -/
theorem skewSign_cocycle {n : ℕ} (a b c : Fin n → ℕ) :
    skewSign a b * skewSign (a + b) c =
      skewSign b c * skewSign a (b + c) := by
  simp only [skewSign, ← pow_add]
  rw [crossingCount_cocycle]

end OddMath
