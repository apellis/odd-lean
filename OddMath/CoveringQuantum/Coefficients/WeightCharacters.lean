import OddMath.CoveringQuantum.Coefficients.Splitting

/-!
# Parity characters over the covering ring

The functions `n ↦ 1` and `n ↦ πⁿ` are not linearly independent over
`ℚ(q)[π]/(π² - 1)`. In particular, vanishing of all integral-weight
character evaluations is not a coefficient-separation criterion over this ring.
For negative integers, the parity character is written `π ^ n.natAbs`,
which agrees with the negative power because `π² = 1`.
-/

noncomputable section
namespace OddMath.CoveringQuantum.Coefficients

/-- The coefficient in the two-term character relation is nonzero. -/
theorem one_add_pi_ne_zero : (1 + pi : Ring) ≠ 0 := by
  intro h
  have hh := congrArg (specialize 1 (one_pow 2)) h
  norm_num at hh

/-- A nonzero multiple of every parity character is constant. -/
theorem one_add_pi_mul_pow (n : ℕ) : (1 + pi) * pi ^ n = (1 + pi : Ring) := by
  have h : (1 + pi) * pi = (1 + pi : Ring) := by
    linear_combination pi_sq
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, h]

/-- Integral-weight parity evaluations do not separate coefficients over the
covering ring. This does not contradict a triangular decomposition theorem. -/
theorem parity_characters_not_separating :
    ¬ (∀ a b : Ring, (∀ n : ℤ, a * pi ^ n.natAbs + b = 0) → a = 0 ∧ b = 0) := by
  intro h
  have h' := h (1 + pi) (-(1 + pi)) (fun n ↦ by rw [one_add_pi_mul_pow]; simp)
  exact one_add_pi_ne_zero h'.1

end OddMath.CoveringQuantum.Coefficients
