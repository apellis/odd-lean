import OddMath.SkewSign

/-! Hand-derived tests for the locked increasing-index convention.
These are exact small checks, not the universal proof. -/
namespace OddMath.Tests

-- Rank zero has no crossings.
example (a b : Fin 0 → ℕ) : crossingCount a b = 0 := by
  simp [crossingCount]

-- At rank one even a repeated odd generator has no crossing.
example : crossingCount (fun _ : Fin 1 => 1) (fun _ => 1) = 0 := by decide
example : skewSign (fun _ : Fin 1 => 1) (fun _ => 1) = 1 := by decide

-- Fin index 0 is source x₁; Fin index 1 is source x₂.
-- e₁ followed by e₀ crosses once; the reverse crosses zero times.
example : crossingCount (![0, 1] : Fin 2 → ℕ) ![1, 0] = 1 := by decide
example : skewSign (![0, 1] : Fin 2 → ℕ) ![1, 0] = -1 := by decide
example : crossingCount (![1, 0] : Fin 2 → ℕ) ![0, 1] = 0 := by decide
example : skewSign (![1, 0] : Fin 2 → ℕ) ![0, 1] = 1 := by decide

-- Degree four input, four crossings (2 * 2): x₂² x₁² contributes +1.
example : crossingCount (![0, 2] : Fin 2 → ℕ) ![2, 0] = 4 := by decide
example : skewSign (![0, 2] : Fin 2 → ℕ) ![2, 0] = 1 := by decide

end OddMath.Tests
