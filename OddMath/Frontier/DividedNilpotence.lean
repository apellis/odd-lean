import OddMath.Frontier.TwistedLeibniz

/-!
# Square-zero rank-two odd divided difference

EKL, arXiv:1111.1320v1, Proposition 2.1, (2.7), p.4: the degree-induction
proof from (2.3)–(2.8). Here exponent induction on the actual normal-ordered
monomials implements that argument, followed by integer linear extension.
No signed-swap multiplicativity or D/s anticommutation premise is required.
-/
namespace OddMath.Frontier.DividedNilpotence

open OddMath.SkewPolynomial OddMath.DividedDifferences
open OddMath.Frontier.TwistedLeibniz

/-- The two subtraction terms cancel on every input, not just monomials. -/
lemma square_x_mul (f : P) : D (D (x * f)) = x * D (D f) := by
  rw [div1_x_mul, map_sub, div1_y_mul]
  abel

/-- The companion cancellation has the same positive final sign. -/
lemma square_y_mul (f : P) : D (D (y * f)) = y * D (D f) := by
  rw [div1_y_mul, map_sub, div1_x_mul]
  abel

/-- Arbitrary pure y exponent; the unit, not a generator sample, is the base. -/
lemma square_M_zero (b : ℕ) : D (D (M 0 b)) = 0 := by
  induction b with
  | zero =>
      rw [M_zero]
      change div1 (div1 one) = 0
      rw [div1_one, div1_zero]
  | succ b ih =>
      have hM : M 0 (b + 1) = y * M 0 b := by simp [y_mono]
      rw [hM, square_y_mul, ih]
      simp

/-- Both exponents are universally quantified and unbounded. -/
lemma square_M (a b : ℕ) : D (D (M a b)) = 0 := by
  induction a with
  | zero => exact square_M_zero b
  | succ a ih =>
      rw [show M (a + 1) b = x * M a b from (x_mono a b 1).symm,
        square_x_mul, ih]
      simp

/-- EKL (2.7), on the inherited finite-support integer skew-polynomial model. -/
theorem div1_square_zero (f : SkewPolynomial 2) : div1 (div1 f) = 0 := by
  change D (D f) = 0
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single e r =>
      have he : e = ![e 0, e 1] := by ext i; fin_cases i <;> rfl
      rw [he]
      change D (D (monomial _ r)) = 0
      rw [mono_smul, map_zsmul, map_zsmul, square_M, smul_zero]

end OddMath.Frontier.DividedNilpotence
