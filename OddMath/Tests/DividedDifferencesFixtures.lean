import OddMath.DividedDifferences

/-! Rank-two odd divided-difference fixtures, hand-derived BEFORE implementation.

Source: Ellis-Khovanov-Lauda, arXiv:1111.1320v1, Section 2.1, eqs. (2.2)-(2.6),
pp.3-4 (ledger id `ekl-odd-nilhecke`; local text-layer copies
an unpublished note
and `ekl-page4.txt`). Convention authority: the sign convention
(increasing-index canonical order, Koszul reorder signs).

Machine-checkable values: an unpublished note
(17 `derivations` pairs for `d_1`, 6 `s1_action` pairs for `s_1`).
Each example below cites its JSON id. Proofs are filled after the module
exists; this file MUST fail to elaborate until then (TDD red step).
-/
namespace OddMath.DividedDifferences.Tests

open OddMath.DividedDifferences
open OddMath.SkewPolynomial (monomial generator)

/-- s1 on x2: EKL (2.2), generator image s1(x2) = -x1. JSON: s1 x2. -/
example : symm1 (monomial ![0, 1] 1) = monomial ![1, 0] (-1) := by
  rw [symm1_monomial, show swapExp ![0, 1] = ![1, 0] from by decide,
    show swapSign ![0, 1] = -1 from by decide, one_mul]

/-- s1 on x1: EKL (2.2), generator image s1(x1) = -x2. JSON: s1 x1. -/
example : symm1 (monomial ![1, 0] 1) = monomial ![0, 1] (-1) := by
  rw [symm1_monomial, show swapExp ![1, 0] = ![0, 1] from by decide,
    show swapSign ![1, 0] = -1 from by decide, one_mul]

/-- s1 on x1*x2: the naive-swap trap, s1(x1x2) = -x1x2 not +x1x2. JSON: s1 x1*x2. -/
example : symm1 (monomial ![1, 1] 1) = monomial ![1, 1] (-1) := by
  rw [symm1_monomial, show swapExp ![1, 1] = ![1, 1] from by decide,
    show swapSign ![1, 1] = -1 from by decide, one_mul]

/-- s1 on x1^2 = +x2^2. JSON: s1 x1^2. -/
example : symm1 (monomial ![2, 0] 1) = monomial ![0, 2] 1 := by
  rw [symm1_monomial, show swapExp ![2, 0] = ![0, 2] from by decide,
    show swapSign ![2, 0] = 1 from by decide, one_mul]

/-- s1 on x1^2*x2 = -x1x2^2. JSON: s1 x1^2*x2. -/
example : symm1 (monomial ![2, 1] 1) = monomial ![1, 2] (-1) := by
  rw [symm1_monomial, show swapExp ![2, 1] = ![1, 2] from by decide,
    show swapSign ![2, 1] = -1 from by decide, one_mul]

/-- s1 on x2^2 = +x1^2. JSON: s1 x2^2. -/
example : symm1 (monomial ![0, 2] 1) = monomial ![2, 0] 1 := by
  rw [symm1_monomial, show swapExp ![0, 2] = ![2, 0] from by decide,
    show swapSign ![0, 2] = 1 from by decide, one_mul]

/-- d1(1) = 0, EKL (2.3). JSON: dd-00. -/
example : divMonomial 0 0 = 0 := divMonomial_zero_zero

/-- d1(x1) = 1, EKL (2.3). JSON: dd-10. -/
example : divMonomial 1 0 = OddMath.SkewPolynomial.one := by
  rw [divMonomial_zero_right, powDiv1_one]

/-- d1(x2) = 1 (the oddity: NOT -1), EKL (2.3). JSON: dd-01. -/
example : divMonomial 0 1 = OddMath.SkewPolynomial.one := by
  rw [divMonomial_zero_left, powDiv2_one]

/-- d1(x1^2) = x1 - x2, EKL (2.6) m=2. JSON: dd-20. -/
example : divMonomial 2 0 = monomial ![1, 0] 1 - monomial ![0, 1] 1 := by
  rw [divMonomial_zero_right, powDiv1_two, generator_zero_monomial,
    generator_one_monomial]

/-- d1(x2^2) = x2 - x1, EKL (2.6) m=2. JSON: dd-02. -/
example : divMonomial 0 2 = monomial ![0, 1] 1 - monomial ![1, 0] 1 := by
  rw [divMonomial_zero_left, powDiv2_two, generator_zero_monomial,
    generator_one_monomial]

/-- d1(x1*x2) = 0, EKL (2.6). JSON: dd-11. -/
example : divMonomial 1 1 = 0 := divMonomial_one_one

/-- d1(x1^2*x2) = x1x2, EKL (2.4) Leibniz. JSON: dd-21. -/
example : divMonomial 2 1 = monomial ![1, 1] 1 := divMonomial_two_one

/-- d1(x1*x2^2) = -x1x2 (reorder sign), EKL (2.4). JSON: dd-12. -/
example : divMonomial 1 2 = -monomial ![1, 1] 1 := divMonomial_one_two

/-- d1(x1^2*x2^2) = 0, EKL (2.4). JSON: dd-22. -/
example : divMonomial 2 2 = 0 := divMonomial_two_two

/-- d1(x1^3) = x1^2 + x1x2 + x2^2, EKL (2.6) m=3. JSON: dd-30. -/
example : divMonomial 3 0
    = monomial ![2, 0] 1 + monomial ![1, 1] 1 + monomial ![0, 2] 1 :=
  divMonomial_three_zero

/-- d1(x2^3) = x2^2 - x1x2 + x1^2, EKL (2.6) m=3. JSON: dd-03. -/
example : divMonomial 0 3
    = monomial ![0, 2] 1 - monomial ![1, 1] 1 + monomial ![2, 0] 1 := by
  rw [divMonomial_zero_left, powDiv2_three, sub_eq_add_neg]

/-- d1(x1^3*x2) = x1^2x2 + x1x2^2, EKL (2.4). JSON: dd-31. -/
example : divMonomial 3 1 = monomial ![2, 1] 1 + monomial ![1, 2] 1 :=
  divMonomial_three_one

/-- d1(x1*x2^3) = -(x1^2x2 + x1x2^2), EKL (2.4). JSON: dd-13. -/
example : divMonomial 1 3 = -monomial ![2, 1] 1 - monomial ![1, 2] 1 :=
  divMonomial_one_three

/-- d1(x1^3*x2^2) = x1^2x2^2, EKL (2.4). JSON: dd-32. -/
example : divMonomial 3 2 = monomial ![2, 2] 1 := divMonomial_three_two

/-- d1(x1^2*x2^3) = x1^2x2^2, EKL (2.4). JSON: dd-23. -/
example : divMonomial 2 3 = monomial ![2, 2] 1 := divMonomial_two_three

/-- d1(x1^4) alternating sum, EKL (2.6) m=4. JSON: dd-40. -/
example : divMonomial 4 0 = monomial ![3, 0] 1 - monomial ![2, 1] 1
    + monomial ![1, 2] 1 - monomial ![0, 3] 1 := divMonomial_four_zero

/-- d1(x2^4) alternating sum, EKL (2.6) m=4. JSON: dd-04. -/
example : divMonomial 0 4 = monomial ![0, 3] 1 - monomial ![1, 2] 1
    + monomial ![2, 1] 1 - monomial ![3, 0] 1 := by
  rw [divMonomial_zero_left, powDiv2_four, sub_eq_add_neg, sub_eq_add_neg]

/-- Operator level: d1(x1) = 1. JSON: dd-10 via div1_generator_zero. -/
example : div1 (generator (0 : Fin 2)) = OddMath.SkewPolynomial.one :=
  div1_generator_zero

/-- Operator level: d1(x2) = 1. JSON: dd-01 via div1_generator_one. -/
example : div1 (generator (1 : Fin 2)) = OddMath.SkewPolynomial.one :=
  div1_generator_one

/-- Operator level: d1(1) = 0. JSON: dd-00 via div1_one. -/
example : div1 OddMath.SkewPolynomial.one = 0 := div1_one

/-- d1^2 = 0 spot check on x1^2 (EKL Prop 2.1 sample, hand grade). -/
example : div1 (div1 (monomial ![2, 0] 1)) = 0 := div1_sq_x1sq

/-- d1^2 = 0 spot check on x1*x2 (EKL Prop 2.1 sample, hand grade). -/
example : div1 (div1 (monomial ![1, 1] 1)) = 0 := div1_sq_x1x2

/-- d1^2 = 0 spot check on x1^3*x2^2 (EKL Prop 2.1 sample, hand grade). -/
example : div1 (div1 (monomial ![3, 2] 1)) = 0 := div1_sq_x1cube_x2sq

end OddMath.DividedDifferences.Tests
