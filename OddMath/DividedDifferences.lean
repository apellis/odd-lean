import OddMath.SkewPolynomial
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Rank-two odd divided differences on the skew-polynomial model

Source: Ellis-Khovanov-Lauda, arXiv:1111.1320v1, Section 2.1, eqs. (2.2)-(2.6),
pp.3-4 (ledger id `ekl-odd-nilhecke`; local text-layer copies
an unpublished note
and `ekl-page4.txt`). Convention authority: the sign convention
(increasing-index canonical order, Koszul reorder signs) and
the translation table.

Definitions, EKL (2.2)-(2.4):
* `symm1`: the signed transposition `s_1` on `OPol_2`, a linear extension from
  monomials with `s_1(x_1^a x_2^b) = (-1)^(a+b+ab) x_1^b x_2^a`. In particular
  `s_1(x_1) = -x_2`, `s_1(x_2) = -x_1` (NOT the naive swap).
* `powDiv1 m = d_1(x_1^m)`, `powDiv2 m = d_1(x_2^m)`: the closed power sums
  EKL (2.6), written directly in canonical coordinates.
* `divMonomial a b = d_1(x_1^a x_2^b)`: EKL (2.4) Leibniz form
  `D(a) x_2^b + s_1(x_1^a) D'(b)`, with products in `SkewPolynomial.mul`.
* `div1`: linear extension of `divMonomial` to all of `SkewPolynomial 2`.

Proved: generator images of `s_1`/`d_1`, involution of `s_1` on monomials,
closed power values through degree 4, the full 17-entry rank-two action table
(as `divMonomial_*` theorems matching `derivations.json`), the Leibniz rule on
the three generator pairs, and `d_1^2 = 0` on three samples (EKL Prop. 2.1
spot checks, hand grade only).

This is ONLY the rank-two operator calculus on the finite-support integer
model. It is not a quotient presentation, not a PBW theorem, not the general
Leibniz rule (stated only on generator pairs; the universal monomial Leibniz
identity is the documented next predicate), and not the nilHecke relations
`d_i^2 = 0` / braid / dot-slide in general.
-/

namespace OddMath.DividedDifferences

open OddMath.SkewPolynomial

/-- The nontrivial transposition of `Fin 2`, as a closed function. -/
def swapFin : Fin 2 → Fin 2 := ![1, 0]

/-- Swap the two entries of a rank-two exponent vector. -/
def swapExp (e : Fin 2 → ℕ) : Fin 2 → ℕ := e ∘ swapFin

/-- Signed-swap sign: `s_1(x_1^a x_2^b) = (-1)^(a+b+ab) x_1^b x_2^a`.
EKL (2.2), p.3: `s_1` is the tensor product of the permutation representation
with the degree-tensor-power of the sign representation. -/
def swapSign (e : Fin 2 → ℕ) : ℤ := (-1 : ℤ) ^ (e 0 + e 1 + e 0 * e 1)

/-- Rank-two signed transposition, linear extension from monomials. EKL (2.2). -/
noncomputable def symm1 (f : SkewPolynomial 2) : SkewPolynomial 2 :=
  f.sum fun e r => monomial (swapExp e) (r * swapSign e)

/-- `d_1(x_1^m)` in canonical coordinates:
`Σ_{i<m} (-1)^(i*(m-i)) x_1^(m-1-i) x_2^i`. EKL (2.6), p.4, re-sorted from the
word order `x_2^i x_1^(m-1-i)` with the Koszul sign `(-1)^(i*(m-1-i))`. -/
noncomputable def powDiv1 (m : ℕ) : SkewPolynomial 2 :=
  ∑ i ∈ Finset.range m, monomial ![m - 1 - i, i] ((-1 : ℤ) ^ (i * (m - i)))

/-- `d_1(x_2^m) = Σ_{k<m} (-1)^k x_1^k x_2^(m-1-k)`, already canonical.
EKL (2.6), p.4. -/
noncomputable def powDiv2 (m : ℕ) : SkewPolynomial 2 :=
  ∑ k ∈ Finset.range m, monomial ![k, m - 1 - k] ((-1 : ℤ) ^ k)

/-- `d_1(x_1^a x_2^b) = D(a) x_2^b + s_1(x_1^a) D'(b)` with
`s_1(x_1^a) = (-1)^a x_2^a`. EKL (2.4) Leibniz from the (2.6) power values. -/
noncomputable def divMonomial (a b : ℕ) : SkewPolynomial 2 :=
  mul (powDiv1 a) (monomial ![0, b] 1)
    + mul (monomial ![0, a] ((-1 : ℤ) ^ a)) (powDiv2 b)

/-- `d_1` linearly extended to all of `SkewPolynomial 2`. EKL (2.3)-(2.4). -/
noncomputable def div1 (f : SkewPolynomial 2) : SkewPolynomial 2 :=
  f.sum fun e r => r • divMonomial (e 0) (e 1)

/-! ## The swap involution, funext-free -/

theorem swapFin_involute : swapFin ∘ swapFin = id := by decide

theorem swapExp_apply_zero (e : Fin 2 → ℕ) : swapExp e 0 = e 1 := by
  show e (swapFin 0) = e 1
  rw [show swapFin (0 : Fin 2) = 1 from by decide]

theorem swapExp_apply_one (e : Fin 2 → ℕ) : swapExp e 1 = e 0 := by
  show e (swapFin 1) = e 0
  rw [show swapFin (1 : Fin 2) = 0 from by decide]

theorem swapExp_swapExp (e : Fin 2 → ℕ) : swapExp (swapExp e) = e := by
  show (e ∘ swapFin) ∘ swapFin = e
  rw [Function.comp_assoc, swapFin_involute, Function.comp_id]

theorem swapSign_swapExp (e : Fin 2 → ℕ) :
    swapSign (swapExp e) = swapSign e := by
  show (-1 : ℤ) ^ (swapExp e 0 + swapExp e 1 + swapExp e 0 * swapExp e 1)
    = (-1 : ℤ) ^ (e 0 + e 1 + e 0 * e 1)
  rw [swapExp_apply_zero, swapExp_apply_one, mul_comm (e 1) (e 0),
    add_comm (e 1) (e 0)]

theorem swapSign_mul_self (e : Fin 2 → ℕ) : swapSign e * swapSign e = 1 := by
  simp only [swapSign, ← mul_pow]
  rw [show (-1 : ℤ) * -1 = 1 from by decide, one_pow]

/-! ## Linearity scaffolding for `symm1` -/

theorem symmMonomial_zero (e : Fin 2 → ℕ) :
    monomial (swapExp e) ((0 : ℤ) * swapSign e) = 0 := by
  simp [monomial, Finsupp.single_zero]

theorem symmMonomial_add (e : Fin 2 → ℕ) (r₁ r₂ : ℤ) :
    monomial (swapExp e) ((r₁ + r₂) * swapSign e)
      = monomial (swapExp e) (r₁ * swapSign e)
        + monomial (swapExp e) (r₂ * swapSign e) := by
  have h : (r₁ + r₂) * swapSign e
      = r₁ * swapSign e + r₂ * swapSign e := by
    rw [_root_.add_mul]
  rw [h]
  exact Finsupp.single_add _ _ _

theorem symm1_monomial (e : Fin 2 → ℕ) (r : ℤ) :
    symm1 (monomial e r) = monomial (swapExp e) (r * swapSign e) := by
  show (monomial e r).sum
        (fun e' r' => monomial (swapExp e') (r' * swapSign e'))
      = monomial (swapExp e) (r * swapSign e)
  show (Finsupp.single e r).sum
        (fun e' r' => monomial (swapExp e') (r' * swapSign e'))
      = monomial (swapExp e) (r * swapSign e)
  rw [Finsupp.sum_single_index (symmMonomial_zero e)]

theorem symm1_zero : symm1 0 = 0 := by
  show (0 : SkewPolynomial 2).sum
      (fun e r => monomial (swapExp e) (r * swapSign e)) = 0
  exact Finsupp.sum_zero_index

theorem symm1_add (f₁ f₂ : SkewPolynomial 2) :
    symm1 (f₁ + f₂) = symm1 f₁ + symm1 f₂ := by
  show (f₁ + f₂).sum (fun e r => monomial (swapExp e) (r * swapSign e))
    = f₁.sum (fun e r => monomial (swapExp e) (r * swapSign e))
      + f₂.sum (fun e r => monomial (swapExp e) (r * swapSign e))
  exact Finsupp.sum_add_index' (fun e => symmMonomial_zero e)
    (fun e r₁ r₂ => symmMonomial_add e r₁ r₂)

/-! ## Generator images and involution -/

/-- EKL (2.2): `s_1(x_1) = -x_2`. -/
theorem symm1_generator_zero :
    symm1 (generator (0 : Fin 2)) = -generator 1 := by
  show symm1 (monomial (expSingle 0) 1) = -(monomial (expSingle 1) 1)
  rw [symm1_monomial,
    show swapExp (expSingle (0 : Fin 2)) = expSingle 1 from by decide,
    show swapSign (expSingle (0 : Fin 2)) = -1 from by decide,
    _root_.one_mul, monomial_neg]

/-- EKL (2.2): `s_1(x_2) = -x_1`. -/
theorem symm1_generator_one :
    symm1 (generator (1 : Fin 2)) = -generator 0 := by
  show symm1 (monomial (expSingle 1) 1) = -(monomial (expSingle 0) 1)
  rw [symm1_monomial,
    show swapExp (expSingle (1 : Fin 2)) = expSingle 0 from by decide,
    show swapSign (expSingle (1 : Fin 2)) = -1 from by decide,
    _root_.one_mul, monomial_neg]

theorem symm1_one : symm1 one = one := by
  show symm1 (monomial (0 : Fin 2 → ℕ) 1) = monomial (0 : Fin 2 → ℕ) 1
  rw [symm1_monomial,
    show swapExp (0 : Fin 2 → ℕ) = 0 from by decide,
    show swapSign (0 : Fin 2 → ℕ) = 1 from by decide, _root_.mul_one]

/-- `s_1` is involutive on monomials (sign squares to one). -/
theorem symm1_involute_monomial (e : Fin 2 → ℕ) (r : ℤ) :
    symm1 (symm1 (monomial e r)) = monomial e r := by
  rw [symm1_monomial, symm1_monomial, swapExp_swapExp, swapSign_swapExp,
    _root_.mul_assoc, swapSign_mul_self, _root_.mul_one]

/-! ## Subtraction through the skew product -/

theorem mul_neg (f g : SkewPolynomial 2) : mul f (-g) = -mul f g := by
  have h : mul f (-g) + mul f g = 0 := by
    rw [← mul_add, neg_add_cancel, mul_zero]
  exact eq_neg_of_add_eq_zero_left h

theorem neg_mul (f g : SkewPolynomial 2) : mul (-f) g = -mul f g := by
  have h : mul (-f) g + mul f g = 0 := by
    rw [← add_mul, neg_add_cancel, zero_mul]
  exact eq_neg_of_add_eq_zero_left h

theorem mul_sub (f g₁ g₂ : SkewPolynomial 2) :
    mul f (g₁ - g₂) = mul f g₁ - mul f g₂ := by
  rw [sub_eq_add_neg, mul_add, mul_neg, sub_eq_add_neg]

theorem sub_mul (f₁ f₂ g : SkewPolynomial 2) :
    mul (f₁ - f₂) g = mul f₁ g - mul f₂ g := by
  rw [sub_eq_add_neg, add_mul, neg_mul, sub_eq_add_neg]

/-! ## Closed power values -/

theorem powDiv1_zero : powDiv1 0 = 0 := by
  simp only [powDiv1, Finset.sum_range_zero]

theorem powDiv2_zero : powDiv2 0 = 0 := by
  simp only [powDiv2, Finset.sum_range_zero]

theorem powDiv1_one : powDiv1 1 = one := by
  simp only [powDiv1, Finset.sum_range_one]
  rw [show ![1 - 1 - 0, 0] = (0 : Fin 2 → ℕ) from by decide,
    show (-1 : ℤ) ^ (0 * (1 - 0)) = 1 from by decide,
    show (monomial (0 : Fin 2 → ℕ) 1) = one from rfl]

theorem powDiv2_one : powDiv2 1 = one := by
  simp only [powDiv2, Finset.sum_range_one]
  rw [show ![0, 1 - 1 - 0] = (0 : Fin 2 → ℕ) from by decide,
    show (-1 : ℤ) ^ (0 : ℕ) = 1 from by decide,
    show (monomial (0 : Fin 2 → ℕ) 1) = one from rfl]

/-- EKL (2.6), m = 2: `d_1(x_1^2) = x_1 - x_2`. -/
theorem powDiv1_two : powDiv1 2 = generator 0 - generator 1 := by
  have expand : powDiv1 2 = monomial ![1, 0] 1 + monomial ![0, 1] (-1) := by
    simp only [powDiv1]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
    rw [show ![2 - 1 - 0, 0] = ![1, 0] from by decide,
      show (-1 : ℤ) ^ (0 * (2 - 0)) = 1 from by decide,
      show ![2 - 1 - 1, 1] = ![0, 1] from by decide,
      show (-1 : ℤ) ^ (1 * (2 - 1)) = -1 from by decide]
  rw [expand]
  simp only [generator]
  rw [show expSingle (0 : Fin 2) = ![1, 0] from by decide,
    show expSingle (1 : Fin 2) = ![0, 1] from by decide,
    sub_eq_add_neg, ← monomial_neg]

/-- EKL (2.6), m = 2: `d_1(x_2^2) = x_2 - x_1`. -/
theorem powDiv2_two : powDiv2 2 = generator 1 - generator 0 := by
  have expand : powDiv2 2 = monomial ![0, 1] 1 + monomial ![1, 0] (-1) := by
    simp only [powDiv2]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
    rw [show ![0, 2 - 1 - 0] = ![0, 1] from by decide,
      show (-1 : ℤ) ^ (0 : ℕ) = 1 from by decide,
      show ![1, 2 - 1 - 1] = ![1, 0] from by decide,
      show (-1 : ℤ) ^ (1 : ℕ) = -1 from by decide]
  rw [expand]
  simp only [generator]
  rw [show expSingle (0 : Fin 2) = ![1, 0] from by decide,
    show expSingle (1 : Fin 2) = ![0, 1] from by decide,
    sub_eq_add_neg, ← monomial_neg]

/-- EKL (2.6), m = 3: `d_1(x_1^3) = x_1^2 + x_1x_2 + x_2^2`. -/
theorem powDiv1_three : powDiv1 3
    = monomial ![2, 0] 1 + monomial ![1, 1] 1 + monomial ![0, 2] 1 := by
  simp only [powDiv1]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  rfl

/-- EKL (2.6), m = 3: `d_1(x_2^3) = x_2^2 - x_1x_2 + x_1^2`. Stated with
`+ -` so the fixture closes the sub-form by one `sub_eq_add_neg`. -/
theorem powDiv2_three : powDiv2 3
    = monomial ![0, 2] 1 + -monomial ![1, 1] 1 + monomial ![2, 0] 1 := by
  simp only [powDiv2]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  show (monomial ![0, 2] 1 + monomial ![1, 1] (-1) + monomial ![2, 0] 1) = _
  rw [monomial_neg]

/-- EKL (2.6), m = 4: `d_1(x_1^4) = x_1^3 - x_1^2x_2 + x_1x_2^2 - x_2^3`. -/
theorem powDiv1_four : powDiv1 4 = monomial ![3, 0] 1 - monomial ![2, 1] 1
    + monomial ![1, 2] 1 - monomial ![0, 3] 1 := by
  simp only [powDiv1]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  show (monomial ![3, 0] 1 + monomial ![2, 1] (-1) + monomial ![1, 2] 1
      + monomial ![0, 3] (-1)) = _
  rw [monomial_neg, monomial_neg, sub_eq_add_neg, sub_eq_add_neg]

/-- EKL (2.6), m = 4: `d_1(x_2^4) = x_2^3 - x_1x_2^2 + x_1^2x_2 - x_1^3`.
Stated with `+ -` so the fixture closes the sub-form by `sub_eq_add_neg`. -/
theorem powDiv2_four : powDiv2 4 = monomial ![0, 3] 1 + -monomial ![1, 2] 1
    + monomial ![2, 1] 1 + -monomial ![3, 0] 1 := by
  simp only [powDiv2]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  show (monomial ![0, 3] 1 + monomial ![1, 2] (-1) + monomial ![2, 1] 1
      + monomial ![3, 0] (-1)) = _
  rw [monomial_neg, monomial_neg]

/-! ## Generator bridges -/

theorem generator_zero_monomial :
    generator (0 : Fin 2) = monomial ![1, 0] 1 := by
  show monomial (expSingle 0) 1 = monomial ![1, 0] 1
  rw [show expSingle (0 : Fin 2) = ![1, 0] from by decide]

theorem generator_one_monomial :
    generator (1 : Fin 2) = monomial ![0, 1] 1 := by
  show monomial (expSingle 1) 1 = monomial ![0, 1] 1
  rw [show expSingle (1 : Fin 2) = ![0, 1] from by decide]

/-! ## The rank-two action table -/

/-- EKL (2.3): `d_1(1) = 0`. JSON: dd-00. -/
theorem divMonomial_zero_zero : divMonomial 0 0 = 0 := by
  simp only [divMonomial, powDiv1_zero, powDiv2_zero, zero_mul, mul_zero,
    add_zero]

theorem divMonomial_zero_left (b : ℕ) : divMonomial 0 b = powDiv2 b := by
  have hexp : ![0, 0] = (0 : Fin 2 → ℕ) := by decide
  simp only [divMonomial, powDiv1_zero, zero_mul, zero_add, hexp, _root_.pow_zero]
  show mul one (powDiv2 b) = powDiv2 b
  exact one_mul _

theorem divMonomial_zero_right (a : ℕ) : divMonomial a 0 = powDiv1 a := by
  have hexp : ![0, 0] = (0 : Fin 2 → ℕ) := by decide
  simp only [divMonomial, powDiv2_zero, mul_zero, add_zero, hexp, _root_.pow_zero]
  show mul (powDiv1 a) one = powDiv1 a
  exact mul_one _

/-- EKL (2.6): `d_1(x_1x_2) = 0`. JSON: dd-11. -/
theorem divMonomial_one_one : divMonomial 1 1 = 0 := by
  have hx : monomial ![0, 1] (1 : ℤ) = generator 1 :=
    generator_one_monomial.symm
  have hnx : monomial ![0, 1] (-1 : ℤ) = -generator 1 := by
    show monomial ![0, 1] (-1) = -(monomial (expSingle 1) 1)
    rw [show expSingle (1 : Fin 2) = ![0, 1] from by decide, monomial_neg]
  simp only [divMonomial, powDiv1_one, powDiv2_one, _root_.pow_one, hx, hnx,
    one_mul, mul_one, add_neg_cancel]

/-- EKL (2.4): `d_1(x_1^2x_2) = x_1x_2`. JSON: dd-21. -/
theorem divMonomial_two_one : divMonomial 2 1 = monomial ![1, 1] 1 := by
  have hx : monomial ![0, 1] (1 : ℤ) = generator 1 :=
    generator_one_monomial.symm
  have hm01 : mul (generator (0 : Fin 2)) (generator 1)
      = monomial ![1, 1] 1 := by
    show mul (monomial (expSingle 0) 1) (monomial (expSingle 1) 1) = _
    rw [mul_monomial,
      show expSingle (0 : Fin 2) + expSingle 1 = ![1, 1] from by decide,
      show OddMath.skewSign (expSingle (0 : Fin 2)) (expSingle 1) = 1
        from by decide,
      _root_.mul_one, _root_.mul_one]
  have hsq : monomial ![0, 2] (1 : ℤ)
      = mul (generator (1 : Fin 2)) (generator 1) := by
    show monomial ![0, 2] 1
      = mul (monomial (expSingle 1) 1) (monomial (expSingle 1) 1)
    rw [mul_monomial,
      show expSingle (1 : Fin 2) + expSingle 1 = ![0, 2] from by decide,
      show OddMath.skewSign (expSingle (1 : Fin 2)) (expSingle 1) = 1
        from by decide,
      _root_.mul_one, _root_.mul_one]
  have hpow : (-1 : ℤ) ^ (2 : ℕ) = 1 := by decide
  simp only [divMonomial, powDiv1_two, powDiv2_one, hpow, hsq, hx, sub_mul,
    mul_one, hm01, sub_add_cancel]

/-- EKL (2.4): `d_1(x_1x_2^2) = -x_1x_2` (reorder sign). JSON: dd-12. -/
theorem divMonomial_one_two : divMonomial 1 2 = -monomial ![1, 1] 1 := by
  have hx : monomial ![0, 1] (1 : ℤ) = generator 1 :=
    generator_one_monomial.symm
  have hnx : monomial ![0, 1] (-1 : ℤ) = -generator 1 := by
    show monomial ![0, 1] (-1) = -(monomial (expSingle 1) 1)
    rw [show expSingle (1 : Fin 2) = ![0, 1] from by decide, monomial_neg]
  have hsq : monomial ![0, 2] (1 : ℤ)
      = mul (generator (1 : Fin 2)) (generator 1) := by
    show monomial ![0, 2] 1
      = mul (monomial (expSingle 1) 1) (monomial (expSingle 1) 1)
    rw [mul_monomial,
      show expSingle (1 : Fin 2) + expSingle 1 = ![0, 2] from by decide,
      show OddMath.skewSign (expSingle (1 : Fin 2)) (expSingle 1) = 1
        from by decide,
      _root_.mul_one, _root_.mul_one]
  have hm10 : mul (generator (1 : Fin 2)) (generator 0)
      = -monomial ![1, 1] 1 := by
    show mul (monomial (expSingle 1) 1) (monomial (expSingle 0) 1) = _
    rw [mul_monomial,
      show expSingle (1 : Fin 2) + expSingle 0 = ![1, 1] from by decide,
      show OddMath.skewSign (expSingle (1 : Fin 2)) (expSingle 0) = -1
        from by decide,
      _root_.mul_one, _root_.one_mul, monomial_neg]
  rw [divMonomial, powDiv1_one, powDiv2_two, _root_.pow_one, hsq, hnx,
    one_mul, neg_mul]
  simp only [mul_sub, hm10]
  rw [sub_eq_add_neg, neg_neg, neg_add, ← add_assoc, add_neg_cancel, zero_add]

/-- EKL (2.4): `d_1(x_1^2x_2^2) = 0`. JSON: dd-22. -/
theorem divMonomial_two_two : divMonomial 2 2 = 0 := by
  have hsq : monomial ![0, 2] (1 : ℤ)
      = mul (generator (1 : Fin 2)) (generator 1) := by
    show monomial ![0, 2] 1
      = mul (monomial (expSingle 1) 1) (monomial (expSingle 1) 1)
    rw [mul_monomial,
      show expSingle (1 : Fin 2) + expSingle 1 = ![0, 2] from by decide,
      show OddMath.skewSign (expSingle (1 : Fin 2)) (expSingle 1) = 1
        from by decide,
      _root_.mul_one, _root_.mul_one]
  have h0 : mul (generator (0 : Fin 2)) (mul (generator 1) (generator 1))
      = monomial ![1, 2] 1 := by
    rw [← hsq]
    show mul (monomial (expSingle 0) 1) (monomial ![0, 2] 1) = _
    rw [mul_monomial,
      show expSingle (0 : Fin 2) + ![0, 2] = ![1, 2] from by decide,
      show OddMath.skewSign (expSingle (0 : Fin 2)) ![0, 2] = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have h1 : mul (generator (1 : Fin 2)) (mul (generator 1) (generator 1))
      = monomial ![0, 3] 1 := by
    rw [← hsq]
    show mul (monomial (expSingle 1) 1) (monomial ![0, 2] 1) = _
    rw [mul_monomial,
      show expSingle (1 : Fin 2) + ![0, 2] = ![0, 3] from by decide,
      show OddMath.skewSign (expSingle (1 : Fin 2)) ![0, 2] = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have h2 : mul (mul (generator (1 : Fin 2)) (generator 1)) (generator 1)
      = monomial ![0, 3] 1 := by
    rw [← hsq]
    show mul (monomial ![0, 2] 1) (monomial (expSingle 1) 1) = _
    rw [mul_monomial,
      show ![0, 2] + expSingle (1 : Fin 2) = ![0, 3] from by decide,
      show OddMath.skewSign ![0, 2] (expSingle (1 : Fin 2)) = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have h3 : mul (mul (generator (1 : Fin 2)) (generator 1)) (generator 0)
      = monomial ![1, 2] 1 := by
    rw [← hsq]
    show mul (monomial ![0, 2] 1) (monomial (expSingle 0) 1) = _
    rw [mul_monomial,
      show ![0, 2] + expSingle (0 : Fin 2) = ![1, 2] from by decide,
      show OddMath.skewSign ![0, 2] (expSingle (0 : Fin 2)) = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have hpow : (-1 : ℤ) ^ (2 : ℕ) = 1 := by decide
  simp only [divMonomial, powDiv1_two, powDiv2_two, hpow, hsq, sub_mul,
    mul_sub, h0, h1, h2, h3]
  rw [← neg_sub, neg_add_cancel]

/-- EKL (2.6): `d_1(x_1^3) = x_1^2 + x_1x_2 + x_2^2`. JSON: dd-30. -/
theorem divMonomial_three_zero : divMonomial 3 0
    = monomial ![2, 0] 1 + monomial ![1, 1] 1 + monomial ![0, 2] 1 := by
  rw [divMonomial_zero_right, powDiv1_three]

/-- EKL (2.4): `d_1(x_1^3x_2) = x_1^2x_2 + x_1x_2^2`. JSON: dd-31. -/
theorem divMonomial_three_one : divMonomial 3 1
    = monomial ![2, 1] 1 + monomial ![1, 2] 1 := by
  have hx : monomial ![0, 1] (1 : ℤ) = generator 1 :=
    generator_one_monomial.symm
  have k0 : mul (monomial ![2, 0] 1) (generator 1) = monomial ![2, 1] 1 := by
    show mul (monomial ![2, 0] 1) (monomial (expSingle 1) 1) = _
    rw [mul_monomial,
      show ![2, 0] + expSingle (1 : Fin 2) = ![2, 1] from by decide,
      show OddMath.skewSign ![2, 0] (expSingle (1 : Fin 2)) = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have k1 : mul (monomial ![1, 1] 1) (generator 1) = monomial ![1, 2] 1 := by
    show mul (monomial ![1, 1] 1) (monomial (expSingle 1) 1) = _
    rw [mul_monomial,
      show ![1, 1] + expSingle (1 : Fin 2) = ![1, 2] from by decide,
      show OddMath.skewSign ![1, 1] (expSingle (1 : Fin 2)) = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have k2 : mul (monomial ![0, 2] 1) (generator 1) = monomial ![0, 3] 1 := by
    show mul (monomial ![0, 2] 1) (monomial (expSingle 1) 1) = _
    rw [mul_monomial,
      show ![0, 2] + expSingle (1 : Fin 2) = ![0, 3] from by decide,
      show OddMath.skewSign ![0, 2] (expSingle (1 : Fin 2)) = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have hcu : (-1 : ℤ) ^ (3 : ℕ) = -1 := by decide
  simp only [divMonomial, powDiv1_three, powDiv2_one, hcu, hx, monomial_neg,
    add_mul, mul_one, neg_mul, k0, k1, k2]
  rw [add_assoc, add_neg_cancel, add_zero]

/-- EKL (2.4): `d_1(x_1x_2^3) = -(x_1^2x_2 + x_1x_2^2)`. JSON: dd-13. -/
theorem divMonomial_one_three : divMonomial 1 3
    = -monomial ![2, 1] 1 - monomial ![1, 2] 1 := by
  have hx : monomial ![0, 1] (1 : ℤ) = generator 1 :=
    generator_one_monomial.symm
  have hnx : monomial ![0, 1] (-1 : ℤ) = -generator 1 := by
    show monomial ![0, 1] (-1) = -(monomial (expSingle 1) 1)
    rw [show expSingle (1 : Fin 2) = ![0, 1] from by decide, monomial_neg]
  have j0 : mul (generator (1 : Fin 2)) (monomial ![0, 2] 1)
      = monomial ![0, 3] 1 := by
    show mul (monomial (expSingle 1) 1) (monomial ![0, 2] 1) = _
    rw [mul_monomial,
      show expSingle (1 : Fin 2) + ![0, 2] = ![0, 3] from by decide,
      show OddMath.skewSign (expSingle (1 : Fin 2)) ![0, 2] = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have j1 : mul (generator (1 : Fin 2)) (monomial ![1, 1] 1)
      = -monomial ![1, 2] 1 := by
    show mul (monomial (expSingle 1) 1) (monomial ![1, 1] 1) = _
    rw [mul_monomial,
      show expSingle (1 : Fin 2) + ![1, 1] = ![1, 2] from by decide,
      show OddMath.skewSign (expSingle (1 : Fin 2)) ![1, 1] = -1 from by decide,
      _root_.mul_one, _root_.one_mul, monomial_neg]
  have j2 : mul (generator (1 : Fin 2)) (monomial ![2, 0] 1)
      = monomial ![2, 1] 1 := by
    show mul (monomial (expSingle 1) 1) (monomial ![2, 0] 1) = _
    rw [mul_monomial,
      show expSingle (1 : Fin 2) + ![2, 0] = ![2, 1] from by decide,
      show OddMath.skewSign (expSingle (1 : Fin 2)) ![2, 0] = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  rw [divMonomial, powDiv1_one, powDiv2_three, _root_.pow_one, hnx,
    one_mul, neg_mul]
  simp only [mul_add, mul_neg, j0, j1, j2]
  rw [neg_neg, sub_eq_add_neg, neg_add, neg_add, ← add_assoc, ← add_assoc,
    add_neg_cancel, zero_add,
    add_comm (-monomial ![1, 2] 1) (-monomial ![2, 1] 1)]

/-- EKL (2.4): `d_1(x_1^3x_2^2) = x_1^2x_2^2`. JSON: dd-32. -/
theorem divMonomial_three_two : divMonomial 3 2 = monomial ![2, 2] 1 := by
  have t0 : mul (monomial ![2, 0] 1) (monomial ![0, 2] 1)
      = monomial ![2, 2] 1 := by
    rw [mul_monomial,
      show ![2, 0] + ![0, 2] = ![2, 2] from by decide,
      show OddMath.skewSign ![2, 0] ![0, 2] = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have t1 : mul (monomial ![1, 1] 1) (monomial ![0, 2] 1)
      = monomial ![1, 3] 1 := by
    rw [mul_monomial,
      show ![1, 1] + ![0, 2] = ![1, 3] from by decide,
      show OddMath.skewSign ![1, 1] ![0, 2] = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have t2 : mul (monomial ![0, 2] 1) (monomial ![0, 2] 1)
      = monomial ![0, 4] 1 := by
    rw [mul_monomial,
      show ![0, 2] + ![0, 2] = ![0, 4] from by decide,
      show OddMath.skewSign ![0, 2] ![0, 2] = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have u0 : mul (monomial ![0, 3] 1) (generator 1) = monomial ![0, 4] 1 := by
    show mul (monomial ![0, 3] 1) (monomial (expSingle 1) 1) = _
    rw [mul_monomial,
      show ![0, 3] + expSingle (1 : Fin 2) = ![0, 4] from by decide,
      show OddMath.skewSign ![0, 3] (expSingle (1 : Fin 2)) = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have u1 : mul (monomial ![0, 3] 1) (generator 0) = -monomial ![1, 3] 1 := by
    show mul (monomial ![0, 3] 1) (monomial (expSingle 0) 1) = _
    rw [mul_monomial,
      show ![0, 3] + expSingle (0 : Fin 2) = ![1, 3] from by decide,
      show OddMath.skewSign ![0, 3] (expSingle (0 : Fin 2)) = -1 from by decide,
      _root_.mul_one, _root_.one_mul, monomial_neg]
  have hcu : (-1 : ℤ) ^ (3 : ℕ) = -1 := by decide
  rw [divMonomial, powDiv1_three, powDiv2_two, hcu, monomial_neg, neg_mul]
  simp only [add_mul, mul_sub, t0, t1, t2, u0, u1]
  rw [sub_eq_add_neg, neg_add, ← add_assoc,
    add_assoc (monomial ![2, 2] 1 + monomial ![1, 3] 1) (monomial ![0, 4] 1)
      (-monomial ![0, 4] 1),
    add_neg_cancel, add_zero, neg_neg, add_assoc, add_neg_cancel, add_zero]

/-- EKL (2.4): `d_1(x_1^2x_2^3) = x_1^2x_2^2`. JSON: dd-23. -/
theorem divMonomial_two_three : divMonomial 2 3 = monomial ![2, 2] 1 := by
  have v0 : mul (generator (0 : Fin 2)) (monomial ![0, 3] 1)
      = monomial ![1, 3] 1 := by
    show mul (monomial (expSingle 0) 1) (monomial ![0, 3] 1) = _
    rw [mul_monomial,
      show expSingle (0 : Fin 2) + ![0, 3] = ![1, 3] from by decide,
      show OddMath.skewSign (expSingle (0 : Fin 2)) ![0, 3] = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have v1 : mul (generator (1 : Fin 2)) (monomial ![0, 3] 1)
      = monomial ![0, 4] 1 := by
    show mul (monomial (expSingle 1) 1) (monomial ![0, 3] 1) = _
    rw [mul_monomial,
      show expSingle (1 : Fin 2) + ![0, 3] = ![0, 4] from by decide,
      show OddMath.skewSign (expSingle (1 : Fin 2)) ![0, 3] = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have t2 : mul (monomial ![0, 2] 1) (monomial ![0, 2] 1)
      = monomial ![0, 4] 1 := by
    rw [mul_monomial,
      show ![0, 2] + ![0, 2] = ![0, 4] from by decide,
      show OddMath.skewSign ![0, 2] ![0, 2] = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have w1 : mul (monomial ![0, 2] 1) (monomial ![1, 1] 1)
      = monomial ![1, 3] 1 := by
    rw [mul_monomial,
      show ![0, 2] + ![1, 1] = ![1, 3] from by decide,
      show OddMath.skewSign ![0, 2] ![1, 1] = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have w2 : mul (monomial ![0, 2] 1) (monomial ![2, 0] 1)
      = monomial ![2, 2] 1 := by
    rw [mul_monomial,
      show ![0, 2] + ![2, 0] = ![2, 2] from by decide,
      show OddMath.skewSign ![0, 2] ![2, 0] = 1 from by decide,
      _root_.mul_one, _root_.mul_one]
  have hpow : (-1 : ℤ) ^ (2 : ℕ) = 1 := by decide
  simp only [divMonomial, powDiv1_two, powDiv2_three, hpow, sub_mul, mul_neg,
    mul_add, v0, v1, t2, w1, w2]
  rw [sub_eq_add_neg, ← add_assoc,
    add_assoc (monomial ![1, 3] 1) (-monomial ![0, 4] 1)
      (monomial ![0, 4] 1 + -monomial ![1, 3] 1),
    ← add_assoc (-monomial ![0, 4] 1) (monomial ![0, 4] 1)
      (-monomial ![1, 3] 1),
    neg_add_cancel, zero_add, add_neg_cancel, zero_add]

/-- EKL (2.6): `d_1(x_1^4)` alternating sum. JSON: dd-40. -/
theorem divMonomial_four_zero : divMonomial 4 0 = monomial ![3, 0] 1
    - monomial ![2, 1] 1 + monomial ![1, 2] 1 - monomial ![0, 3] 1 := by
  rw [divMonomial_zero_right, powDiv1_four]

/-! ## The operator `div1`: linearity and values -/

theorem divMonomialCoeff_zero (e : Fin 2 → ℕ) :
    (0 : ℤ) • divMonomial (e 0) (e 1) = 0 :=
  zero_smul _ _

theorem divMonomialCoeff_add (e : Fin 2 → ℕ) (r₁ r₂ : ℤ) :
    (r₁ + r₂) • divMonomial (e 0) (e 1)
      = r₁ • divMonomial (e 0) (e 1) + r₂ • divMonomial (e 0) (e 1) :=
  add_smul _ _ _

theorem div1_zero : div1 0 = 0 := by
  show (0 : SkewPolynomial 2).sum (fun e r => r • divMonomial (e 0) (e 1)) = 0
  exact Finsupp.sum_zero_index

theorem div1_add (f₁ f₂ : SkewPolynomial 2) :
    div1 (f₁ + f₂) = div1 f₁ + div1 f₂ := by
  show (f₁ + f₂).sum (fun e r => r • divMonomial (e 0) (e 1))
    = f₁.sum (fun e r => r • divMonomial (e 0) (e 1))
      + f₂.sum (fun e r => r • divMonomial (e 0) (e 1))
  exact Finsupp.sum_add_index' (fun e => divMonomialCoeff_zero e)
    (fun e r₁ r₂ => divMonomialCoeff_add e r₁ r₂)

theorem div1_neg (f : SkewPolynomial 2) : div1 (-f) = -div1 f := by
  have h : div1 (-f) + div1 f = 0 := by
    rw [← div1_add, neg_add_cancel, div1_zero]
  exact eq_neg_of_add_eq_zero_left h

theorem div1_sub (f₁ f₂ : SkewPolynomial 2) :
    div1 (f₁ - f₂) = div1 f₁ - div1 f₂ := by
  rw [sub_eq_add_neg, div1_add, div1_neg, sub_eq_add_neg]

theorem div1_monomial (e : Fin 2 → ℕ) (r : ℤ) :
    div1 (monomial e r) = r • divMonomial (e 0) (e 1) := by
  show (monomial e r).sum (fun e' r' => r' • divMonomial (e' 0) (e' 1))
    = r • divMonomial (e 0) (e 1)
  show (Finsupp.single e r).sum (fun e' r' => r' • divMonomial (e' 0) (e' 1))
    = r • divMonomial (e 0) (e 1)
  rw [Finsupp.sum_single_index (divMonomialCoeff_zero e)]

/-- EKL (2.3): `d_1(1) = 0`. JSON: dd-00 at operator level. -/
theorem div1_one : div1 one = 0 := by
  show div1 (monomial (0 : Fin 2 → ℕ) 1) = 0
  rw [div1_monomial,
    show (0 : Fin 2 → ℕ) 0 = 0 from by decide,
    show (0 : Fin 2 → ℕ) 1 = 0 from by decide,
    divMonomial_zero_zero, one_smul]

/-- EKL (2.3): `d_1(x_1) = 1`. JSON: dd-10 at operator level. -/
theorem div1_generator_zero : div1 (generator (0 : Fin 2)) = one := by
  show div1 (monomial (expSingle 0) 1) = one
  rw [div1_monomial,
    show expSingle (0 : Fin 2) 0 = 1 from by decide,
    show expSingle (0 : Fin 2) 1 = 0 from by decide,
    divMonomial_zero_right, powDiv1_one, one_smul]

/-- EKL (2.3): `d_1(x_2) = 1`, the characteristic oddity. JSON: dd-01. -/
theorem div1_generator_one : div1 (generator (1 : Fin 2)) = one := by
  show div1 (monomial (expSingle 1) 1) = one
  rw [div1_monomial,
    show expSingle (1 : Fin 2) 0 = 0 from by decide,
    show expSingle (1 : Fin 2) 1 = 1 from by decide,
    divMonomial_zero_left, powDiv2_one, one_smul]

/-! ## Leibniz on generator pairs, EKL (2.4) -/

/-- Leibniz seed: `d_1(x_1 * x_1) = d_1(x_1)x_1 + s_1(x_1)d_1(x_1)`. -/
theorem divLeibniz_gen00 :
    div1 (mul (generator (0 : Fin 2)) (generator 0))
      = mul (div1 (generator (0 : Fin 2))) (generator 0)
        + mul (symm1 (generator (0 : Fin 2))) (div1 (generator 0)) := by
  have hsq00 : mul (generator (0 : Fin 2)) (generator 0)
      = monomial ![2, 0] 1 := by
    show mul (monomial (expSingle 0) 1) (monomial (expSingle 0) 1) = _
    rw [mul_monomial,
      show expSingle (0 : Fin 2) + expSingle 0 = ![2, 0] from by decide,
      show OddMath.skewSign (expSingle (0 : Fin 2)) (expSingle 0) = 1
        from by decide,
      _root_.mul_one, _root_.mul_one]
  rw [hsq00, div1_generator_zero, symm1_generator_zero, div1_monomial,
    show (![2, 0] : Fin 2 → ℕ) 0 = 2 from by decide,
    show (![2, 0] : Fin 2 → ℕ) 1 = 0 from by decide,
    divMonomial_zero_right, powDiv1_two, one_smul, one_mul, neg_mul, mul_one,
    sub_eq_add_neg]

/-- Leibniz seed: `d_1(x_1 * x_2) = d_1(x_1)x_2 + s_1(x_1)d_1(x_2)`. -/
theorem divLeibniz_gen01 :
    div1 (mul (generator (0 : Fin 2)) (generator 1))
      = mul (div1 (generator (0 : Fin 2))) (generator 1)
        + mul (symm1 (generator (0 : Fin 2))) (div1 (generator 1)) := by
  have hm01 : mul (generator (0 : Fin 2)) (generator 1)
      = monomial ![1, 1] 1 := by
    show mul (monomial (expSingle 0) 1) (monomial (expSingle 1) 1) = _
    rw [mul_monomial,
      show expSingle (0 : Fin 2) + expSingle 1 = ![1, 1] from by decide,
      show OddMath.skewSign (expSingle (0 : Fin 2)) (expSingle 1) = 1
        from by decide,
      _root_.mul_one, _root_.mul_one]
  rw [hm01, div1_monomial,
    show (![1, 1] : Fin 2 → ℕ) 0 = 1 from by decide,
    show (![1, 1] : Fin 2 → ℕ) 1 = 1 from by decide,
    divMonomial_one_one, one_smul, div1_generator_zero, div1_generator_one,
    symm1_generator_zero, one_mul, neg_mul, mul_one, add_neg_cancel]

/-- Leibniz seed: `d_1(x_2 * x_2) = d_1(x_2)x_2 + s_1(x_2)d_1(x_2)`. -/
theorem divLeibniz_gen11 :
    div1 (mul (generator (1 : Fin 2)) (generator 1))
      = mul (div1 (generator (1 : Fin 2))) (generator 1)
        + mul (symm1 (generator (1 : Fin 2))) (div1 (generator 1)) := by
  have hsq11 : mul (generator (1 : Fin 2)) (generator 1)
      = monomial ![0, 2] 1 := by
    show mul (monomial (expSingle 1) 1) (monomial (expSingle 1) 1) = _
    rw [mul_monomial,
      show expSingle (1 : Fin 2) + expSingle 1 = ![0, 2] from by decide,
      show OddMath.skewSign (expSingle (1 : Fin 2)) (expSingle 1) = 1
        from by decide,
      _root_.mul_one, _root_.mul_one]
  rw [hsq11, div1_monomial,
    show (![0, 2] : Fin 2 → ℕ) 0 = 0 from by decide,
    show (![0, 2] : Fin 2 → ℕ) 1 = 2 from by decide,
    divMonomial_zero_left, powDiv2_two, one_smul,
    div1_generator_one, symm1_generator_one, one_mul, neg_mul, mul_one,
    sub_eq_add_neg]

/-! ## `d_1^2 = 0` spot checks (EKL Prop. 2.1 samples, hand grade) -/

theorem div1_sq_x1sq : div1 (div1 (monomial ![2, 0] 1)) = 0 := by
  rw [div1_monomial,
    show (![2, 0] : Fin 2 → ℕ) 0 = 2 from by decide,
    show (![2, 0] : Fin 2 → ℕ) 1 = 0 from by decide,
    divMonomial_zero_right, powDiv1_two, one_smul, div1_sub,
    div1_generator_zero, div1_generator_one, sub_self]

theorem div1_sq_x1x2 : div1 (div1 (monomial ![1, 1] 1)) = 0 := by
  rw [div1_monomial,
    show (![1, 1] : Fin 2 → ℕ) 0 = 1 from by decide,
    show (![1, 1] : Fin 2 → ℕ) 1 = 1 from by decide,
    divMonomial_one_one, one_smul, div1_zero]

theorem div1_sq_x1cube_x2sq : div1 (div1 (monomial ![3, 2] 1)) = 0 := by
  rw [div1_monomial,
    show (![3, 2] : Fin 2 → ℕ) 0 = 3 from by decide,
    show (![3, 2] : Fin 2 → ℕ) 1 = 2 from by decide,
    divMonomial_three_two, one_smul, div1_monomial,
    show (![2, 2] : Fin 2 → ℕ) 0 = 2 from by decide,
    show (![2, 2] : Fin 2 → ℕ) 1 = 2 from by decide,
    divMonomial_two_two, one_smul]

end OddMath.DividedDifferences
