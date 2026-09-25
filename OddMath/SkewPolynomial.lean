import OddMath.SkewSign
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finsupp.Single

/-!
# Finite-support integer model of the skew-polynomial ring

For exponent vectors `a b : Fin n → ℕ`, the product of the increasing-index
ordered words `x^a * x^b` collects `(-1) ^ B(a, b)`, where `B` counts pairs
`(i, j)` with `j < i` weighted by `a i * b j`.  Distinct generators
anticommute in EKL, arXiv:1111.1320v1, §2.1.1, (2.1), p.3; the increasing-index
normal order is locked by the sign convention and
the translation table.

This module constructs the finite-support model over `ℤ` with an explicit
named multiplication (no ambient `Finsupp` multiplication instance) and proves:
basis multiplication, distributivity, universal associativity via the imported
`OddMath.skewSign_cocycle`, unit laws, distinct-generator anticommutation, and
nonzero same-generator square / ordered rank-two coordinates.

This is ONLY the finite-support integer model.  It is not a quotient
equivalence, normal-form, or PBW theorem.
-/

namespace OddMath.SkewPolynomial

set_option linter.dupNamespace false

/-- Finite-support integer polynomials indexed by exponent vectors. -/
abbrev SkewPolynomial (n : ℕ) := ((Fin n → ℕ) →₀ ℤ)

/-- Monomial: finite-support singleton at exponent vector `a` with coefficient `c`.
Reducible so that singleton rewrite rules apply through the wrapper. -/
@[reducible]
noncomputable def monomial {n : ℕ} (a : Fin n → ℕ) (c : ℤ) : SkewPolynomial n :=
  Finsupp.single a c

/-- Unit exponent vector at index `i`. -/
def expSingle {n : ℕ} (i : Fin n) : Fin n → ℕ :=
  fun j => if i = j then 1 else 0

/-- Skew multiplication: double sum over the finite supports, with the
crossing-count sign.  No degree truncation is used. -/
noncomputable def mul {n : ℕ} (f g : SkewPolynomial n) : SkewPolynomial n :=
  f.sum fun a r => g.sum fun b s => monomial (a + b) (r * s * OddMath.skewSign a b)

/-- Multiplicative unit: singleton at the zero exponent vector. -/
noncomputable def one {n : ℕ} : SkewPolynomial n := monomial 0 1

/-- Generator: singleton at the `i`-th unit exponent vector. -/
noncomputable def generator {n : ℕ} (i : Fin n) : SkewPolynomial n :=
  monomial (expSingle i) 1

theorem monomial_coeff_zero_left {n : ℕ} (a b : Fin n → ℕ) (s : ℤ) :
    monomial (a + b) ((0 : ℤ) * s * OddMath.skewSign a b) = 0 := by
  simp [monomial, Finsupp.single_zero]

theorem monomial_coeff_zero_right {n : ℕ} (a b : Fin n → ℕ) (r : ℤ) :
    monomial (a + b) (r * (0 : ℤ) * OddMath.skewSign a b) = 0 := by
  simp [monomial, Finsupp.single_zero]

theorem monomial_coeff_add_left {n : ℕ} (a b : Fin n → ℕ) (r₁ r₂ s : ℤ) :
    monomial (a + b) ((r₁ + r₂) * s * OddMath.skewSign a b)
      = monomial (a + b) (r₁ * s * OddMath.skewSign a b)
        + monomial (a + b) (r₂ * s * OddMath.skewSign a b) := by
  have h : (r₁ + r₂) * s * OddMath.skewSign a b
      = r₁ * s * OddMath.skewSign a b + r₂ * s * OddMath.skewSign a b := by
    rw [add_mul, add_mul]
  rw [h]
  exact Finsupp.single_add _ _ _

theorem monomial_coeff_add_right {n : ℕ} (a b : Fin n → ℕ) (r s₁ s₂ : ℤ) :
    monomial (a + b) (r * (s₁ + s₂) * OddMath.skewSign a b)
      = monomial (a + b) (r * s₁ * OddMath.skewSign a b)
        + monomial (a + b) (r * s₂ * OddMath.skewSign a b) := by
  have h : r * (s₁ + s₂) * OddMath.skewSign a b
      = r * s₁ * OddMath.skewSign a b + r * s₂ * OddMath.skewSign a b := by
    rw [mul_add, add_mul]
  rw [h]
  exact Finsupp.single_add _ _ _

theorem monomial_neg {n : ℕ} (a : Fin n → ℕ) (c : ℤ) :
    monomial a (-c) = -monomial a c :=
  Finsupp.single_neg a c

/-- Singleton product formula: the entire multiplication table on monomials. -/
theorem mul_monomial {n : ℕ} (a b : Fin n → ℕ) (r s : ℤ) :
    mul (monomial a r) (monomial b s) =
      monomial (a + b) (r * s * OddMath.skewSign a b) := by
  have hzR : ∀ (a' : Fin n → ℕ) (r' : ℤ),
      (fun b' s' => monomial (a' + b') (r' * s' * OddMath.skewSign a' b')) b (0 : ℤ)
        = 0 :=
    fun a' r' => monomial_coeff_zero_right a' b r'
  have hzO : (fun a' r' => (monomial b s).sum
        (fun b' s' => monomial (a' + b') (r' * s' * OddMath.skewSign a' b'))) a (0 : ℤ)
        = 0 := by
    show (monomial b s).sum
        (fun b' s' => monomial (a + b') ((0 : ℤ) * s' * OddMath.skewSign a b')) = 0
    calc (monomial b s).sum
            (fun b' s' => monomial (a + b') ((0 : ℤ) * s' * OddMath.skewSign a b'))
        = (monomial b s).sum (fun _ _ => (0 : SkewPolynomial n)) :=
          Finsupp.sum_congr
            (fun b' _ => monomial_coeff_zero_left a b' ((monomial b s) b'))
      _ = 0 := Finsupp.sum_zero
  show (Finsupp.single a r).sum (fun a' r' => (monomial b s).sum
      (fun b' s' => monomial (a' + b') (r' * s' * OddMath.skewSign a' b')))
      = monomial (a + b) (r * s * OddMath.skewSign a b)
  rw [Finsupp.sum_single_index hzO]
  show (monomial b s).sum
      (fun b' s' => monomial (a + b') (r * s' * OddMath.skewSign a b'))
      = monomial (a + b) (r * s * OddMath.skewSign a b)
  show (Finsupp.single b s).sum
      (fun b' s' => monomial (a + b') (r * s' * OddMath.skewSign a b'))
      = monomial (a + b) (r * s * OddMath.skewSign a b)
  rw [Finsupp.sum_single_index (hzR a r)]

theorem zero_mul {n : ℕ} (g : SkewPolynomial n) : mul 0 g = 0 := by
  show (0 : SkewPolynomial n).sum
      (fun a r => g.sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b)))
      = 0
  exact Finsupp.sum_zero_index

theorem mul_zero {n : ℕ} (f : SkewPolynomial n) : mul f 0 = 0 := by
  show f.sum (fun a r => (0 : SkewPolynomial n).sum
      (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b))) = 0
  calc f.sum (fun a r => (0 : SkewPolynomial n).sum
          (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b)))
      = f.sum (fun _ _ => (0 : SkewPolynomial n)) :=
        Finsupp.sum_congr (fun _ _ => Finsupp.sum_zero_index)
    _ = 0 := Finsupp.sum_zero

theorem add_mul {n : ℕ} (f₁ f₂ g : SkewPolynomial n) :
    mul (f₁ + f₂) g = mul f₁ g + mul f₂ g := by
  have hzero : ∀ (a : Fin n → ℕ),
      g.sum (fun b s => monomial (a + b) ((0 : ℤ) * s * OddMath.skewSign a b)) = 0 :=
    fun a => by
      calc g.sum (fun b s => monomial (a + b) ((0 : ℤ) * s * OddMath.skewSign a b))
          = g.sum (fun _ _ => (0 : SkewPolynomial n)) :=
            Finsupp.sum_congr
              (fun b _ => monomial_coeff_zero_left a b (g b))
        _ = 0 := Finsupp.sum_zero
  have hadd : ∀ (a : Fin n → ℕ) (r₁ r₂ : ℤ),
      g.sum (fun b s => monomial (a + b) ((r₁ + r₂) * s * OddMath.skewSign a b))
        = g.sum (fun b s => monomial (a + b) (r₁ * s * OddMath.skewSign a b))
          + g.sum (fun b s => monomial (a + b) (r₂ * s * OddMath.skewSign a b)) := by
    intro a r₁ r₂
    calc g.sum (fun b s => monomial (a + b) ((r₁ + r₂) * s * OddMath.skewSign a b))
        = g.sum (fun b s => monomial (a + b) (r₁ * s * OddMath.skewSign a b)
            + monomial (a + b) (r₂ * s * OddMath.skewSign a b)) := by
          refine Finsupp.sum_congr ?_
          intro b _
          exact monomial_coeff_add_left a b r₁ r₂ (g b)
      _ = g.sum (fun b s => monomial (a + b) (r₁ * s * OddMath.skewSign a b))
          + g.sum (fun b s => monomial (a + b) (r₂ * s * OddMath.skewSign a b)) :=
          Finsupp.sum_add
  show (f₁ + f₂).sum
        (fun a r => g.sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b)))
      = f₁.sum (fun a r => g.sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b)))
        + f₂.sum
          (fun a r => g.sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b)))
  exact Finsupp.sum_add_index' (fun a => hzero a) (fun a r₁ r₂ => hadd a r₁ r₂)

theorem mul_add {n : ℕ} (f g₁ g₂ : SkewPolynomial n) :
    mul f (g₁ + g₂) = mul f g₁ + mul f g₂ := by
  have hinner : ∀ (a : Fin n → ℕ) (r : ℤ),
      (g₁ + g₂).sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b))
        = g₁.sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b))
          + g₂.sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b)) :=
    fun a r => Finsupp.sum_add_index' (fun b => monomial_coeff_zero_right a b r)
      (fun b s₁ s₂ => monomial_coeff_add_right a b r s₁ s₂)
  show f.sum (fun a r => (g₁ + g₂).sum
        (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b)))
      = f.sum (fun a r => g₁.sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b)))
        + f.sum
          (fun a r => g₂.sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b)))
  calc f.sum (fun a r => (g₁ + g₂).sum
            (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b)))
      = f.sum (fun a r => g₁.sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b))
          + g₂.sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b))) := by
        refine Finsupp.sum_congr ?_
        intro a _
        exact hinner a (f a)
    _ = f.sum (fun a r => g₁.sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b)))
        + f.sum
          (fun a r => g₂.sum (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b))) :=
        Finsupp.sum_add

/-- Singleton associativity: the cocycle pays for reassociation. -/
theorem mul_assoc_single {n : ℕ} (a b c : Fin n → ℕ) (r s t : ℤ) :
    mul (mul (monomial a r) (monomial b s)) (monomial c t)
      = mul (monomial a r) (mul (monomial b s) (monomial c t)) := by
  simp only [mul_monomial]
  have hexp : (a + b) + c = a + (b + c) := add_assoc _ _ _
  have hsign := OddMath.skewSign_cocycle a b c
  have hcoeff : (r * s * OddMath.skewSign a b) * t * OddMath.skewSign (a + b) c
      = r * (s * t * OddMath.skewSign b c) * OddMath.skewSign a (b + c) := by
    calc (r * s * OddMath.skewSign a b) * t * OddMath.skewSign (a + b) c
        = (r * s * t) * (OddMath.skewSign a b * OddMath.skewSign (a + b) c) := by
          ac_rfl
      _ = (r * s * t) * (OddMath.skewSign b c * OddMath.skewSign a (b + c)) := by
          rw [hsign]
      _ = r * (s * t * OddMath.skewSign b c) * OddMath.skewSign a (b + c) := by
          ac_rfl
  rw [hexp, hcoeff]

/-- Associativity with two leading singletons, by induction on the third factor. -/
theorem mul_assoc_two_single_left {n : ℕ} (a b : Fin n → ℕ) (r s : ℤ)
    (h : SkewPolynomial n) :
    mul (mul (monomial a r) (monomial b s)) h
      = mul (monomial a r) (mul (monomial b s) h) := by
  induction h using Finsupp.induction_linear with
  | zero => simp [mul_zero]
  | add h₁ h₂ ih₁ ih₂ =>
      calc mul (mul (monomial a r) (monomial b s)) (h₁ + h₂)
          = mul (mul (monomial a r) (monomial b s)) h₁
            + mul (mul (monomial a r) (monomial b s)) h₂ := by rw [mul_add]
        _ = mul (monomial a r) (mul (monomial b s) h₁)
            + mul (monomial a r) (mul (monomial b s) h₂) := by rw [ih₁, ih₂]
        _ = mul (monomial a r)
              (mul (monomial b s) h₁ + mul (monomial b s) h₂) := by rw [← mul_add]
        _ = mul (monomial a r) (mul (monomial b s) (h₁ + h₂)) := by
            conv_rhs => rw [mul_add]
  | single c t =>
      show mul (mul (monomial a r) (monomial b s)) (monomial c t)
        = mul (monomial a r) (mul (monomial b s) (monomial c t))
      exact mul_assoc_single a b c r s t

/-- Associativity with one leading singleton, by induction on the middle factor. -/
theorem mul_assoc_one_single_left {n : ℕ} (a : Fin n → ℕ) (r : ℤ)
    (g h : SkewPolynomial n) :
    mul (mul (monomial a r) g) h = mul (monomial a r) (mul g h) := by
  induction g using Finsupp.induction_linear with
  | zero => simp [mul_zero, zero_mul]
  | add g₁ g₂ ih₁ ih₂ =>
      calc mul (mul (monomial a r) (g₁ + g₂)) h
          = mul (mul (monomial a r) g₁ + mul (monomial a r) g₂) h := by rw [mul_add]
        _ = mul (mul (monomial a r) g₁) h + mul (mul (monomial a r) g₂) h := by
            rw [add_mul]
        _ = mul (monomial a r) (mul g₁ h) + mul (monomial a r) (mul g₂ h) := by
            rw [ih₁, ih₂]
        _ = mul (monomial a r) (mul g₁ h + mul g₂ h) := by rw [← mul_add]
        _ = mul (monomial a r) (mul (g₁ + g₂) h) := by conv_rhs => rw [add_mul]
  | single b s =>
      show mul (mul (monomial a r) (monomial b s)) h
        = mul (monomial a r) (mul (monomial b s) h)
      exact mul_assoc_two_single_left a b r s h

/-- Associativity with a trailing singleton, by induction on the first factor. -/
theorem mul_assoc_single_right {n : ℕ} (f g : SkewPolynomial n) (c : Fin n → ℕ)
    (t : ℤ) :
    mul (mul f g) (monomial c t) = mul f (mul g (monomial c t)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [zero_mul]
  | add f₁ f₂ ih₁ ih₂ =>
      calc mul (mul (f₁ + f₂) g) (monomial c t)
          = mul (mul f₁ g + mul f₂ g) (monomial c t) := by rw [add_mul]
        _ = mul (mul f₁ g) (monomial c t) + mul (mul f₂ g) (monomial c t) := by
            rw [add_mul]
        _ = mul f₁ (mul g (monomial c t)) + mul f₂ (mul g (monomial c t)) := by
            rw [ih₁, ih₂]
        _ = mul (f₁ + f₂) (mul g (monomial c t)) := by rw [← add_mul]
  | single a r =>
      show mul (mul (monomial a r) g) (monomial c t)
        = mul (monomial a r) (mul g (monomial c t))
      exact mul_assoc_one_single_left a r g (monomial c t)

/-- Universal associativity, by induction on the trailing factor. -/
theorem mul_assoc {n : ℕ} (f g h : SkewPolynomial n) :
    mul (mul f g) h = mul f (mul g h) := by
  induction h using Finsupp.induction_linear with
  | zero => simp [mul_zero]
  | add h₁ h₂ ih₁ ih₂ =>
      calc mul (mul f g) (h₁ + h₂)
          = mul (mul f g) h₁ + mul (mul f g) h₂ := by rw [mul_add]
        _ = mul f (mul g h₁) + mul f (mul g h₂) := by rw [ih₁, ih₂]
        _ = mul f (mul g h₁ + mul g h₂) := by rw [← mul_add]
        _ = mul f (mul g (h₁ + h₂)) := by conv_rhs => rw [mul_add]
  | single c t =>
      show mul (mul f g) (monomial c t) = mul f (mul g (monomial c t))
      exact mul_assoc_single_right f g c t

theorem crossingCount_zero_left {n : ℕ} (b : Fin n → ℕ) :
    OddMath.crossingCount 0 b = 0 := by
  simp [OddMath.crossingCount]

theorem crossingCount_zero_right {n : ℕ} (a : Fin n → ℕ) :
    OddMath.crossingCount a 0 = 0 := by
  simp [OddMath.crossingCount]

theorem skewSign_zero_left {n : ℕ} (b : Fin n → ℕ) :
    OddMath.skewSign 0 b = 1 := by
  simp [OddMath.skewSign, crossingCount_zero_left]

theorem skewSign_zero_right {n : ℕ} (a : Fin n → ℕ) :
    OddMath.skewSign a 0 = 1 := by
  simp [OddMath.skewSign, crossingCount_zero_right]

theorem one_mul {n : ℕ} (f : SkewPolynomial n) : mul one f = f := by
  have hzero : f.sum
      (fun b s => monomial ((0 : Fin n → ℕ) + b)
        ((0 : ℤ) * s * OddMath.skewSign 0 b)) = 0 := by
    calc f.sum (fun b s => monomial ((0 : Fin n → ℕ) + b)
            ((0 : ℤ) * s * OddMath.skewSign 0 b))
        = f.sum (fun _ _ => (0 : SkewPolynomial n)) :=
          Finsupp.sum_congr
            (fun b _ => monomial_coeff_zero_left 0 b (f b))
      _ = 0 := Finsupp.sum_zero
  have hpt : ∀ (b : Fin n → ℕ) (s : ℤ),
      monomial ((0 : Fin n → ℕ) + b) (1 * s * OddMath.skewSign 0 b)
        = monomial b s := by
    intro b s
    rw [zero_add, skewSign_zero_left, _root_.mul_one, _root_.one_mul]
  calc mul one f
      = f.sum (fun b s => monomial ((0 : Fin n → ℕ) + b)
        (1 * s * OddMath.skewSign 0 b)) := by
        show (Finsupp.single (0 : Fin n → ℕ) 1).sum
            (fun a r => f.sum
              (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b))) = _
        rw [Finsupp.sum_single_index hzero]
    _ = f.sum (fun b s => monomial b s) := by
        refine Finsupp.sum_congr ?_
        intro b _
        exact hpt b (f b)
    _ = f := Finsupp.sum_single f

theorem mul_one {n : ℕ} (f : SkewPolynomial n) : mul f one = f := by
  have hpt : ∀ (a : Fin n → ℕ) (r : ℤ),
      monomial (a + (0 : Fin n → ℕ)) (r * 1 * OddMath.skewSign a 0)
        = monomial a r := by
    intro a r
    rw [add_zero, skewSign_zero_right, _root_.mul_one, _root_.mul_one]
  calc mul f one
      = f.sum (fun a r => monomial (a + (0 : Fin n → ℕ))
        (r * 1 * OddMath.skewSign a 0)) := by
        show f.sum (fun a r => (Finsupp.single (0 : Fin n → ℕ) 1).sum
            (fun b s => monomial (a + b) (r * s * OddMath.skewSign a b))) = _
        refine Finsupp.sum_congr ?_
        intro a _
        show (Finsupp.single (0 : Fin n → ℕ) 1).sum
            (fun b s => monomial (a + b) ((f a) * s * OddMath.skewSign a b))
            = monomial (a + (0 : Fin n → ℕ)) ((f a) * 1 * OddMath.skewSign a 0)
        rw [Finsupp.sum_single_index]
        exact monomial_coeff_zero_right a 0 (f a)
    _ = f.sum (fun a r => monomial a r) := by
        refine Finsupp.sum_congr ?_
        intro a _
        exact hpt a (f a)
    _ = f := Finsupp.sum_single f

/-- A unit vector sums to `1` over any finset containing its index. -/
theorem sum_expSingle {n : ℕ} (j : Fin n) (s : Finset (Fin n)) :
    (∑ k ∈ s, expSingle j k) = if j ∈ s then 1 else 0 := by
  simp only [expSingle, Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- Crossing count of two unit vectors: `1` iff the pair is out of order. -/
theorem crossingCount_expSingle {n : ℕ} (i j : Fin n) :
    OddMath.crossingCount (expSingle i) (expSingle j) = if j < i then 1 else 0 := by
  have outer : ∀ i' : Fin n, (expSingle i) i' * (if j < i' then (1 : ℕ) else 0)
      = (if i = i' then (if j < i' then 1 else 0) else 0) := by
    intro i'
    simp only [expSingle]
    by_cases h : i = i'
    · subst h
      simp
    · rw [if_neg h, if_neg h]
      simp
  simp only [OddMath.crossingCount, ← Finset.mul_sum, sum_expSingle,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_congr rfl (fun i' _ => outer i'), Finset.sum_ite_eq]
  simp

/-- Sign of two unit vectors: `-1` iff the pair is out of order. -/
theorem skewSign_expSingle {n : ℕ} (i j : Fin n) :
    OddMath.skewSign (expSingle i) (expSingle j)
      = if j < i then (-1 : ℤ) else 1 := by
  show (-1 : ℤ) ^ OddMath.crossingCount (expSingle i) (expSingle j) = _
  rw [crossingCount_expSingle]
  by_cases h : j < i <;> simp [h]

/-- Generator products are monomials with the unit-vector sign. -/
theorem mul_generator {n : ℕ} (i j : Fin n) :
    mul (generator i) (generator j)
      = monomial (expSingle i + expSingle j)
        (OddMath.skewSign (expSingle i) (expSingle j)) := by
  show mul (monomial (expSingle i) 1) (monomial (expSingle j) 1) = _
  rw [mul_monomial, _root_.one_mul, _root_.one_mul]

/-- Distinct generators anticommute. -/
theorem generator_anticommute {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    mul (generator i) (generator j) = -mul (generator j) (generator i) := by
  have hprod : OddMath.skewSign (expSingle i) (expSingle j)
      * OddMath.skewSign (expSingle j) (expSingle i) = (-1 : ℤ) := by
    rw [skewSign_expSingle, skewSign_expSingle]
    cases lt_or_gt_of_ne h with
    | inl h_ij =>
        have h1 : ¬ j < i := not_lt_of_gt h_ij
        rw [if_neg h1, if_pos h_ij]
        exact _root_.one_mul _
    | inr h_ji =>
        have h2 : j < i := h_ji
        have h3 : ¬ i < j := not_lt_of_gt h_ji
        rw [if_pos h2, if_neg h3]
        exact _root_.mul_one _
  have hsq : OddMath.skewSign (expSingle j) (expSingle i)
      * OddMath.skewSign (expSingle j) (expSingle i) = 1 := by
    rw [skewSign_expSingle]
    by_cases hlt : i < j
    · rw [if_pos hlt]
      decide
    · rw [if_neg hlt]
      exact _root_.mul_one _
  have hsign : OddMath.skewSign (expSingle i) (expSingle j)
      = -OddMath.skewSign (expSingle j) (expSingle i) := by
    calc OddMath.skewSign (expSingle i) (expSingle j)
        = OddMath.skewSign (expSingle i) (expSingle j)
          * (OddMath.skewSign (expSingle j) (expSingle i)
            * OddMath.skewSign (expSingle j) (expSingle i)) := by
            rw [hsq, _root_.mul_one]
      _ = (OddMath.skewSign (expSingle i) (expSingle j)
          * OddMath.skewSign (expSingle j) (expSingle i))
          * OddMath.skewSign (expSingle j) (expSingle i) := by ac_rfl
      _ = -OddMath.skewSign (expSingle j) (expSingle i) := by
          rw [hprod, neg_one_mul]
  rw [mul_generator, mul_generator, add_comm (expSingle j) (expSingle i), hsign,
    monomial_neg]

/-- A generator square is the doubled-exponent monomial with coefficient `1`. -/
theorem generator_square {n : ℕ} (i : Fin n) :
    mul (generator i) (generator i)
      = monomial (expSingle i + expSingle i) 1 := by
  rw [mul_generator, skewSign_expSingle]
  simp

/-- Generator squares do not vanish (no exterior square law is imposed). -/
theorem generator_square_ne_zero {n : ℕ} (i : Fin n) :
    mul (generator i) (generator i) ≠ 0 := by
  rw [generator_square]
  exact Finsupp.single_ne_zero.mpr one_ne_zero

/-- Ordered rank-two product coordinate. -/
theorem ordered_rank_two_coordinate :
    (mul (generator (0 : Fin 2)) (generator 1)) ![1, 1] = 1 := by
  rw [mul_generator]
  have hexp : expSingle (0 : Fin 2) + expSingle 1 = ![1, 1] := by decide
  have hsign : OddMath.skewSign (expSingle (0 : Fin 2)) (expSingle 1) = 1 := by
    decide
  rw [hexp, hsign]
  exact Finsupp.single_eq_same

/-- Reversed rank-two product coordinate. -/
theorem reversed_rank_two_coordinate :
    (mul (generator (1 : Fin 2)) (generator 0)) ![1, 1] = -1 := by
  rw [mul_generator]
  have hexp : expSingle (1 : Fin 2) + expSingle 0 = ![1, 1] := by decide
  have hsign : OddMath.skewSign (expSingle (1 : Fin 2)) (expSingle 0) = -1 := by
    decide
  rw [hexp, hsign]
  exact Finsupp.single_eq_same

end OddMath.SkewPolynomial
