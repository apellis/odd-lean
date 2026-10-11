import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.HahnSeries.Valuation

/-!
# Finite-support q-adic estimates

The order is the actual Laurent-series order at q = 0. The headline
`eval_order_lower` controls polynomial evaluation using all its coefficient
orders, including negative ones. It is used for the Verma polarization limit.
-/

noncomputable section
open scoped LaurentSeries RatFunc
namespace OddMath.CoveringQuantum.QAdic

/-- Order at q = 0, with order zero equal to infinity. -/
def order : AddValuation (RatFunc ℚ) (WithTop ℤ) :=
  (HahnSeries.addVal ℤ ℚ).comap (algebraMap (RatFunc ℚ) (LaurentSeries ℚ))

@[simp] theorem order_X : order (RatFunc.X : RatFunc ℚ) = 1 := by
  change HahnSeries.orderTop ((RatFunc.X : RatFunc ℚ) : LaurentSeries ℚ) = 1
  rw [RatFunc.coe_X, HahnSeries.orderTop_single one_ne_zero]
  rfl

@[simp] theorem order_X_zpow (n : ℤ) : order ((RatFunc.X : RatFunc ℚ) ^ n) = n := by
  change HahnSeries.orderTop (algebraMap (RatFunc ℚ) (LaurentSeries ℚ) (RatFunc.X ^ n)) = n
  rw [map_zpow₀]
  change HahnSeries.orderTop (((RatFunc.X : RatFunc ℚ) : LaurentSeries ℚ) ^ n) = n
  rw [RatFunc.coe_X, ← RatFunc.single_zpow, HahnSeries.orderTop_single one_ne_zero]

/-- The actual (possibly negative) coefficient orders supply a finite lower bound.
Zero coefficients have order infinity and contribute zero to this conservative bound. -/
def coefficientFloor {I R : Type*} [CommRing R] (f : R →+* RatFunc ℚ)
    (P : MvPolynomial I R) : ℤ :=
  - ∑ d ∈ P.support, |(order (f (P.coeff d))).untopD 0|

theorem coefficientFloor_le {I R : Type*} [CommRing R] (f : R →+* RatFunc ℚ)
    (P : MvPolynomial I R) {d : I →₀ ℕ} (hd : d ∈ P.support) :
    (coefficientFloor f P : WithTop ℤ) ≤ order (f (P.coeff d)) := by
  have h : coefficientFloor f P ≤ (order (f (P.coeff d))).untopD 0 := by
    unfold coefficientFloor
    have hs := Finset.single_le_sum (fun e (_ : e ∈ P.support) =>
      abs_nonneg ((order (f (P.coeff e))).untopD 0)) hd
    have ha := neg_abs_le ((order (f (P.coeff d))).untopD 0)
    omega
  exact (WithTop.coe_le_coe.mpr h).trans (WithTop.coe_untopD_le _ _)

private theorem order_prod {J : Type*} (s : Finset J) (a : J → RatFunc ℚ) :
    order (∏ j ∈ s, a j) = ∑ j ∈ s, order (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp [hj, ih]

/-- A positive monomial gains at least B orders when each of its variables has
order at least B >= 0. No coefficient integrality or degree estimate is used. -/
theorem monomial_order_lower {I : Type*} (d : I →₀ ℕ) (hd : d ≠ 0)
    (a : I → RatFunc ℚ) (B : ℤ) (hB : 0 ≤ B)
    (ha : ∀ i ∈ d.support, (B : WithTop ℤ) ≤ order (a i)) :
    (B : WithTop ℤ) ≤ order (∏ i ∈ d.support, a i ^ d i) := by
  classical
  rw [order_prod]
  have hterm (i) (hi : i ∈ d.support) :
      (B : WithTop ℤ) ≤ order (a i ^ d i) := by
    rw [order.map_pow]
    have hi' : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    calc
      (B : WithTop ℤ) ≤ d i • (B : WithTop ℤ) := by
        simpa using nsmul_le_nsmul_left (show (0 : WithTop ℤ) ≤ B by exact_mod_cast hB) hi'
      _ ≤ d i • order (a i) := nsmul_le_nsmul_right (ha i hi) _
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
  exact (hterm i hi).trans (Finset.single_le_sum (fun j hj =>
    (show (0 : WithTop ℤ) ≤ B by exact_mod_cast hB).trans (hterm j hj)) hi)

/-- Explicit finite-coefficient-support q-adic bound. Only variables that actually
occur in the polynomial are constrained. -/
theorem eval_order_lower {I R : Type*} [CommRing R] (f : R →+* RatFunc ℚ)
    (P : MvPolynomial I R) (hP : MvPolynomial.constantCoeff P = 0)
    (a : I → RatFunc ℚ) (N : ℤ)
    (ha : ∀ i ∈ P.vars, (max 0 (N - coefficientFloor f P) : ℤ) ≤ order (a i)) :
    (N : WithTop ℤ) ≤ order (P.eval₂ f a) := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply order.map_le_sum
  intro d hd
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    have hc := MvPolynomial.mem_support_iff.mp hd
    exact hc (by simpa only [MvPolynomial.constantCoeff_eq] using hP)
  have hm := monomial_order_lower d hd0 a (max 0 (N - coefficientFloor f P))
    (le_max_left _ _) (fun i hi => ha i ((MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩))
  rw [order.map_mul]
  calc
    (N : WithTop ℤ) ≤ (coefficientFloor f P : WithTop ℤ) +
        (max 0 (N - coefficientFloor f P) : ℤ) := by
      exact_mod_cast (show N ≤ coefficientFloor f P + max 0 (N - coefficientFloor f P) by omega)
    _ ≤ _ := add_le_add (coefficientFloor_le f P hd) hm

open scoped Topology
open Filter

/-- Comparison with Mathlib's actual X-adic topology on rational functions. -/
theorem valuation_le_of_order_le (r : RatFunc ℚ) (N : ℤ) (h : (N : WithTop ℤ) ≤ order r) :
    Valued.v r ≤ WithZero.exp (-N) := by
  rw [← LaurentSeries.valuation_coe_ratFunc]
  apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero ℚ).mpr
  intro n hn
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  exact (WithTop.coe_lt_coe.mpr hn).trans_le h

/-- Integer lower bounds tending to infinity imply genuine q-adic convergence. -/
theorem tendsto_zero_of_order {A : Type*} {l : Filter A} {f : A → RatFunc ℚ}
    (h : ∀ N : ℤ, ∀ᶠ a in l, (N : WithTop ℤ) ≤ order (f a)) :
    Tendsto f l (𝓝 0) := by
  apply (Valued.hasBasis_nhds_zero (RatFunc ℚ) _).tendsto_right_iff.mpr
  intro γ _
  let g := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
  have hg : g ≠ 0 := by simp [g]
  filter_upwards [h (-WithZero.log g + 1)] with a ha
  apply (Valuation.restrict_lt_iff_lt_embedding _).mpr
  apply (valuation_le_of_order_le (f a) _ ha).trans_lt
  change WithZero.exp (-(-WithZero.log g + 1)) < g
  calc
    _ < WithZero.exp (WithZero.log g) := WithZero.exp_lt_exp.mpr (by omega)
    _ = g := WithZero.exp_log hg

end OddMath.CoveringQuantum.QAdic
