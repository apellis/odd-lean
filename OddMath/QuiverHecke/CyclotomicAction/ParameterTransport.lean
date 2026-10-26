/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.MixedComparison
import OddMath.SKM.Grading
import OddMath.QuiverHecke.CyclotomicAction.SignedMultipliers

/-!
# An involutive transport of the even scalar parameters

Ports the parameter-comparison obligation behind
`Categorification/KLR/CyclotomicAction/MixedComparison.lean` to super scalars.
On the permitted even powers of an odd dot, signed right multiplication changes
`x^(2m)` by `(-1)^m`; two crossing multipliers contribute `(-1)^(|i||j|)`.
The coefficient family below records these signs and is again valid scalar
data. It is involutive and preserves homogeneous support. These coefficient
facts alone do not assert compatibility with the categorical braid or Mackey
map; those are separate relation-transport obligations.
-/
noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The parity sign as a unit of the even coefficient ring. -/
def parameterSignUnit (p : ZMod 2) : kˣ := if p = 1 then -1 else 1

/-- The coefficient sign for a permitted two-dot monomial. -/
def parameterSignExponent (i j : I) (p q : ℕ) : ZMod 2 :=
  D.parity i * D.parity j + D.parity i * (p / 2 : ℕ) + D.parity j * (q / 2 : ℕ)

theorem parameterSignExponent_swap (i j : I) (p q : ℕ) :
    parameterSignExponent D i j p q = parameterSignExponent D j i q p := by
  unfold parameterSignExponent
  ring

/-- Transport the even coefficients while retaining their support conditions. -/
def parameterTwist : SKM.Scalars D k where
  t i j := if i = j then Sc.t i j else
    parameterSignUnit (k := k) (parameterSignExponent D i j (D.dn i j) 0) * Sc.t i j
  t_self i := by simp [Sc.t_self]
  t_symm_of_d_eq_zero i j hd := by
    by_cases hij : i = j
    · subst j; rfl
    have hd' := (D.d_eq_zero_iff i j).mp hd
    simp [hij, Ne.symm hij, parameterSignExponent, SKM.Datum.dn, hd, hd',
      Sc.t_symm_of_d_eq_zero i j hd, mul_comm]
  s i j p q := SKM.zsign k (parameterSignExponent D i j p q) * Sc.s i j p q
  s_symm i j p q := by rw [parameterSignExponent_swap, Sc.s_symm]
  s_eq_zero i j p q hp := by rw [Sc.s_eq_zero i j p q hp, mul_zero]
  two_isUnit := Sc.two_isUnit

/-- Signs do not enlarge the coefficient support, so homogeneity is preserved. -/
theorem parameterTwist_homogeneous (hSc : Sc.Homogeneous) : (parameterTwist D Sc).Homogeneous := by
  intro i j p q hp hp' hq hq' hs
  apply hSc i j p q hp hp' hq hq'
  intro hz
  exact hs (by simp [parameterTwist, hz])

private theorem scalars_ext {S T : SKM.Scalars D k} (ht : S.t = T.t) (hs : S.s = T.s) : S = T := by
  cases S
  cases T
  cases ht
  cases hs
  rfl

/-- The unit signs square to one. -/
theorem parameterSignUnit_square (p : ZMod 2) :
    parameterSignUnit (k := k) p * parameterSignUnit p = 1 := by
  unfold parameterSignUnit
  split_ifs <;> simp

/-- The coefficient transport is its own inverse, also over a non-field base ring. -/
theorem parameterTwist_involutive : parameterTwist D (parameterTwist D Sc) = Sc := by
  apply scalars_ext D
  · funext i j
    by_cases hij : i = j
    · simp [parameterTwist, hij]
    · simp [parameterTwist, hij, ← mul_assoc, parameterSignUnit_square]
  · funext i j p q
    change SKM.zsign k (parameterSignExponent D i j p q) *
      (SKM.zsign k (parameterSignExponent D i j p q) * Sc.s i j p q) = Sc.s i j p q
    rw [← mul_assoc, zsign_mul_self, one_mul]

/-- Every even power of a signed odd right multiplier has the expected half-exponent sign. -/
theorem oddRight_iterate_even {A : Type*} [Ring A] (σ : A →+* A)
    (hσ : Function.Involutive σ) (x : A) (hx : σ x = -x) (m : ℕ) (h : A) :
    (CyclotomicAction.oddRight σ x)^[2 * m] h = (-1 : ℤ) ^ m • (h * x ^ (2 * m)) := by
  induction m generalizing h with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, ih]
    change (-1 : ℤ) ^ m • (CyclotomicAction.oddRight σ x
      (CyclotomicAction.oddRight σ x h) * x ^ (2 * m)) = _
    rw [CyclotomicAction.oddRight_comp σ hσ x x hx]
    simp only [← pow_two, neg_mul, mul_assoc, ← pow_add, smul_neg]
    rw [Nat.add_comm 2 (2 * m)]
    simp [pow_succ]

end OddMath.QuiverHecke
