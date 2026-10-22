/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# `(q, π)`-integers, factorials and binomial coefficients

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2 ([BE2]), §9: for `n ∈ ℤ`,
```
[n]_{q,π} = (qⁿ - (πq)⁻ⁿ) / (q - (πq)⁻¹)
          = q^{n-1} + π q^{n-3} + ⋯ + π^{n-1} q^{1-n}              (n ≥ 0),
          = -πⁿ (q^{-n-1} + π q^{-n-3} + ⋯ + π^{-n-1} q^{1+n})     (n ≤ 0),
```
`[n]!_{q,π} = [n][n-1]⋯[1]`, `[n r]_{q,π} = [n]! / ([r]! [n-r]!)`, and the bar involution
`q ↦ q⁻¹`, `π ↦ π` satisfies (9.1) `bar [n] = π^{n-1} [n] = -π [-n]`, and
`bar [n r] = π^{r(n-r)} [n r]`.

We work over any commutative ring `k`, with a unit `q` and an element `π` (with `π² = 1` where
needed). The quantum integers are defined by the polynomial expressions above (`qpNat`, `qpInt`),
so no division is needed; `qpInt_mul_sub` is the defining quotient formula multiplied out
(with `(πq)⁻¹ = π q⁻¹` when `π² = 1`). The binomial coefficients are defined by a Pascal
recursion (`qpBinom`) and `qpBinom_mul_qpFact` shows `[n r][r]![n-r]! = [n]!`, so they agree with
[BE2]'s quotient whenever the factorials are invertible. The bar involution of a ring is not needed
here: `bar [n]_{q,π} = [n]_{q⁻¹,π}` for any ring map with `q ↦ q⁻¹`, `π ↦ π` (`map_qpInt`), and the
identities (9.1) are stated as `qpInt_inv` and `qpBinom_inv`.

## Main definitions

* `qpNat q π n`, `qpInt q π n`: `[n]_{q,π}` for `n ∈ ℕ`, `n ∈ ℤ`.
* `qpFact q π n`: `[n]!_{q,π}`; `qpBinom q π n r`: `[n r]_{q,π}`.

## Main results

* `qpNat_mul_sub`, `qpInt_mul_sub`: `(q - π q⁻¹) [n] = qⁿ - πⁿ q⁻ⁿ`.
* `qpNat_add`: `[m + n] = πⁿ q⁻ⁿ [m] + qᵐ [n]`.
* `qpInt_neg`: `[-n] = -π^{|n|} [n]`; `qpInt_inv`, `qpInt_inv_eq_neg`: (9.1); `qpFact_inv`.
* `qpBinom_mul_qpFact`, `qpBinom_symm`, `qpBinom_succ_succ'` (second Pascal rule),
  `qpBinom_inv` (`bar [n r] = π^{r(n-r)} [n r]`).
-/

namespace OddMath.CoveringQuantum

open Finset

variable {k : Type*} [CommRing k] (q : kˣ) (π : k)

/-- The `(q, π)`-integer `[n]_{q,π} = Σ_{s < n} πˢ q^{n-1-s} q^{-s}` for `n ∈ ℕ` ([BE2] §9). -/
def qpNat (n : ℕ) : k := ∑ s ∈ range n, π ^ s * (q : k) ^ (n - 1 - s) * ((q⁻¹ : kˣ) : k) ^ s

/-- The `(q, π)`-integer `[n]_{q,π}` for `n ∈ ℤ` ([BE2] §9): `[-m] = -πᵐ [m]` for `m > 0`. -/
def qpInt : ℤ → k
  | .ofNat n => qpNat q π n
  | .negSucc n => -(π ^ (n + 1) * qpNat q π (n + 1))

/-- The `(q, π)`-factorial `[n]!_{q,π} = [1][2]⋯[n]`. -/
def qpFact : ℕ → k
  | 0 => 1
  | n + 1 => qpNat q π (n + 1) * qpFact n

/-- The `(q, π)`-binomial coefficient `[n r]_{q,π}`, by the Pascal rule
`[n+1, r+1] = π^{r+1} q^{-(r+1)} [n, r+1] + q^{n-r} [n, r]`; `[n r] [r]! [n-r]! = [n]!`
(`qpBinom_mul_qpFact`). -/
def qpBinom : ℕ → ℕ → k
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, r + 1 =>
      π ^ (r + 1) * ((q⁻¹ : kˣ) : k) ^ (r + 1) * qpBinom n (r + 1) + (q : k) ^ (n - r) * qpBinom n r

variable {q π}

local notation "Q" => (q : k)
local notation "Qi" => ((q⁻¹ : kˣ) : k)

lemma q_mul_qinv : Q * Qi = 1 := q.mul_inv

private lemma pow_eq_pow_of_mod (hπ : π ^ 2 = 1) {a b : ℕ} (h : a % 2 = b % 2) : π ^ a = π ^ b := by
  rw [← Nat.div_add_mod a 2, ← Nat.div_add_mod b 2, pow_add, pow_add, pow_mul, pow_mul, hπ,
    one_pow, one_pow, h]

private lemma pow_mul_self (hπ : π ^ 2 = 1) (n : ℕ) : π ^ n * π ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, hπ, one_pow]

@[simp] lemma qpNat_zero : qpNat q π 0 = 0 := by simp [qpNat]

@[simp] lemma qpNat_one : qpNat q π 1 = 1 := by simp [qpNat]

/-- `[n+1] = qⁿ + π q⁻¹ [n]`. -/
lemma qpNat_succ (n : ℕ) : qpNat q π (n + 1) = Q ^ n + π * Qi * qpNat q π n := by
  rw [qpNat, sum_range_succ', qpNat, mul_sum]
  simp only [pow_zero, one_mul, mul_one, Nat.add_sub_cancel, Nat.sub_zero]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun s hs ↦ ?_
  have : n - (s + 1) = n - 1 - s := by omega
  rw [this]; ring

/-- `[n+1] = q [n] + πⁿ q⁻ⁿ`. -/
lemma qpNat_succ' (n : ℕ) : qpNat q π (n + 1) = Q * qpNat q π n + π ^ n * Qi ^ n := by
  rw [qpNat, sum_range_succ, qpNat, mul_sum]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
  congr 1
  refine sum_congr rfl fun s hs ↦ ?_
  have : n - s = n - 1 - s + 1 := by have := mem_range.1 hs; omega
  rw [this, pow_succ]; ring

/-- `(q - π q⁻¹) [n] = qⁿ - πⁿ q⁻ⁿ` ([BE2] §9, the defining quotient multiplied out). -/
theorem qpNat_mul_sub (n : ℕ) : (Q - π * Qi) * qpNat q π n = Q ^ n - π ^ n * Qi ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qpNat_succ', mul_add, ← mul_assoc, mul_comm _ Q, mul_assoc, ih]
    ring

/-- `[m + n] = πⁿ q⁻ⁿ [m] + qᵐ [n]`. -/
theorem qpNat_add (m n : ℕ) :
    qpNat q π (m + n) = π ^ n * Qi ^ n * qpNat q π m + Q ^ m * qpNat q π n := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := (qpNat_succ (q := q) (π := π) n).symm.trans (qpNat_succ' n)
    rw [show m + 1 + n = (m + n) + 1 by omega, qpNat_succ, ih, qpNat_succ m]
    linear_combination Q ^ m * h

lemma qpNat_two : qpNat q π 2 = Q + π * Qi := by
  rw [qpNat_succ, qpNat_one]; ring

@[simp] lemma qpInt_ofNat (n : ℕ) : qpInt q π n = qpNat q π n := rfl

@[simp] lemma qpInt_negSucc (n : ℕ) :
    qpInt q π (Int.negSucc n) = -(π ^ (n + 1) * qpNat q π (n + 1)) := rfl

@[simp] lemma qpInt_zero : qpInt q π 0 = 0 := qpNat_zero

lemma qpInt_neg_natCast (n : ℕ) : qpInt q π (-(n : ℤ)) = -(π ^ n * qpNat q π n) := by
  cases n with
  | zero => simp
  | succ n => rfl

/-- `[-n] = -π^{|n|} [n]` ([BE2] §9, given `π² = 1`). -/
theorem qpInt_neg (hπ : π ^ 2 = 1) (n : ℤ) : qpInt q π (-n) = -(π ^ n.natAbs * qpInt q π n) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simp [qpInt_neg_natCast]
  · rw [neg_neg, Int.natAbs_neg, Int.natAbs_natCast, qpInt_neg_natCast, qpInt_ofNat]
    linear_combination (-qpNat q π m) * pow_mul_self hπ m

/-- The quotient formula for negative arguments: `(q - π q⁻¹) [-n] = q⁻ⁿ - πⁿ qⁿ` for `n ∈ ℕ`,
given `π² = 1`. -/
theorem qpInt_neg_mul_sub (hπ : π ^ 2 = 1) (n : ℕ) :
    (Q - π * Qi) * qpInt q π (-(n : ℤ)) = Qi ^ n - π ^ n * Q ^ n := by
  rw [qpInt_neg_natCast, mul_neg, mul_left_comm, qpNat_mul_sub]
  linear_combination Qi ^ n * pow_mul_self hπ n

/-- `[n]_{q⁻¹,π} = π^{n-1} [n]_{q,π}` for `n ≥ 1`, given `π² = 1`. -/
theorem qpNat_inv (hπ : π ^ 2 = 1) (n : ℕ) :
    qpNat q⁻¹ π (n + 1) = π ^ n * qpNat q π (n + 1) := by
  rw [qpNat, qpNat, mul_sum]
  conv_rhs => rw [← sum_range_reflect]
  refine sum_congr rfl fun s hs ↦ ?_
  have hs := mem_range.1 hs
  simp only [inv_inv, Nat.add_sub_cancel]
  rw [show n - (n - s) = s by omega]
  have h1 : π ^ n = π ^ (n - s) * π ^ s := by rw [← pow_add]; congr 1; omega
  rw [h1]
  linear_combination (-(π ^ s * Q ^ s * Qi ^ (n - s))) * pow_mul_self hπ (n - s)

/-- [BE2] (9.1), first equality, in the form `[n]_{q⁻¹,π} = π^{n-1} [n]_{q,π}` for `n ∈ ℤ`
(the exponent `n - 1` read mod 2, i.e. `π^{|n-1|}`), given `π² = 1`. -/
theorem qpInt_inv (hπ : π ^ 2 = 1) (n : ℤ) :
    qpInt q⁻¹ π n = π ^ (n - 1).natAbs * qpInt q π n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rcases m with _ | m
    · simp
    · rw [qpInt_ofNat, qpInt_ofNat, qpNat_inv hπ,
        show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) by push_cast; ring, Int.natAbs_natCast]
  · rcases m with _ | m
    · simp
    · rw [qpInt_neg_natCast, qpInt_neg_natCast, qpNat_inv hπ,
        show -((m + 1 : ℕ) : ℤ) - 1 = -((m + 2 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_neg,
        Int.natAbs_natCast, pow_eq_pow_of_mod hπ (show (m + 2) % 2 = m % 2 by omega)]
      ring

/-- [BE2] (9.1), second equality: `π^{n-1} [n] = -π [-n]`, given `π² = 1`. -/
theorem qpInt_inv_eq_neg (hπ : π ^ 2 = 1) (n : ℤ) :
    qpInt q⁻¹ π n = -(π * qpInt q π (-n)) := by
  rw [qpInt_inv hπ, qpInt_neg hπ, mul_neg, neg_neg, ← mul_assoc, ← pow_succ']
  congr 1
  apply pow_eq_pow_of_mod hπ
  omega

/-- Ring homomorphisms commute with `(q, π)`-integers. -/
theorem map_qpNat {k' : Type*} [CommRing k'] (f : k →+* k') (n : ℕ) :
    f (qpNat q π n) = qpNat (Units.map f.toMonoidHom q) (f π) n := by
  simp [qpNat, map_sum, map_mul, map_pow, Units.coe_map, Units.coe_map_inv]

theorem map_qpInt {k' : Type*} [CommRing k'] (f : k →+* k') (n : ℤ) :
    f (qpInt q π n) = qpInt (Units.map f.toMonoidHom q) (f π) n := by
  cases n <;> simp [map_qpNat]

/-! ### Factorials and binomial coefficients -/

@[simp] lemma qpFact_zero : qpFact q π 0 = 1 := rfl

lemma qpFact_succ (n : ℕ) : qpFact q π (n + 1) = qpNat q π (n + 1) * qpFact q π n := rfl

/-- Ring homomorphisms commute with `(q, π)`-factorials. -/
theorem map_qpFact {k' : Type*} [CommRing k'] (f : k →+* k') (n : ℕ) :
    f (qpFact q π n) = qpFact (Units.map f.toMonoidHom q) (f π) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [qpFact_succ, qpFact_succ, map_mul, ih, map_qpNat]

/-- `[n]!_{q⁻¹,π} = π^{n(n-1)/2} [n]!_{q,π}`, given `π² = 1`. -/
theorem qpFact_inv (hπ : π ^ 2 = 1) (n : ℕ) :
    qpFact q⁻¹ π n = π ^ n.choose 2 * qpFact q π n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qpFact_succ, qpFact_succ, qpNat_inv hπ, ih, Nat.choose_succ_succ', Nat.choose_one_right,
      pow_add]
    ring

@[simp] lemma qpBinom_zero_right (n : ℕ) : qpBinom q π n 0 = 1 := by cases n <;> rfl

@[simp] lemma qpBinom_zero_succ (r : ℕ) : qpBinom q π 0 (r + 1) = 0 := rfl

lemma qpBinom_succ_succ (n r : ℕ) : qpBinom q π (n + 1) (r + 1) =
    π ^ (r + 1) * Qi ^ (r + 1) * qpBinom q π n (r + 1) + Q ^ (n - r) * qpBinom q π n r := rfl

lemma qpBinom_eq_zero_of_lt {n r : ℕ} (h : n < r) : qpBinom q π n r = 0 := by
  induction n generalizing r with
  | zero => obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0); rfl
  | succ n ih =>
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    rw [qpBinom_succ_succ, ih (by omega), ih (by omega)]; ring

@[simp] lemma qpBinom_self (n : ℕ) : qpBinom q π n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [qpBinom_succ_succ, qpBinom_eq_zero_of_lt (by omega), ih]; simp

lemma qpBinom_one_right (n : ℕ) : qpBinom q π n 1 = qpNat q π n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [qpBinom_succ_succ, ih, qpBinom_zero_right, qpNat_succ]
    simp only [Nat.sub_zero, zero_add, pow_one, mul_one]; ring

/-- `[n r] [r]! [n-r]! = [n]!` for `r ≤ n`, so `[n r]` is [BE2]'s quotient whenever the
factorials are invertible. -/
theorem qpBinom_mul_qpFact {n r : ℕ} (h : r ≤ n) :
    qpBinom q π n r * qpFact q π r * qpFact q π (n - r) = qpFact q π n := by
  induction n generalizing r with
  | zero =>
    obtain rfl : r = 0 := by omega
    simp
  | succ n ih =>
    rcases r with _ | r
    · simp
    rcases Nat.lt_or_ge n (r + 1) with hr | hr
    · obtain rfl : r = n := by omega
      simp
    obtain ⟨m, rfl⟩ : ∃ m, n = r + 1 + m := ⟨n - (r + 1), by omega⟩
    have hp : qpBinom q π (r + 1 + m + 1) (r + 1) = π ^ (r + 1) * Qi ^ (r + 1) *
        qpBinom q π (r + 1 + m) (r + 1) + Q ^ (m + 1) * qpBinom q π (r + 1 + m) r := by
      rw [qpBinom_succ_succ, show r + 1 + m - r = m + 1 by omega]
    have e1 := ih (r := r + 1) (by omega)
    rw [show r + 1 + m - (r + 1) = m by omega, qpFact_succ r] at e1
    have e2 := ih (r := r) (by omega)
    rw [show r + 1 + m - r = m + 1 by omega, qpFact_succ m] at e2
    have hadd := qpNat_add (q := q) (π := π) (m + 1) (r + 1)
    rw [show m + 1 + (r + 1) = r + 1 + m + 1 by omega] at hadd
    rw [show r + 1 + m + 1 - (r + 1) = m + 1 by omega, qpFact_succ r, qpFact_succ m,
      qpFact_succ (r + 1 + m)]
    linear_combination (qpNat q π (r + 1) * qpFact q π r * qpNat q π (m + 1) * qpFact q π m) * hp +
      (π ^ (r + 1) * Qi ^ (r + 1) * qpNat q π (m + 1)) * e1 +
      (Q ^ (m + 1) * qpNat q π (r + 1)) * e2 - qpFact q π (r + 1 + m) * hadd

/-- The second Pascal rule `[n+1, r+1] = q^{r+1} [n, r+1] + π^{n-r} q^{-(n-r)} [n, r]`. -/
theorem qpBinom_succ_succ' (n r : ℕ) : qpBinom q π (n + 1) (r + 1) =
    Q ^ (r + 1) * qpBinom q π n (r + 1) + π ^ (n - r) * Qi ^ (n - r) * qpBinom q π n r := by
  induction n generalizing r with
  | zero =>
    rcases r with _ | r
    · simp
    · simp [qpBinom_eq_zero_of_lt]
  | succ n ih =>
    rcases r with _ | s
    · rw [qpBinom_one_right, qpBinom_one_right, qpBinom_zero_right, qpNat_succ' (n + 1)]
      simp only [Nat.sub_zero, zero_add, pow_one, mul_one]
    rcases Nat.lt_or_ge n (s + 1) with hs | hs
    · rcases Nat.lt_or_ge n s with hs' | hs'
      · rw [qpBinom_eq_zero_of_lt (by omega : n + 1 + 1 < s + 1 + 1),
          qpBinom_eq_zero_of_lt (by omega : n + 1 < s + 1 + 1),
          qpBinom_eq_zero_of_lt (by omega : n + 1 < s + 1)]
        ring
      · obtain rfl : s = n := by omega
        rw [qpBinom_self, qpBinom_self, qpBinom_eq_zero_of_lt (by omega : s + 1 < s + 1 + 1),
          Nat.sub_self]
        ring
    obtain ⟨m, rfl⟩ : ∃ m, n = s + 1 + m := ⟨n - (s + 1), by omega⟩
    have p1 : qpBinom q π (s + 1 + m + 1 + 1) (s + 1 + 1) = π ^ (s + 2) * Qi ^ (s + 2) *
        qpBinom q π (s + 1 + m + 1) (s + 1 + 1) + Q ^ (m + 1) * qpBinom q π (s + 1 + m + 1) (s + 1) := by
      rw [qpBinom_succ_succ, show s + 1 + m + 1 - (s + 1) = m + 1 by omega]
    have p2 : qpBinom q π (s + 1 + m + 1) (s + 1 + 1) = π ^ (s + 2) * Qi ^ (s + 2) *
        qpBinom q π (s + 1 + m) (s + 1 + 1) + Q ^ m * qpBinom q π (s + 1 + m) (s + 1) := by
      rw [qpBinom_succ_succ, show s + 1 + m - (s + 1) = m by omega]
    have p3 : qpBinom q π (s + 1 + m + 1) (s + 1) = π ^ (s + 1) * Qi ^ (s + 1) *
        qpBinom q π (s + 1 + m) (s + 1) + Q ^ (m + 1) * qpBinom q π (s + 1 + m) s := by
      rw [qpBinom_succ_succ, show s + 1 + m - s = m + 1 by omega]
    have i1 := ih (s + 1)
    rw [show s + 1 + m - (s + 1) = m by omega] at i1
    have i2 := ih s
    rw [show s + 1 + m - s = m + 1 by omega] at i2
    rw [show s + 1 + m + 1 - (s + 1) = m + 1 by omega]
    linear_combination p1 + (π ^ (s + 2) * Qi ^ (s + 2)) * i1 + Q ^ (m + 1) * i2 -
      Q ^ (s + 2) * p2 - (π ^ (m + 1) * Qi ^ (m + 1)) * p3

/-- The symmetry `[n, n-r] = [n, r]` for `r ≤ n`. -/
theorem qpBinom_symm {n r : ℕ} (h : r ≤ n) : qpBinom q π n (n - r) = qpBinom q π n r := by
  induction n generalizing r with
  | zero => obtain rfl : r = 0 := by omega
            rfl
  | succ n ih =>
    rcases r with _ | s
    · simp
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [h', Nat.sub_self, qpBinom_zero_right, qpBinom_self]
    obtain ⟨t, ht⟩ : ∃ t, n - s = t + 1 := ⟨n - s - 1, by omega⟩
    rw [show n + 1 - (s + 1) = t + 1 by omega, qpBinom_succ_succ', qpBinom_succ_succ,
      show n - t = s + 1 by omega, ← ht, ih (by omega : s ≤ n),
      show t = n - (s + 1) by omega, ih (by omega : s + 1 ≤ n)]
    ring

/-- `bar [n r] = π^{r(n-r)} [n r]` ([BE2] §9), in the form
`[n r]_{q⁻¹,π} = π^{r(n-r)} [n r]_{q,π}`, given `π² = 1`. -/
theorem qpBinom_inv (hπ : π ^ 2 = 1) (n r : ℕ) :
    qpBinom q⁻¹ π n r = π ^ (r * (n - r)) * qpBinom q π n r := by
  induction n generalizing r with
  | zero => rcases r with _ | r <;> simp
  | succ n ih =>
    rcases r with _ | r
    · simp
    rcases Nat.lt_or_ge n (r + 1) with hr | hr
    · rcases Nat.lt_or_ge n r with hr' | hr'
      · rw [qpBinom_eq_zero_of_lt (by omega), qpBinom_eq_zero_of_lt (by omega), mul_zero]
      · obtain rfl : r = n := by omega
        simp
    obtain ⟨m, rfl⟩ : ∃ m, n = r + 1 + m := ⟨n - (r + 1), by omega⟩
    have hp := qpBinom_succ_succ (q := q⁻¹) (π := π) (r + 1 + m) r
    simp only [inv_inv] at hp
    rw [show r + 1 + m - r = m + 1 by omega] at hp
    have hs := qpBinom_succ_succ' (q := q) (π := π) (r + 1 + m) r
    rw [show r + 1 + m - r = m + 1 by omega] at hs
    have i1 := ih (r + 1)
    rw [show r + 1 + m - (r + 1) = m by omega] at i1
    have i2 := ih r
    rw [show r + 1 + m - r = m + 1 by omega] at i2
    have hpow : π ^ (r * (m + 1)) = π ^ ((r + 1) * (m + 1)) * π ^ (m + 1) := by
      rw [← pow_add]
      refine pow_eq_pow_of_mod hπ ?_
      rw [show (r + 1) * (m + 1) + (m + 1) = r * (m + 1) + 2 * (m + 1) by ring,
        Nat.add_mul_mod_self_left]
    rw [show r + 1 + m + 1 - (r + 1) = m + 1 by omega]
    linear_combination hp + (π ^ (r + 1) * Q ^ (r + 1)) * i1 + Qi ^ (m + 1) * i2 -
      π ^ ((r + 1) * (m + 1)) * hs + (qpBinom q π (r + 1 + m) r * Qi ^ (m + 1)) * hpow

/-- For `n` odd, `[n r]_{q,π}` is invariant under `q ↦ q⁻¹` ([BE2] §9). -/
theorem qpBinom_inv_of_odd (hπ : π ^ 2 = 1) {n : ℕ} (hn : Odd n) (r : ℕ) :
    qpBinom q⁻¹ π n r = qpBinom q π n r := by
  rcases Nat.lt_or_ge n r with h | h
  · rw [qpBinom_eq_zero_of_lt h, qpBinom_eq_zero_of_lt h]
  rw [qpBinom_inv hπ, pow_eq_pow_of_mod hπ (b := 0), pow_zero, one_mul]
  obtain ⟨m, rfl⟩ := hn
  rcases Nat.even_or_odd r with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [show 2 * m + 1 - (a + a) = 2 * (m - a) + 1 by omega]
    rw [Nat.mul_mod, show (a + a) % 2 = 0 by omega]; simp
  · rw [show 2 * m + 1 - (2 * a + 1) = 2 * (m - a) by omega, Nat.mul_mod,
      show 2 * (m - a) % 2 = 0 by omega]; simp

end OddMath.CoveringQuantum
