/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.Ring.GeomSum

/-!
# The polynomial calculation in the super Serre complex

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 11.2, via Hill–Wang, arXiv:1202.2769v2, Theorem 5.9.
The use of condition (C6) in Hill–Wang's polynomial lemma can be replaced
by the odd-exponent vanishing already included in BE2 (1.6).

The finitely supported functions below record **ordered** monomials
`z^a x^b y^c`. They are coefficient modules, not commutative algebra models
of the odd dots. `serreWindow` retains precisely the exponents not killed
by the two local nilHecke annihilation bounds. The main result computes
this window for arbitrary BE2 parameters. No bar-consistency or relation
between the symmetrizer and parity is assumed. This is the polynomial
input, not a construction of the categorical split exact sequence.
-/

noncomputable section
namespace OddMath.SKM.SerrePolynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Coefficients of ordered monomials `z^a x^b y^c`. -/
abbrev OrderedPolynomial (R : Type*) [Zero R] := (ℕ × ℕ × ℕ) →₀ R

/-- Ordered expansion of the odd braid correction on `u^p v^q`, when `p`
is even. Extending the formula to other exponents is useful for the bounds. -/
def braidTerm (p q : ℕ) : OrderedPolynomial R :=
  ∑ r ∈ Finset.range p, Finsupp.single (p - 1 - r, r, q) ((-1 : R) ^ r)

/-- The two rank-one annihilation bounds at the `k`th interior vertex. -/
def serreWindow (d k : ℕ) (f : OrderedPolynomial R) : OrderedPolynomial R :=
  f.filter fun a => d - k ≤ a.1 ∧ k - 1 ≤ a.2.1

/-- Any term of smaller total outer-dot degree is annihilated. -/
theorem serreWindow_braidTerm_lt {d k p : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d)
    (hp : p < d) (q : ℕ) : serreWindow d k (braidTerm p q : OrderedPolynomial R) = 0 := by
  classical
  unfold serreWindow braidTerm
  rw [Finsupp.filter_sum]
  apply Finset.sum_eq_zero
  intro r hr
  apply Finsupp.filter_single_of_neg
  simp only [Finset.mem_range] at hr
  dsimp
  omega

/-- At the top outer-dot degree exactly one ordered monomial survives. -/
theorem serreWindow_braidTerm_self {d k : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d)
    (q : ℕ) : serreWindow d k (braidTerm d q : OrderedPolynomial R) =
      Finsupp.single (d - k, k - 1, q) ((-1 : R) ^ (k - 1)) := by
  classical
  unfold serreWindow braidTerm
  rw [Finsupp.filter_sum]
  rw [Finset.sum_eq_single (k - 1)]
  · have he : d - 1 - (k - 1) = d - k := by omega
    rw [he]
    apply Finsupp.filter_single_of_pos
    exact ⟨le_rfl, le_rfl⟩
  · intro r hr hne
    apply Finsupp.filter_single_of_neg
    simp only [Finset.mem_range] at hr
    dsimp
    omega
  · intro hn
    exact (hn (Finset.mem_range.mpr (by omega))).elim

variable {I X : Type*} [AddCommGroup X] {D : Datum I X}

/-- The ordered coefficient polynomial in the odd braid correction for BE2.
The full correction is `(-1)^|j|` times this expression; that overall sign
is deliberately not included here. The pure `v` term has zero divided difference. -/
def braidPolynomial (S : Scalars D R) (i j : I) : OrderedPolynomial R :=
  (S.t i j : R) • braidTerm (D.dn i j) 0 +
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      S.s i j p q • braidTerm p q

/-- BE2 Proposition 11.2, polynomial input to Hill–Wang Theorem 5.9:
after the two annihilation bounds only the unit leading coefficient remains.
The bounds use only `p < dᵢⱼ`; homogeneity of the parameters is not needed
for this algebraic calculation. Oddness is needed to identify this expression
with the odd braid relation, not for the coefficient extraction itself. -/
theorem serreWindow_braidPolynomial (S : Scalars D R) (i j : I) {k : ℕ}
    (hk : 1 ≤ k) (hkd : k ≤ D.dn i j) :
    serreWindow (D.dn i j) k (braidPolynomial S i j) =
      Finsupp.single (D.dn i j - k, k - 1, 0)
        ((S.t i j : R) * (-1 : R) ^ (k - 1)) := by
  classical
  unfold braidPolynomial serreWindow
  rw [Finsupp.filter_add, Finsupp.filter_smul]
  rw [show Finsupp.filter (fun a : ℕ × ℕ × ℕ =>
      D.dn i j - k ≤ a.1 ∧ k - 1 ≤ a.2.1) (braidTerm (D.dn i j) 0) =
      Finsupp.single (D.dn i j - k, k - 1, 0) ((-1 : R) ^ (k - 1)) from
    serreWindow_braidTerm_self hk hkd 0]
  have hz : Finsupp.filter (fun a : ℕ × ℕ × ℕ =>
      D.dn i j - k ≤ a.1 ∧ k - 1 ≤ a.2.1)
      (∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        S.s i j p q • (braidTerm p q : OrderedPolynomial R)) = 0 := by
    rw [Finsupp.filter_sum]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finsupp.filter_sum]
    apply Finset.sum_eq_zero
    intro q _
    rw [Finsupp.filter_smul]
    change S.s i j p q • serreWindow (D.dn i j) k (braidTerm p q) = 0
    rw [serreWindow_braidTerm_lt hk hkd (Finset.mem_Ioo.mp hp).2 q, smul_zero]
  rw [hz, add_zero, Finsupp.smul_single]
  rfl

/-- The potentially forbidden exponents vanish directly by BE2 (1.6),
without Hill–Wang's condition (C6). -/
theorem odd_exponent_coefficient_zero (S : Scalars D R) {i : I}
    (hi : D.parity i = 1) (j : I) {p : ℕ} (hp : Odd p) (q : ℕ) :
    S.s i j p q = 0 := by
  apply S.s_eq_zero
  rw [hi, mul_one]
  obtain ⟨m, rfl⟩ := hp
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]

/-- BE2's connected-colour quadratic polynomial evaluated with an explicitly
ordered product. The target may be noncommutative. -/
def quadraticValue {A : Type*} [Ring A] [Module R A]
    (S : Scalars D R) (i j : I) (u v : A) : A :=
  (S.t i j : R) • u ^ D.dn i j + (S.t j i : R) • v ^ D.dn j i +
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      S.s i j p q • (u ^ p * v ^ q)

/-- The admissibility property for which Hill–Wang invokes (C6) follows
instead from BE2 (1.4) and (1.6), for every BE2 parameter family. -/
theorem quadraticValue_neg_left {A : Type*} [Ring A] [Module R A]
    (S : Scalars D R) {i j : I} (hij : i ≠ j) (hi : D.parity i = 1)
    (u v : A) : quadraticValue S i j (-u) v = quadraticValue S i j u v := by
  have hd : Even (D.dn i j) := by
    apply (Int.even_coe_nat _).mp
    rw [D.dn_cast hij]
    exact D.even_d_of_odd hi j
  unfold quadraticValue
  rw [hd.neg_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : Even p
  · rw [hp.neg_pow]
  · rw [odd_exponent_coefficient_zero S hi j (Nat.not_even_iff_odd.mp hp) q]
    simp

/-- The denominator in the odd braid formula denotes a polynomial geometric
sum in the commuting squares, not an inversion in the ground ring. -/
theorem square_difference_factorization {A : Type*} [Ring A] (z x : A)
    (h : Commute (z ^ 2) (x ^ 2)) (m : ℕ) :
    (∑ r ∈ Finset.range m, (z ^ 2) ^ r * (x ^ 2) ^ (m - 1 - r)) *
      (z ^ 2 - x ^ 2) = (z ^ 2) ^ m - (x ^ 2) ^ m := by
  exact h.geom_sum₂_mul m

end OddMath.SKM.SerrePolynomial
