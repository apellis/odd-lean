/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BWWScalars
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# The Brundan–Wang–Webster polynomials `Qᵢⱼ` on purely even data

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2, (2.6) and (2.7): for a Cartan
datum (purely even) and a commutative ring `k`, polynomials `Qᵢⱼ(x, y) ∈ k[x, y]` with
`Qᵢᵢ = 0`, `Qᵢⱼ(x, y) = Qⱼᵢ(y, x)`, and for `i ≠ j`

    Qᵢⱼ(x, y) = tᵢⱼ x^{dᵢⱼ} + Σ_{0 ≤ r < dᵢⱼ, 0 ≤ s < dⱼᵢ} tᵢⱼ;ᵣₛ x^r y^s + tⱼᵢ y^{dⱼᵢ},

with `tᵢⱼ` a unit. Here `dᵢⱼ = -aᵢⱼ`. This file compares these polynomials with
`SKM.BWWScalars`, the encoding of the same parameters by the coefficient function
`c i j p q` (the coefficient of `u^p v^q`).

* `BWWPolynomials D k`: the polynomials, as elements of `MvPolynomial (Fin 2) k` with
  `x = X 0`, `y = X 1`. The shape (2.7) is a support condition (`support`); the leading
  coefficient `tᵢⱼ` of `x^{dᵢⱼ}` is a unit (`isUnit_lead`).
* `BWWPolynomials.toBWWScalars`: on purely even data, the coefficient function of the
  polynomials, with `tᵢⱼ` the coefficient of `x^{dᵢⱼ}`.
* `BWWScalars.toPolynomials`: the polynomial with coefficients `c i j p q` on the box
  `[0, dᵢⱼ] × [0, dⱼᵢ]`. It needs no parity hypothesis.
* `bwwPolynomialsEquiv`: on purely even data the two encodings are equivalent.
* `BWWPolynomials.eq_form`: each `Qᵢⱼ` for `i ≠ j` with `dᵢⱼ ≠ 0` has the form (2.7), with
  `tᵢⱼ;ᵣₛ = c i j r s`, and `Qᵢⱼ = tᵢⱼ` when `dᵢⱼ = 0` (`eq_const`).

The pure terms of Brundan–Wang–Webster, the monomials `x^r`, `y^s` and `1` with `r < dᵢⱼ`,
`s < dⱼᵢ`, are the coefficients `c i j r 0` and `c i j 0 s`.

**Convention at `dᵢⱼ = 0`.** Read literally, (2.7) with `aᵢⱼ = 0` gives the constant
`tᵢⱼ + tⱼᵢ`. Brundan–Wang–Webster define `tᵢⱼ := Qᵢⱼ(1, 0)` (§3, before Theorem 3.5); for
`aᵢⱼ = 0` this is the constant `Qᵢⱼ` itself, which must be a unit. The structure below uses
that reading: `Qᵢⱼ` is the unit constant `tᵢⱼ = tⱼᵢ`, as in Brundan–Ellis (1.3).
-/

noncomputable section

namespace OddMath.SKM

open MvPolynomial

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
variable {k : Type w} [CommRing k]

/-- The exponent of `x^p y^q` in `k[x, y] = MvPolynomial (Fin 2) k`. -/
def bwwExp (p q : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 p + Finsupp.single 1 q

@[simp] theorem bwwExp_zero (p q : ℕ) : bwwExp p q 0 = p := by simp [bwwExp]

@[simp] theorem bwwExp_one (p q : ℕ) : bwwExp p q 1 = q := by simp [bwwExp]

theorem eq_bwwExp (m : Fin 2 →₀ ℕ) : m = bwwExp (m 0) (m 1) := by
  ext a
  fin_cases a <;> simp

theorem bwwExp_inj {p q p' q' : ℕ} : bwwExp p q = bwwExp p' q' ↔ p = p' ∧ q = q' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (· 0) h, by simpa using congrArg (· 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The exchange of the two variables. -/
abbrev bwwSwap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

theorem mapDomain_bwwSwap (p q : ℕ) : (bwwExp q p).mapDomain bwwSwap = bwwExp p q := by
  simp only [bwwExp, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  rw [show bwwSwap 0 = 1 from rfl, show bwwSwap 1 = 0 from rfl, add_comm]

/-- The coefficient of `x^p y^q` in `f(y, x)` is the coefficient of `x^q y^p` in `f(x, y)`. -/
theorem coeff_rename_bwwSwap (f : MvPolynomial (Fin 2) k) (p q : ℕ) :
    (rename bwwSwap f).coeff (bwwExp p q) = f.coeff (bwwExp q p) := by
  rw [← mapDomain_bwwSwap, coeff_rename_mapDomain _ bwwSwap.injective]

/-- The coefficient of `x^a y^b` in a sum of monomials over the box `[0, A) × [0, B)`. -/
theorem coeff_boxSum (A B : ℕ) (f : ℕ → ℕ → k) (a b : ℕ) :
    (∑ p ∈ Finset.range A, ∑ q ∈ Finset.range B, monomial (bwwExp p q) (f p q) :
      MvPolynomial (Fin 2) k).coeff (bwwExp a b) = if a < A ∧ b < B then f a b else 0 := by
  simp only [coeff_sum, coeff_monomial, bwwExp_inj, ite_and]
  simp [Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.mem_range]

/-- The polynomials `Qᵢⱼ(x, y)` of Brundan–Wang–Webster §2.2 for the Cartan datum of `D`,
without the grading: (2.6), the shape (2.7) and the unit leading coefficients. -/
structure BWWPolynomials (D : Datum I X) (k : Type w) [CommRing k] where
  /-- `Qᵢⱼ(x, y)`, with `x = X 0` and `y = X 1`. -/
  Q : I → I → MvPolynomial (Fin 2) k
  Q_self : ∀ i, Q i i = 0
  /-- (2.6): `Qⱼᵢ(x, y) = Qᵢⱼ(y, x)`. -/
  Q_swap : ∀ i j, Q j i = rename bwwSwap (Q i j)
  /-- The shape (2.7): monomials `x^p y^q` in the box `[0, dᵢⱼ] × [0, dⱼᵢ]`, with only the
  corners `x^{dᵢⱼ}` and `y^{dⱼᵢ}` on its top and right edges. -/
  support : ∀ i j (p q : ℕ), (Q i j).coeff (bwwExp p q) ≠ 0 →
    (p ≤ D.dn i j ∧ q ≤ D.dn j i) ∧ (p = D.dn i j → q = 0) ∧ (q = D.dn j i → p = 0)
  /-- `tᵢⱼ`, the coefficient of `x^{dᵢⱼ}`, is a unit. -/
  isUnit_lead : ∀ i j, i ≠ j → IsUnit ((Q i j).coeff (bwwExp (D.dn i j) 0))

namespace BWWPolynomials

variable (P : BWWPolynomials D k)

@[ext]
theorem ext {P P' : BWWPolynomials D k} (h : P.Q = P'.Q) : P = P' := by
  cases P; cases P'; cases h; rfl

theorem coeff_symm (i j : I) (p q : ℕ) :
    (P.Q i j).coeff (bwwExp p q) = (P.Q j i).coeff (bwwExp q p) := by
  rw [P.Q_swap i j, coeff_rename_bwwSwap]

/-- The unit `tᵢⱼ`: the coefficient of `x^{dᵢⱼ}` in `Qᵢⱼ` for `i ≠ j`, and `1` for `i = j`. -/
def t (i j : I) : kˣ :=
  haveI := Classical.propDecidable (i = j)
  if h : i = j then 1 else (P.isUnit_lead i j h).unit

theorem t_of_ne {i j : I} (h : i ≠ j) :
    ((P.t i j : kˣ) : k) = (P.Q i j).coeff (bwwExp (D.dn i j) 0) := by
  simp [t, h]

/-- On purely even data, the coefficient function of the polynomials `Qᵢⱼ`. -/
def toBWWScalars (hD : ∀ i, D.parity i = 0) : BWWScalars D k where
  t := P.t
  t_self i := by simp [t]
  t_symm_of_d_eq_zero i j hd := by
    by_cases hij : i = j
    · subst hij; rfl
    have h1 : D.dn i j = 0 := by simp [Datum.dn, hd]
    have h2 : D.dn j i = 0 := (ScalarData.dn_eq_zero_iff i j).mp h1
    apply Units.ext
    rw [P.t_of_ne hij, P.t_of_ne (Ne.symm hij), h1, h2, P.coeff_symm]
  c i j p q := (P.Q i j).coeff (bwwExp p q)
  c_symm i j p q := P.coeff_symm i j p q
  c_parity i j p q h := by
    rw [hD i, mul_zero] at h
    exact absurd h (by decide)
  c_self i p q := by rw [P.Q_self]; simp
  c_corner i j hij := (P.t_of_ne hij).symm
  c_outside i j p q h := by
    by_contra hc
    have := (P.support i j p q hc).1
    omega
  c_top i j q hq := by
    by_contra hc
    have := (P.support i j _ q hc).2.1 rfl
    omega
  two_isUnit h := by
    obtain ⟨i, hi⟩ := h
    rw [hD i] at hi
    exact absurd hi (by decide)

@[simp] theorem toBWWScalars_t (hD : ∀ i, D.parity i = 0) : (P.toBWWScalars hD).t = P.t := rfl

theorem toBWWScalars_c (hD : ∀ i, D.parity i = 0) (i j : I) (p q : ℕ) :
    (P.toBWWScalars hD).c i j p q = (P.Q i j).coeff (bwwExp p q) := rfl

end BWWPolynomials

namespace BWWScalars

variable (Sc : BWWScalars D k)

/-- The polynomial `Σ_{p ≤ dᵢⱼ, q ≤ dⱼᵢ} c i j p q x^p y^q`. -/
def poly (i j : I) : MvPolynomial (Fin 2) k :=
  ∑ p ∈ Finset.range (D.dn i j + 1), ∑ q ∈ Finset.range (D.dn j i + 1),
    monomial (bwwExp p q) (Sc.c i j p q)

theorem coeff_poly (i j : I) (a b : ℕ) : (Sc.poly i j).coeff (bwwExp a b) = Sc.c i j a b := by
  rw [poly, coeff_boxSum]
  split_ifs with h
  · rfl
  · exact (Sc.c_outside i j a b (by omega)).symm

/-- The polynomials `Qᵢⱼ` of the coefficient function. No parity hypothesis is needed. -/
def toPolynomials : BWWPolynomials D k where
  Q := Sc.poly
  Q_self i := by
    ext m
    rw [eq_bwwExp m, coeff_poly, Sc.c_self]; simp
  Q_swap i j := by
    ext m
    rw [eq_bwwExp m, coeff_poly, coeff_rename_bwwSwap, coeff_poly, Sc.c_symm]
  support i j p q h := by
    rw [coeff_poly] at h
    refine ⟨?_, fun hp => ?_, fun hq => ?_⟩
    · by_contra h'
      exact h (Sc.c_outside i j p q (by omega))
    · by_contra h'
      exact h (hp ▸ Sc.c_top i j q (by omega))
    · by_contra h'
      exact h (hq ▸ Sc.c_right i j (by omega))
  isUnit_lead i j hij := by
    rw [coeff_poly, Sc.c_corner i j hij]
    exact (Sc.t i j).isUnit

@[simp] theorem toPolynomials_Q : Sc.toPolynomials.Q = Sc.poly := rfl

end BWWScalars

/-- **The even dictionary.** On purely even data, the polynomials `Qᵢⱼ` of
Brundan–Wang–Webster §2.2 are equivalent to the coefficient functions `BWWScalars`: the
coefficient of `x^p y^q` in `Qᵢⱼ` is `c i j p q`, and `tᵢⱼ` is the coefficient of
`x^{dᵢⱼ}`. -/
def bwwPolynomialsEquiv (hD : ∀ i, D.parity i = 0) : BWWPolynomials D k ≃ BWWScalars D k where
  toFun P := P.toBWWScalars hD
  invFun Sc := Sc.toPolynomials
  left_inv P := by
    ext i j m
    rw [eq_bwwExp m]
    exact BWWScalars.coeff_poly _ i j _ _
  right_inv Sc := by
    refine BWWScalars.ext ?_ ?_
    · funext i j
      by_cases hij : i = j
      · subst hij
        simp [BWWPolynomials.t, Sc.t_self]
      · apply Units.ext
        change ((Sc.toPolynomials.t i j : kˣ) : k) = Sc.t i j
        rw [BWWPolynomials.t_of_ne _ hij, BWWScalars.toPolynomials_Q, BWWScalars.coeff_poly,
          Sc.c_corner i j hij]
    · funext i j p q
      exact BWWScalars.coeff_poly Sc i j p q

namespace BWWPolynomials

variable (P : BWWPolynomials D k)

/-- Each `Qᵢⱼ` is the polynomial of its coefficients on the box. -/
theorem Q_eq_poly (hD : ∀ i, D.parity i = 0) (i j : I) :
    P.Q i j = (P.toBWWScalars hD).poly i j := by
  have := congrArg (fun P' => P'.Q i j) ((bwwPolynomialsEquiv (k := k) hD).left_inv P)
  exact this.symm

/-- **(2.7).** For `i ≠ j` with `dᵢⱼ ≠ 0`,
`Qᵢⱼ(x, y) = tᵢⱼ x^{dᵢⱼ} + Σ_{r < dᵢⱼ, s < dⱼᵢ} tᵢⱼ;ᵣₛ x^r y^s + tⱼᵢ y^{dⱼᵢ}`, where
`tᵢⱼ;ᵣₛ` is the coefficient of `x^r y^s`. -/
theorem eq_form {i j : I} (hij : i ≠ j) (hd : D.dn i j ≠ 0) :
    P.Q i j = monomial (bwwExp (D.dn i j) 0) (P.t i j : k) +
      ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
        monomial (bwwExp r s) ((P.Q i j).coeff (bwwExp r s)) +
      monomial (bwwExp 0 (D.dn j i)) (P.t j i : k) := by
  ext m
  rw [eq_bwwExp m]
  generalize m 0 = a, m 1 = b
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply]
  rw [coeff_boxSum, coeff_monomial, coeff_monomial, P.t_of_ne hij,
    P.t_of_ne (Ne.symm hij), ← P.coeff_symm i j 0 (D.dn j i)]
  simp only [bwwExp_inj]
  by_cases hab : a < D.dn i j ∧ b < D.dn j i
  · have n1 : ¬(D.dn i j = a ∧ 0 = b) := by omega
    have n2 : ¬(0 = a ∧ D.dn j i = b) := by omega
    simp [hab, n1, n2]
  by_cases h1 : D.dn i j = a ∧ 0 = b
  · obtain ⟨rfl, rfl⟩ := h1
    have n2 : ¬(0 = D.dn i j ∧ D.dn j i = 0) := by omega
    simp [n2]
  by_cases h2 : 0 = a ∧ D.dn j i = b
  · obtain ⟨rfl, rfl⟩ := h2
    simp [h1]
  simp only [hab, h1, h2, ite_false, add_zero]
  by_contra hc
  have hs := P.support i j a b hc
  omega

/-- `x^0 y^0` is the zero exponent. -/
@[simp] theorem _root_.OddMath.SKM.bwwExp_zero_zero : bwwExp 0 0 = 0 := by simp [bwwExp]

/-- For `i ≠ j` with `dᵢⱼ = 0`, `Qᵢⱼ` is the constant `tᵢⱼ`. -/
theorem eq_const {i j : I} (hij : i ≠ j) (hd : D.dn i j = 0) :
    P.Q i j = C (P.t i j : k) := by
  ext m
  rw [eq_bwwExp m, coeff_C, P.t_of_ne hij, hd]
  generalize m 0 = a, m 1 = b
  rw [← bwwExp_zero_zero]
  simp only [bwwExp_inj]
  by_cases h : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬(0 = a ∧ 0 = b) := by omega
    simp only [h', ite_false]
    by_contra hc
    have hs := P.support i j a b hc
    have hd' : D.dn j i = 0 := (ScalarData.dn_eq_zero_iff i j).mp hd
    omega

end BWWPolynomials

end OddMath.SKM
