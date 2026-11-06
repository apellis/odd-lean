/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Grading

/-!
# Brundan–Wang–Webster parameters

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2 (the polynomials `Qᵢⱼ(u, v)` with
coefficients `tᵢⱼ;ᵣₛ` for `0 ≤ r < dᵢⱼ`, `0 ≤ s < dⱼᵢ`), compared with J. Brundan,
A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §1, (1.3), (1.4) and the
homogeneity condition (1.31).

The Brundan–Ellis polynomial `Qᵢⱼ(u, v) = tᵢⱼ u^{dᵢⱼ} + tⱼᵢ v^{dⱼᵢ} + Σ sᵢⱼ^{pq} u^p v^q`
has interior monomials only (`0 < p < dᵢⱼ`, `0 < q < dⱼᵢ`). The Brundan–Wang–Webster
polynomial also allows the monomials with `p = 0` or `q = 0`. Both are encoded by one
coefficient function `c i j p q`, the coefficient of `u^p v^q` in `Qᵢⱼ(u, v)`, supported on
the box `[0, dᵢⱼ] × [0, dⱼᵢ]`, with the corner values `c i j dᵢⱼ 0 = tᵢⱼ` and
`c i j 0 dⱼᵢ = tⱼᵢ` and no other monomial on the top and right edges.

* `BWWScalars D k`: the units `tᵢⱼ` of (1.3) and such a coefficient function, symmetric
  (`c i j p q = c j i q p`), even (`c i j p q = 0` if `p|i|` is odd), and zero on the
  diagonal `i = j`, with `2` invertible if some `i` is odd. When `dᵢⱼ = 0` the box is the
  single point `(0, 0)` and `Qᵢⱼ = tᵢⱼ`.
* `ScalarData.toBWW`: the Brundan–Ellis parameters, with zero monomials off the interior and
  the corners.
* `BWWScalars.Homogeneous`: the homogeneity condition (1.31) on every monomial below the
  corners.
* `BWWScalars.Homogeneous.exists_eq_toBWW`: homogeneous Brundan–Wang–Webster parameters are
  Brundan–Ellis parameters satisfying (1.31). Indeed a monomial with `p = 0` or `q = 0` below
  the corners never satisfies (1.31), so its coefficient vanishes.
-/

noncomputable section

namespace OddMath.SKM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}

/-- Parameters in the shape of Brundan–Wang–Webster §2.2. The units `tᵢⱼ` are as in
Brundan–Ellis (1.3); `c i j p q` is the coefficient of `u^p v^q` in `Qᵢⱼ(u, v)`. -/
structure BWWScalars (D : Datum I X) (k : Type w) [CommRing k] where
  /-- The units `tᵢⱼ`. -/
  t : I → I → kˣ
  t_self : ∀ i, t i i = 1
  t_symm_of_d_eq_zero : ∀ i j, D.d i j = 0 → t i j = t j i
  /-- The coefficient of `u^p v^q` in `Qᵢⱼ(u, v)`. -/
  c : I → I → ℕ → ℕ → k
  c_symm : ∀ i j p q, c i j p q = c j i q p
  c_parity : ∀ (i j : I) (p q : ℕ), (p : ZMod 2) * D.parity i = 1 → c i j p q = 0
  c_self : ∀ i p q, c i i p q = 0
  /-- The leading coefficient of `u^{dᵢⱼ}`. -/
  c_corner : ∀ i j, i ≠ j → c i j (D.dn i j) 0 = t i j
  /-- No monomial outside the box `[0, dᵢⱼ] × [0, dⱼᵢ]`. -/
  c_outside : ∀ i j (p q : ℕ), D.dn i j < p ∨ D.dn j i < q → c i j p q = 0
  /-- No monomial `u^{dᵢⱼ} v^q` with `q > 0`. -/
  c_top : ∀ i j (q : ℕ), 0 < q → c i j (D.dn i j) q = 0
  two_isUnit : (∃ i, D.parity i = 1) → IsUnit (2 : k)

namespace BWWScalars

variable {k : Type w} [CommRing k]

@[ext]
theorem ext {Sc Sc' : BWWScalars D k} (ht : Sc.t = Sc'.t) (hc : Sc.c = Sc'.c) : Sc = Sc' := by
  cases Sc; cases Sc'; cases ht; cases hc; rfl

/-- The coefficient of `v^{dⱼᵢ}` is `tⱼᵢ`. -/
theorem c_corner' (Sc : BWWScalars D k) {i j : I} (hij : i ≠ j) :
    Sc.c i j 0 (D.dn j i) = Sc.t j i := by
  rw [Sc.c_symm, Sc.c_corner j i (Ne.symm hij)]

/-- No monomial `u^p v^{dⱼᵢ}` with `p > 0`. -/
theorem c_right (Sc : BWWScalars D k) (i j : I) {p : ℕ} (hp : 0 < p) :
    Sc.c i j p (D.dn j i) = 0 := by
  rw [Sc.c_symm, Sc.c_top j i p hp]

/-- The homogeneity condition (1.31) on every monomial strictly below the corners:
a nonzero `c i j p q` with `p < dᵢⱼ`, `q < dⱼᵢ` has `p dⱼᵢ + q dᵢⱼ = dᵢⱼ dⱼᵢ`. -/
def Homogeneous (Sc : BWWScalars D k) : Prop :=
  ∀ i j (p q : ℕ), i ≠ j → (p : ℤ) < D.d i j → (q : ℤ) < D.d j i → Sc.c i j p q ≠ 0 →
    p * D.d j i + q * D.d i j = D.d i j * D.d j i

/-- Under (1.31), the monomials with `p = 0` or `q = 0` below the corners vanish. -/
theorem Homogeneous.c_eq_zero {Sc : BWWScalars D k} (hh : Sc.Homogeneous) {i j : I}
    (hij : i ≠ j) {p q : ℕ} (hp : (p : ℤ) < D.d i j) (hq : (q : ℤ) < D.d j i)
    (hpq : p = 0 ∨ q = 0) : Sc.c i j p q = 0 := by
  by_contra hc
  have h := hh i j p q hij hp hq hc
  have hi : (0 : ℤ) < D.d i j := lt_of_le_of_lt (Int.natCast_nonneg p) hp
  have hj : (0 : ℤ) < D.d j i := lt_of_le_of_lt (Int.natCast_nonneg q) hq
  rcases hpq with rfl | rfl
  · have : (q : ℤ) * D.d i j < D.d j i * D.d i j := mul_lt_mul_of_pos_right hq hi
    simp only [Nat.cast_zero, zero_mul, zero_add] at h
    linarith [mul_comm (D.d i j) (D.d j i)]
  · have : (p : ℤ) * D.d j i < D.d i j * D.d j i := mul_lt_mul_of_pos_right hp hj
    simp only [Nat.cast_zero, zero_mul, add_zero] at h
    linarith

end BWWScalars

namespace ScalarData

open Classical

variable {k : Type w} [CommRing k]

/-- The coefficient of `u^p v^q` in the Brundan–Ellis polynomial `Qᵢⱼ(u, v)`: `tᵢⱼ` at
`(dᵢⱼ, 0)`, `tⱼᵢ` at `(0, dⱼᵢ)`, `sᵢⱼ^{pq}` in the interior and `0` elsewhere (and `0` for
`i = j`). -/
def bwwCoeff (Sc : Scalars D k) (i j : I) (p q : ℕ) : k :=
  if i = j then 0
  else if p = D.dn i j ∧ q = 0 then (Sc.t i j : k)
  else if p = 0 ∧ q = D.dn j i then (Sc.t j i : k)
  else if 0 < p ∧ p < D.dn i j ∧ 0 < q ∧ q < D.dn j i then Sc.s i j p q
  else 0

theorem dn_eq_zero_iff (i j : I) : D.dn i j = 0 ↔ D.dn j i = 0 := by
  unfold Datum.dn
  have := D.d_eq_zero_iff i j
  by_cases hij : i = j
  · subst hij; rfl
  · have h1 := D.d_nonneg hij
    have h2 := D.d_nonneg (Ne.symm hij)
    omega

theorem bwwCoeff_symm (Sc : Scalars D k) (i j : I) (p q : ℕ) :
    bwwCoeff Sc i j p q = bwwCoeff Sc j i q p := by
  have hz := dn_eq_zero_iff (D := D) i j
  unfold bwwCoeff
  by_cases hij : i = j
  · simp [hij]
  have hji : j ≠ i := Ne.symm hij
  simp only [hij, hji, ite_false]
  by_cases h1 : p = D.dn i j ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h1
    by_cases h0 : D.dn i j = 0
    · have h0' : D.dn j i = 0 := hz.mp h0
      have hd : D.d i j = 0 := by
        have := D.d_nonneg hij; unfold Datum.dn at h0; omega
      simp [h0, h0', Sc.t_symm_of_d_eq_zero i j hd]
    · simp [h0]
  by_cases h2 : p = 0 ∧ q = D.dn j i
  · obtain ⟨rfl, rfl⟩ := h2
    simp only [h1, ite_false, and_self, ite_true]
  have h1' : ¬(q = D.dn j i ∧ p = 0) := fun h => h2 ⟨h.2, h.1⟩
  have h2' : ¬(q = 0 ∧ p = D.dn i j) := fun h => h1 ⟨h.2, h.1⟩
  simp only [h1, h2, h1', h2', ite_false]
  by_cases h3 : 0 < p ∧ p < D.dn i j ∧ 0 < q ∧ q < D.dn j i
  · simp only [h3, Sc.s_symm]
  · have h3' : ¬(0 < q ∧ q < D.dn j i ∧ 0 < p ∧ p < D.dn i j) :=
      fun h => h3 ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩
    simp only [h3, h3', ite_false]

theorem natCast_dn_eq_zero_of_odd {i : I} (hi : D.parity i = 1) (j : I) :
    ((D.dn i j : ℕ) : ZMod 2) = 0 := by
  obtain ⟨m, hm⟩ := D.even_d_of_odd hi j
  have : D.dn i j = (m + m).toNat := by unfold Datum.dn; rw [hm]
  rw [this]
  rcases le_or_gt 0 m with h | h
  · have : (m + m).toNat = m.toNat + m.toNat := by omega
    rw [this, Nat.cast_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  · have : (m + m).toNat = 0 := by omega
    simp [this]

theorem bwwCoeff_parity (Sc : Scalars D k) (i j : I) (p q : ℕ)
    (h : (p : ZMod 2) * D.parity i = 1) : bwwCoeff Sc i j p q = 0 := by
  have hi : D.parity i = 1 := by
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (D.parity i) with h0 | h0
    · rw [h0, mul_zero] at h; exact absurd h (by decide)
    · exact h0
  unfold bwwCoeff
  by_cases hij : i = j
  · simp [hij]
  simp only [hij, ite_false]
  by_cases h1 : p = D.dn i j ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h1
    rw [natCast_dn_eq_zero_of_odd hi j, zero_mul] at h
    exact absurd h (by decide)
  by_cases h2 : p = 0 ∧ q = D.dn j i
  · obtain ⟨rfl, rfl⟩ := h2
    simp at h
  simp only [h1, h2, ite_false, Sc.s_eq_zero i j p q h, ite_self]

/-- The Brundan–Ellis parameters as Brundan–Wang–Webster parameters: the coefficients of
`Qᵢⱼ(u, v)` with `p = 0` or `q = 0` are zero except at the corners. -/
def toBWW (Sc : Scalars D k) : BWWScalars D k where
  t := Sc.t
  t_self := Sc.t_self
  t_symm_of_d_eq_zero := Sc.t_symm_of_d_eq_zero
  c := bwwCoeff Sc
  c_symm := bwwCoeff_symm Sc
  c_parity := bwwCoeff_parity Sc
  c_self i p q := by simp [bwwCoeff]
  c_corner i j hij := by simp [bwwCoeff, hij]
  c_outside i j p q h := by
    unfold bwwCoeff
    split_ifs <;> first | rfl | omega
  c_top i j q hq := by
    unfold bwwCoeff
    split_ifs with h0 h1 h2 h3
    · rfl
    · omega
    · have := (dn_eq_zero_iff (D := D) i j).mp h2.1
      omega
    · omega
    · rfl
  two_isUnit := Sc.two_isUnit

@[simp] theorem toBWW_t (Sc : Scalars D k) : Sc.toBWW.t = Sc.t := rfl

theorem toBWW_c (Sc : Scalars D k) : Sc.toBWW.c = bwwCoeff Sc := rfl

/-- In the interior of the box, the coefficients of `Sc.toBWW` are the scalars `sᵢⱼ^{pq}`. -/
theorem toBWW_c_of_interior (Sc : Scalars D k) {i j : I} (hij : i ≠ j) {p q : ℕ} (hp : 0 < p)
    (hp' : p < D.dn i j) (hq : 0 < q) (hq' : q < D.dn j i) :
    Sc.toBWW.c i j p q = Sc.s i j p q := by
  have h1 : ¬(p = D.dn i j ∧ q = 0) := by omega
  have h2 : ¬(p = 0 ∧ q = D.dn j i) := by omega
  have h3 : 0 < p ∧ p < D.dn i j ∧ 0 < q ∧ q < D.dn j i := ⟨hp, hp', hq, hq'⟩
  simp [toBWW_c, bwwCoeff, hij, h1, h2, h3]

/-- `Sc.toBWW` satisfies (1.31) exactly when `Sc` does. -/
theorem toBWW_homogeneous_iff (Sc : Scalars D k) : Sc.toBWW.Homogeneous ↔ Sc.Homogeneous := by
  constructor
  · intro hh i j p q hp hp' hq hq' hs
    have hij : i ≠ j := by
      rintro rfl
      have := D.d_self i
      omega
    have hdn : (D.dn i j : ℤ) = D.d i j := D.dn_cast hij
    have hdn' : (D.dn j i : ℤ) = D.d j i := D.dn_cast (Ne.symm hij)
    refine hh i j p q hij hp' hq' ?_
    rw [toBWW_c_of_interior Sc hij hp (by omega) hq (by omega)]
    exact hs
  · intro hh i j p q hij hp hq hc
    have hdn : (D.dn i j : ℤ) = D.d i j := D.dn_cast hij
    have hdn' : (D.dn j i : ℤ) = D.d j i := D.dn_cast (Ne.symm hij)
    rw [toBWW_c, bwwCoeff] at hc
    simp only [hij, ite_false] at hc
    split_ifs at hc with h1 h2 h3
    · omega
    · omega
    · exact hh i j p q h3.1 (by omega) h3.2.2.1 (by omega) hc
    · exact absurd rfl hc

end ScalarData

namespace BWWScalars

variable {k : Type w} [CommRing k]

/-- The Brundan–Ellis parameters underlying Brundan–Wang–Webster parameters, keeping the
interior coefficients. -/
def toScalars (Sc : BWWScalars D k) : Scalars D k where
  t := Sc.t
  t_self := Sc.t_self
  t_symm_of_d_eq_zero := Sc.t_symm_of_d_eq_zero
  s := Sc.c
  s_symm := Sc.c_symm
  s_eq_zero := Sc.c_parity
  two_isUnit := Sc.two_isUnit

/-- Homogeneous Brundan–Wang–Webster parameters have no monomials with `p = 0` or `q = 0`
other than the corners, so they come from Brundan–Ellis parameters. -/
theorem Homogeneous.toScalars_toBWW {Sc : BWWScalars D k} (hh : Sc.Homogeneous) :
    Sc.toScalars.toBWW = Sc := by
  refine ext rfl ?_
  funext i j p q
  change ScalarData.bwwCoeff Sc.toScalars i j p q = Sc.c i j p q
  unfold ScalarData.bwwCoeff
  by_cases hij : i = j
  · subst hij; simp [Sc.c_self]
  have hdn : (D.dn i j : ℤ) = D.d i j := D.dn_cast hij
  have hdn' : (D.dn j i : ℤ) = D.d j i := D.dn_cast (Ne.symm hij)
  simp only [hij, ite_false]
  split_ifs with h1 h2 h3
  · obtain ⟨rfl, rfl⟩ := h1
    exact (Sc.c_corner i j hij).symm
  · obtain ⟨rfl, rfl⟩ := h2
    exact (Sc.c_corner' hij).symm
  · rfl
  · symm
    by_cases ho : D.dn i j < p ∨ D.dn j i < q
    · exact Sc.c_outside i j p q ho
    push Not at ho
    by_cases hp : p = D.dn i j
    · subst hp
      exact Sc.c_top i j q (by omega)
    by_cases hq : q = D.dn j i
    · subst hq
      exact Sc.c_right i j (by omega)
    exact hh.c_eq_zero hij (by omega) (by omega) (by omega)

/-- **(H)**: homogeneous Brundan–Wang–Webster parameters are the Brundan–Ellis parameters
satisfying (1.31). -/
theorem Homogeneous.exists_eq_toBWW {Sc : BWWScalars D k} (hh : Sc.Homogeneous) :
    ∃ Sc₀ : Scalars D k, Sc₀.Homogeneous ∧ Sc₀.toBWW = Sc :=
  ⟨Sc.toScalars, by rwa [← ScalarData.toBWW_homogeneous_iff, hh.toScalars_toBWW],
    hh.toScalars_toBWW⟩

end BWWScalars

end OddMath.SKM
