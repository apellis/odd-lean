/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.NilHeckeFamily

/-!
# Signed nilHecke families and their Demazure idempotents

Hill–Wang, arXiv:1202.2769v2, §5.2, Lemmas 5.6–5.8 (after Khovanov–Lauda II, Lemma 5 and
(10)–(13), and Ellis–Khovanov–Lauda, Propositions 3.5–3.6), in the form used by
Brundan–Ellis, arXiv:1701.04133v2, §11: the divided-power idempotent `1_{i^{(n)}}` of a block of
`n` strands of one colour is the longest product `D_{w_0}` of `D_j = -ε T_j X_{j+1}`.

A *signed nilHecke family* with sign `ε = ±1` on the block `[s, s + n)` of a ring consists of
dots `X a` and crossings `T j` (of the positions `j`, `j + 1`) with

* `X_a X_b = ε X_b X_a` (`a ≠ b`), `X_a T_j = ε T_j X_a` (`a ≠ j, j + 1`),
  `T_j T_l = ε T_l T_j` (`|j - l| > 1`);
* `T_j² = 0` and the braid relation `T_j T_{j+1} T_j = T_{j+1} T_j T_{j+1}`;
* `T_j X_j - ε X_{j+1} T_j = 1` and `X_j T_j - ε T_j X_{j+1} = 1`.

For `ε = 1` these are the relations of the nilHecke ring and for `ε = -1` those of the odd
nilHecke ring. They hold in the endomorphism ring of a word of one colour `i` in BE2's quiver
Hecke supercategory, with `ε = (-1)^{|i|}`. Positions are zero-indexed and products are ring
products; no orientation of the strands is fixed here.

## Main results

* `dem`: the Demazure elements `D_j`, with `D_j² = D_j`, `T_j D_j = 0`, `D_j T_j = T_j`,
  `D_j = 1 - X_j T_j` and the braid relations (`isBraidFamily_dem`).
* `idem s' n'`: the longest product `D_{w_0}` of a sub-block, an idempotent absorbing every
  `D_j` of its block on both sides and killed by every `T_j` of its block on the left
  (`idem_mul_idem`, `dem_mul_idem`, `idem_mul_dem`, `t_mul_idem`).
* HW Lemma 5.7: (5.25) `idem_mul_idem_succ`, `idem_succ_mul_idem_succ`; (5.26)–(5.27)
  `idem_mul_chL_mul_idem`, `idem_mul_chR_mul_idem`.
* HW Lemma 5.8 (KL II (12)–(13)): `chR_mul_x_pow_mul_idem`, `chL_mul_x_pow_mul_idem`, with the
  signs `ε^{n(n-1)/2}` and `(-1)^n ε^{n(n+1)/2}` of the Demazure normalization.

The proofs use only the relations: HW deduce (5.26) from Lemma 5.6, `e_n ∂_{w_0} = ∂_{w_0}`;
here each `D_j = 1 - X_j T_j` of the block fixes the left-hand side directly.
-/

namespace OddMath.QuiverHecke.SignedNilHecke

open Categorification.KLR.KL2.NH
open Categorification.NilHecke (w0Word)

variable {B : Type*} [Ring B]

/-- The relations of the (odd) nilHecke ring on the block of positions `[s, s + n)`, with sign
`ε`: `ε = 1` even, `ε = -1` odd. -/
structure IsSignedNilHeckeFamily (ε : ℤˣ) (s n : ℕ) (X T : ℕ → B) : Prop where
  x_comm : ∀ a b, s ≤ a → a < s + n → s ≤ b → b < s + n → a ≠ b →
    X a * X b = (ε : ℤ) • (X b * X a)
  x_t_comm : ∀ a j, s ≤ a → a < s + n → s ≤ j → j + 1 < s + n → a ≠ j → a ≠ j + 1 →
    X a * T j = (ε : ℤ) • (T j * X a)
  t_comm : ∀ j l, s ≤ j → j + 1 < l → l + 1 < s + n → T j * T l = (ε : ℤ) • (T l * T j)
  t_sq : ∀ j, s ≤ j → j + 1 < s + n → T j * T j = 0
  braid : ∀ j, s ≤ j → j + 2 < s + n → T j * T (j + 1) * T j = T (j + 1) * T j * T (j + 1)
  t_x : ∀ j, s ≤ j → j + 1 < s + n → T j * X j - (ε : ℤ) • (X (j + 1) * T j) = 1
  x_t : ∀ j, s ≤ j → j + 1 < s + n → X j * T j - (ε : ℤ) • (T j * X (j + 1)) = 1

theorem eps_mul_eps (ε : ℤˣ) : (ε : ℤ) * (ε : ℤ) = 1 := by
  rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

theorem eps_smul_eps_smul (ε : ℤˣ) (x : B) : (ε : ℤ) • (ε : ℤ) • x = x := by
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

/-- The Demazure element `D_j = -ε T_j X_{j+1}` of the block, zero outside it. -/
def dem (ε : ℤˣ) (s n : ℕ) (X T : ℕ → B) (j : ℕ) : B :=
  if s ≤ j ∧ j + 1 < s + n then -((ε : ℤ) • (T j * X (j + 1))) else 0

/-- The Demazure product `D_{w_0}` of the sub-block `[s', s' + n')`. -/
def idem (ε : ℤˣ) (s n : ℕ) (X T : ℕ → B) (s' n' : ℕ) : B := Wb (dem ε s n X T) s' n'

variable {ε : ℤˣ} {s n : ℕ} {X T : ℕ → B}

theorem dem_of {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) :
    dem ε s n X T j = -((ε : ℤ) • (T j * X (j + 1))) := by
  simp only [dem, h₁, h₂, and_self, ↓reduceIte]

theorem dem_of_not {j : ℕ} (h : ¬ (s ≤ j ∧ j + 1 < s + n)) : dem ε s n X T j = 0 := by
  simp only [dem, h, ↓reduceIte]

/-! ### Commuting up to a sign -/

/-- `x` and `y` commute up to a sign. -/
def SignComm (x y : B) : Prop := ∃ u : ℤˣ, x * y = (u : ℤ) • (y * x)

namespace SignComm

variable {x y z : B}

theorem one_right (x : B) : SignComm x 1 := ⟨1, by simp⟩

theorem one_left (x : B) : SignComm 1 x := ⟨1, by simp⟩

theorem symm (h : SignComm x y) : SignComm y x := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by rw [hu, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]⟩

theorem mul_right (h₁ : SignComm x y) (h₂ : SignComm x z) : SignComm x (y * z) := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  exact ⟨u * v, by rw [← mul_assoc, hu, smul_mul_assoc, mul_assoc, hv, mul_smul_comm, smul_smul,
    ← mul_assoc, Units.val_mul]⟩

theorem mul_left (h₁ : SignComm x z) (h₂ : SignComm y z) : SignComm (x * y) z :=
  (h₁.symm.mul_right h₂.symm).symm

theorem pow_right (h : SignComm x y) (m : ℕ) : SignComm x (y ^ m) := by
  induction m with
  | zero => simpa using one_right x
  | succ m ih => rw [pow_succ]; exact ih.mul_right h

theorem pow_left (h : SignComm x y) (m : ℕ) : SignComm (x ^ m) y :=
  (h.symm.pow_right m).symm

theorem wp {T : ℕ → B} {ρ : List ℕ} (h : ∀ j ∈ ρ, SignComm x (T j)) : SignComm x (wp T ρ) := by
  induction ρ with
  | nil => exact one_right x
  | cons j ρ ih =>
    rw [wp_cons]
    exact (h j List.mem_cons_self).mul_right (ih fun l hl => h l (List.mem_cons_of_mem _ hl))

/-- Moving `x` to the front of `y * r` costs a sign. -/
theorem exists_mul_mul (h : SignComm x y) (r : B) :
    ∃ u : ℤˣ, y * (x * r) = (u : ℤ) • (x * (y * r)) := by
  obtain ⟨u, hu⟩ := h.symm
  exact ⟨u, by rw [← mul_assoc, hu, smul_mul_assoc, mul_assoc]⟩

end SignComm

namespace IsSignedNilHeckeFamily

variable (hF : IsSignedNilHeckeFamily ε s n X T)
include hF

/-! ### The relations, with a tail -/

theorem xt_far {a j : ℕ} (ha₁ : s ≤ a) (ha₂ : a < s + n) (h₁ : s ≤ j) (h₂ : j + 1 < s + n)
    (h₃ : a ≠ j) (h₄ : a ≠ j + 1) (r : B) :
    X a * (T j * r) = (ε : ℤ) • (T j * (X a * r)) := by
  rw [← mul_assoc, hF.x_t_comm a j ha₁ ha₂ h₁ h₂ h₃ h₄, smul_mul_assoc, mul_assoc]

theorem tx_far {a j : ℕ} (ha₁ : s ≤ a) (ha₂ : a < s + n) (h₁ : s ≤ j) (h₂ : j + 1 < s + n)
    (h₃ : a ≠ j) (h₄ : a ≠ j + 1) (r : B) :
    T j * (X a * r) = (ε : ℤ) • (X a * (T j * r)) := by
  rw [hF.xt_far ha₁ ha₂ h₁ h₂ h₃ h₄, eps_smul_eps_smul]

theorem x_succ_mul_t {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) :
    X (j + 1) * T j = (ε : ℤ) • (T j * X j - 1) := by
  rw [← hF.t_x j h₁ h₂, sub_sub_cancel, eps_smul_eps_smul]

theorem t_mul_x_succ {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) :
    T j * X (j + 1) = (ε : ℤ) • (X j * T j - 1) := by
  rw [← hF.x_t j h₁ h₂, sub_sub_cancel, eps_smul_eps_smul]

theorem xt_succ {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (r : B) :
    X (j + 1) * (T j * r) = (ε : ℤ) • (T j * (X j * r)) - (ε : ℤ) • r := by
  rw [← mul_assoc, hF.x_succ_mul_t h₁ h₂, smul_mul_assoc, sub_mul, one_mul, mul_assoc, smul_sub]

theorem tx_succ {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (r : B) :
    T j * (X (j + 1) * r) = (ε : ℤ) • (X j * (T j * r)) - (ε : ℤ) • r := by
  rw [← mul_assoc, hF.t_mul_x_succ h₁ h₂, smul_mul_assoc, sub_mul, one_mul, mul_assoc, smul_sub]

theorem xt_self {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (r : B) :
    X j * (T j * r) = r + (ε : ℤ) • (T j * (X (j + 1) * r)) := by
  rw [← mul_assoc, sub_eq_iff_eq_add.mp (hF.x_t j h₁ h₂), add_mul, one_mul, smul_mul_assoc,
    mul_assoc, add_comm]

theorem tx_self {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (r : B) :
    T j * (X j * r) = r + (ε : ℤ) • (X (j + 1) * (T j * r)) := by
  rw [← mul_assoc, sub_eq_iff_eq_add.mp (hF.t_x j h₁ h₂), add_mul, one_mul, smul_mul_assoc,
    mul_assoc, add_comm]

theorem xx {a b : ℕ} (ha₁ : s ≤ a) (ha₂ : a < s + n) (hb₁ : s ≤ b) (hb₂ : b < s + n)
    (h : a ≠ b) (r : B) : X a * (X b * r) = (ε : ℤ) • (X b * (X a * r)) := by
  rw [← mul_assoc, hF.x_comm a b ha₁ ha₂ hb₁ hb₂ h, smul_mul_assoc, mul_assoc]

theorem tt_far {j l : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < l) (h₃ : l + 1 < s + n) (r : B) :
    T j * (T l * r) = (ε : ℤ) • (T l * (T j * r)) := by
  rw [← mul_assoc, hF.t_comm j l h₁ h₂ h₃, smul_mul_assoc, mul_assoc]

theorem tt_sq {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (r : B) : T j * (T j * r) = 0 := by
  rw [← mul_assoc, hF.t_sq j h₁ h₂, zero_mul]

theorem tt_far' {j l : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < l) (h₃ : l + 1 < s + n) (r : B) :
    T l * (T j * r) = (ε : ℤ) • (T j * (T l * r)) := by
  rw [hF.tt_far h₁ h₂ h₃, eps_smul_eps_smul]

theorem braid_tail {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 2 < s + n) (r : B) :
    T (j + 1) * (T j * (T (j + 1) * r)) = T j * (T (j + 1) * (T j * r)) := by
  simp only [← mul_assoc, hF.braid j h₁ h₂]

/-! ### Demazure elements -/

theorem dem_eq {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) :
    dem ε s n X T j = 1 - X j * T j := by
  rw [dem_of h₁ h₂, ← hF.x_t j h₁ h₂]; abel

/-- `T_j D_j = 0`. -/
theorem t_mul_dem {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) : T j * dem ε s n X T j = 0 := by
  rw [dem_of h₁ h₂, mul_neg, mul_smul_comm, ← mul_assoc, hF.t_sq j h₁ h₂, zero_mul, smul_zero,
    neg_zero]

/-- `D_j T_j = T_j`. -/
theorem dem_mul_t {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) : dem ε s n X T j * T j = T j := by
  rw [hF.dem_eq h₁ h₂, sub_mul, one_mul, mul_assoc, hF.t_sq j h₁ h₂, mul_zero, sub_zero]

/-- `D_j² = D_j`. -/
theorem dem_mul_dem {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) :
    dem ε s n X T j * dem ε s n X T j = dem ε s n X T j := by
  nth_rw 1 [hF.dem_eq h₁ h₂]
  rw [sub_mul, one_mul, mul_assoc, hF.t_mul_dem h₁ h₂, mul_zero, sub_zero]

theorem dem_sq (j : ℕ) : dem ε s n X T j * dem ε s n X T j = (1 : ℤ) • dem ε s n X T j := by
  by_cases h : s ≤ j ∧ j + 1 < s + n
  · rw [hF.dem_mul_dem h.1 h.2, one_smul]
  · rw [dem_of_not h, mul_zero, smul_zero]

theorem dem_mul_dem_comm {j l : ℕ} (h : j + 1 < l) :
    dem ε s n X T j * dem ε s n X T l = dem ε s n X T l * dem ε s n X T j := by
  by_cases hj : s ≤ j ∧ j + 1 < s + n
  swap; · rw [dem_of_not hj, zero_mul, mul_zero]
  by_cases hl : s ≤ l ∧ l + 1 < s + n
  swap; · rw [dem_of_not hl, zero_mul, mul_zero]
  obtain ⟨h₁, h₂⟩ := hj
  obtain ⟨h₃, h₄⟩ := hl
  have core : T j * (X (j + 1) * (T l * (X (l + 1) * 1))) =
      T l * (X (l + 1) * (T j * (X (j + 1) * 1))) := by
    rw [hF.xt_far (a := j + 1) (j := l) (by omega) (by omega) h₃ h₄ (by omega) (by omega),
      hF.xt_far (a := l + 1) (j := j) (by omega) h₄ h₁ h₂ (by omega) (by omega),
      hF.xx (a := l + 1) (b := j + 1) (by omega) h₄ (by omega) (by omega) (by omega),
      mul_smul_comm, hF.tt_far h₁ h h₄]
    simp only [mul_smul_comm, eps_smul_eps_smul]
  rw [dem_of h₁ h₂, dem_of h₃ h₄, neg_mul_neg, neg_mul_neg, smul_mul_smul_comm,
    smul_mul_smul_comm]
  congr 1
  simpa only [mul_assoc, mul_one] using core

theorem dem_braid (j : ℕ) :
    dem ε s n X T j * dem ε s n X T (j + 1) * dem ε s n X T j =
      dem ε s n X T (j + 1) * dem ε s n X T j * dem ε s n X T (j + 1) := by
  by_cases hj : s ≤ j ∧ j + 1 < s + n
  swap; · simp only [dem_of_not hj, zero_mul, mul_zero]
  by_cases hl : s ≤ j + 1 ∧ j + 1 + 1 < s + n
  swap; · simp only [dem_of_not hl, zero_mul, mul_zero]
  obtain ⟨h₁, -⟩ := hj
  obtain ⟨-, h₂⟩ := hl
  have h₂' : j + 2 < s + n := by omega
  have core : T j * (X (j + 1) * (T (j + 1) * (X (j + 2) * (T j * (X (j + 1) * 1))))) =
      T (j + 1) * (X (j + 2) * (T j * (X (j + 1) * (T (j + 1) * (X (j + 2) * 1))))) := by
    have F1 := hF.xt_far (a := j + 2) (j := j) (by omega) h₂' h₁ (by omega) (by omega)
      (by omega)
    have F2 := hF.xt_self (j := j + 1) (by omega) (by omega)
    have F3 := hF.xt_succ (j := j + 1) (by omega) (by omega)
    have F4 := hF.tt_sq (j := j) h₁ (by omega)
    have F5 := hF.xx (a := j + 2) (b := j + 1) (by omega) h₂' (by omega) (by omega) (by omega)
    have F6 := hF.braid_tail h₁ h₂'
    have e : j + 1 + 1 = j + 2 := rfl
    simp only [e] at F2 F3
    simp only [F1, F2, F3, F4, F5, F6, mul_add, mul_sub, smul_sub, mul_smul_comm, smul_smul,
      eps_mul_eps, one_smul, zero_add]
    abel
  rw [dem_of h₁ (by omega), dem_of (by omega) h₂]
  simp only [show j + 1 + 1 = j + 2 from rfl, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm,
    mul_assoc]
  simp only [mul_one] at core
  rw [core]

/-- The Demazure elements satisfy the braid relations. -/
theorem isBraidFamily_dem : IsBraidFamily (dem ε s n X T) :=
  ⟨fun _ _ h => hF.dem_mul_dem_comm h, hF.dem_braid⟩

/-! ### The Demazure idempotent of a sub-block -/

theorem dem_mul_idem {s' n' j : ℕ} (h₁ : s' ≤ j) (h₂ : j + 1 < s' + n') :
    dem ε s n X T j * idem ε s n X T s' n' = idem ε s n X T s' n' := by
  rw [idem, d_mul_wb_eq_smul hF.isBraidFamily_dem hF.dem_sq h₁ h₂, one_smul]

theorem idem_mul_dem {s' n' j : ℕ} (h₁ : s' ≤ j) (h₂ : j + 1 < s' + n') :
    idem ε s n X T s' n' * dem ε s n X T j = idem ε s n X T s' n' := by
  rw [idem, wb_mul_d_eq_smul hF.isBraidFamily_dem hF.dem_sq h₁ h₂, one_smul]

omit hF in
/-- A product of Demazure elements of the block `[s', s' + n')` fixes everything that each of
them fixes. -/
theorem wp_dem_mul_of_forall {s' n' : ℕ} {y : B}
    (hy : ∀ j, s' ≤ j → j + 1 < s' + n' → dem ε s n X T j * y = y) {ρ : List ℕ}
    (hρ : ∀ j ∈ ρ, s' ≤ j ∧ j + 1 < s' + n') : wp (dem ε s n X T) ρ * y = y := by
  induction ρ with
  | nil => simp
  | cons j ρ ih =>
    rw [wp_cons, mul_assoc, ih fun l hl => hρ l (List.mem_cons_of_mem _ hl),
      hy j (hρ j List.mem_cons_self).1 (hρ j List.mem_cons_self).2]

omit hF in
/-- `D_{w_0}` fixes everything that every `D_j` of its block fixes. -/
theorem idem_mul_of_forall {s' n' : ℕ} {y : B}
    (hy : ∀ j, s' ≤ j → j + 1 < s' + n' → dem ε s n X T j * y = y) :
    idem ε s n X T s' n' * y = y :=
  wp_dem_mul_of_forall hy fun _ hj => mem_w0Word_map hj

/-- `1_{i^{(n)}} = D_{w_0}` is an idempotent. -/
theorem idem_mul_idem (s' n' : ℕ) :
    idem ε s n X T s' n' * idem ε s n X T s' n' = idem ε s n X T s' n' :=
  idem_mul_of_forall fun _ h₁ h₂ => hF.dem_mul_idem h₁ h₂

/-- `T_j D_{w_0} = 0` for a crossing of the block. -/
theorem t_mul_idem {s' n' j : ℕ} (hs : s ≤ s') (hn : s' + n' ≤ s + n) (h₁ : s' ≤ j)
    (h₂ : j + 1 < s' + n') : T j * idem ε s n X T s' n' = 0 := by
  rw [← hF.dem_mul_idem h₁ h₂, ← mul_assoc, hF.t_mul_dem (by omega) (by omega), zero_mul]

/-- HW (5.25), KL II (10), with the sub-block on the first strands:
`(1_{i^{(n)}} ⊗ 1) 1_{i^{(n+1)}} = 1_{i^{(n+1)}}`. -/
theorem idem_mul_idem_succ (s' n' : ℕ) :
    idem ε s n X T s' n' * idem ε s n X T s' (n' + 1) = idem ε s n X T s' (n' + 1) := by
  have h := hF.idem_mul_idem s' n'
  simp only [idem] at h ⊢
  rw [wb_succ_eq_wb_mul_chR hF.isBraidFamily_dem, ← mul_assoc, h]

/-- HW (5.25), KL II (10), with the sub-block on the last strands:
`(1 ⊗ 1_{i^{(n)}}) 1_{i^{(n+1)}} = 1_{i^{(n+1)}}`. -/
theorem idem_succ_mul_idem_succ (s' n' : ℕ) :
    idem ε s n X T (s' + 1) n' * idem ε s n X T s' (n' + 1) = idem ε s n X T s' (n' + 1) := by
  have h := hF.idem_mul_idem (s' + 1) n'
  simp only [idem] at h ⊢
  rw [wb_succ_eq_wb_mul_chL hF.isBraidFamily_dem, ← mul_assoc, h]

theorem idem_succ_mul_idem (s' n' : ℕ) :
    idem ε s n X T s' (n' + 1) * idem ε s n X T s' n' = idem ε s n X T s' (n' + 1) := by
  have h := hF.idem_mul_idem s' n'
  simp only [idem] at h ⊢
  rw [wb_succ, mul_assoc, h]

theorem idem_succ_mul_idem_succ' (s' n' : ℕ) :
    idem ε s n X T s' (n' + 1) * idem ε s n X T (s' + 1) n' = idem ε s n X T s' (n' + 1) := by
  have h := hF.idem_mul_idem (s' + 1) n'
  simp only [idem] at h ⊢
  rw [wb_succ_eq_chR_mul_wb hF.isBraidFamily_dem, mul_assoc, h]

/-! ### Powers of dots past a crossing -/

/-- `T_j X_j^a = Σ_{b<a} ε^b X_{j+1}^b X_j^{a-1-b} + ε^a X_{j+1}^a T_j`. -/
theorem tx_pow {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (a : ℕ) (r : B) :
    T j * (X j ^ a * r) = (∑ b ∈ Finset.range a,
      ((ε : ℤ) ^ b) • (X (j + 1) ^ b * (X j ^ (a - 1 - b) * r))) +
      ((ε : ℤ) ^ a) • (X (j + 1) ^ a * (T j * r)) := by
  induction a generalizing r with
  | zero => simp
  | succ a ih =>
    have hp : ∀ (b : ℕ) (r : B), X (j + 1) * (X (j + 1) ^ b * r) = X (j + 1) ^ (b + 1) * r :=
      fun b r => by rw [← mul_assoc, ← pow_succ']
    rw [pow_succ', mul_assoc, hF.tx_self h₁ h₂, ih, Finset.sum_range_succ']
    simp only [mul_add, Finset.mul_sum, smul_add, Finset.smul_sum, mul_smul_comm, smul_smul, hp,
      ← pow_succ', pow_zero, one_smul, one_mul, Nat.sub_zero, Nat.add_sub_cancel]
    simp only [Nat.sub_sub, Nat.add_comm 1]
    abel

/-- `T_j X_{j+1}^a = -Σ_{b<a} ε^{b+1} X_j^b X_{j+1}^{a-1-b} + ε^a X_j^a T_j`. -/
theorem tx_succ_pow {j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (a : ℕ) (r : B) :
    T j * (X (j + 1) ^ a * r) = (∑ b ∈ Finset.range a,
      (-(ε : ℤ) ^ (b + 1)) • (X j ^ b * (X (j + 1) ^ (a - 1 - b) * r))) +
      ((ε : ℤ) ^ a) • (X j ^ a * (T j * r)) := by
  induction a generalizing r with
  | zero => simp
  | succ a ih =>
    have hp : ∀ (b : ℕ) (r : B), X j * (X j ^ b * r) = X j ^ (b + 1) * r :=
      fun b r => by rw [← mul_assoc, ← pow_succ']
    rw [pow_succ', mul_assoc, hF.tx_succ h₁ h₂, ih, Finset.sum_range_succ']
    simp only [mul_add, Finset.mul_sum, smul_add, Finset.smul_sum, mul_smul_comm, smul_smul, hp,
      ← pow_succ', pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_cancel, mul_neg, zero_add,
      pow_one, neg_smul]
    have hs : ∀ b ∈ Finset.range a, -((ε : ℤ) ^ (b + 1 + 1) • (X j ^ (b + 1) *
        (X (j + 1) ^ (a - (b + 1)) * r))) = (ε : ℤ) • -((ε : ℤ) ^ (b + 1) • (X j ^ (b + 1) *
        (X (j + 1) ^ (a - 1 - b) * r))) := fun b _ => by
      rw [show a - (b + 1) = a - 1 - b by omega, smul_neg, smul_smul, ← pow_succ']
    rw [Finset.sum_congr rfl hs]
    abel

/-! ### Chains of crossings -/

theorem signComm_t_t {j l : ℕ} (h₁ : s ≤ j) (h₂ : s ≤ l) (h₃ : j + 1 < s + n)
    (h₄ : l + 1 < s + n) (h : j + 1 < l ∨ l + 1 < j) : SignComm (T j) (T l) := by
  rcases h with h | h
  · exact ⟨ε, hF.t_comm j l h₁ h h₄⟩
  · exact SignComm.symm (show SignComm (T l) (T j) from ⟨ε, hF.t_comm l j h₂ h h₃⟩)

theorem signComm_x_t {a j : ℕ} (ha₁ : s ≤ a) (ha₂ : a < s + n) (h₁ : s ≤ j)
    (h₂ : j + 1 < s + n) (h₃ : a ≠ j) (h₄ : a ≠ j + 1) : SignComm (X a) (T j) :=
  ⟨ε, hF.x_t_comm a j ha₁ ha₂ h₁ h₂ h₃ h₄⟩

theorem signComm_x_x {a b : ℕ} (ha₁ : s ≤ a) (ha₂ : a < s + n) (hb₁ : s ≤ b) (hb₂ : b < s + n)
    (h : a ≠ b) : SignComm (X a) (X b) :=
  ⟨ε, hF.x_comm a b ha₁ ha₂ hb₁ hb₂ h⟩

/-- A crossing far from a chain commutes with it up to a sign. -/
theorem signComm_t_chL {j p l : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (hp : s ≤ p)
    (hl : p + l < s + n) (h : j + 1 < p ∨ p + l < j) : SignComm (T j) (chL T p l) :=
  SignComm.wp fun l' hl' => by
    rw [List.mem_range'_1] at hl'
    exact hF.signComm_t_t h₁ (by omega) h₂ (by omega) (by omega)

theorem signComm_t_chR {j p l : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (hp : s ≤ p)
    (hl : p + l < s + n) (h : j + 1 < p ∨ p + l < j) : SignComm (T j) (chR T p l) :=
  SignComm.wp fun l' hl' => by
    rw [List.mem_reverse, List.mem_range'_1] at hl'
    exact hF.signComm_t_t h₁ (by omega) h₂ (by omega) (by omega)

/-- A dot away from a chain commutes with it up to a sign. -/
theorem signComm_x_chR {a p l : ℕ} (ha₁ : s ≤ a) (ha₂ : a < s + n) (hp : s ≤ p)
    (hl : p + l < s + n) (h : a < p ∨ p + l < a) : SignComm (X a) (chR T p l) :=
  SignComm.wp fun l' hl' => by
    rw [List.mem_reverse, List.mem_range'_1] at hl'
    exact hF.signComm_x_t ha₁ ha₂ (by omega) (by omega) (by omega) (by omega)

theorem signComm_x_chL {a p l : ℕ} (ha₁ : s ≤ a) (ha₂ : a < s + n) (hp : s ≤ p)
    (hl : p + l < s + n) (h : a < p ∨ p + l < a) : SignComm (X a) (chL T p l) :=
  SignComm.wp fun l' hl' => by
    rw [List.mem_range'_1] at hl'
    exact hF.signComm_x_t ha₁ ha₂ (by omega) (by omega) (by omega) (by omega)

/-- Sliding a crossing through `T_p ⋯ T_{p+l-1}`, up to a sign. -/
theorem t_mul_chL {p l j : ℕ} (hp : s ≤ p) (hl : p + l < s + n) (h₁ : p ≤ j)
    (h₂ : j + 2 ≤ p + l) : ∃ u : ℤˣ, T (j + 1) * chL T p l = (u : ℤ) • (chL T p l * T j) := by
  induction l generalizing p with
  | zero => omega
  | succ l ih =>
    rw [chL_succ]
    rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
    · obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      obtain ⟨u, hu⟩ := hF.signComm_t_chL (j := p) (p := p + 1 + 1) (l := l) hp (by omega)
        (by omega) (by omega) (by omega)
      refine ⟨u, ?_⟩
      rw [chL_succ]
      simp only [mul_assoc]
      rw [hF.braid_tail hp (by omega), hu, mul_smul_comm, mul_smul_comm]
    · obtain ⟨u, hu⟩ := ih (p := p + 1) (by omega) (by omega) (by omega) (by omega)
      refine ⟨ε * u, ?_⟩
      rw [hF.tt_far' hp (by omega) (by omega), hu, mul_smul_comm, smul_smul, Units.val_mul,
        mul_assoc]

/-- Sliding a crossing through `T_{p+l-1} ⋯ T_p`, up to a sign. -/
theorem t_mul_chR {p l j : ℕ} (hp : s ≤ p) (hl : p + l < s + n) (h₁ : p ≤ j)
    (h₂ : j + 2 ≤ p + l) : ∃ u : ℤˣ, T j * chR T p l = (u : ℤ) • (chR T p l * T (j + 1)) := by
  induction l generalizing p with
  | zero => omega
  | succ l ih =>
    rw [chR_succ]
    rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
    · obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      obtain ⟨u, hu⟩ := hF.signComm_t_chR (j := p) (p := p + 1 + 1) (l := l) hp (by omega)
        (by omega) (by omega) (by omega)
      refine ⟨u, ?_⟩
      have hb : T p * (T (p + 1) * T p) = T (p + 1) * (T p * T (p + 1)) := by
        simp only [← mul_assoc, hF.braid p hp (by omega)]
      rw [chR_succ, ← mul_assoc, ← mul_assoc, hu, smul_mul_assoc, smul_mul_assoc]
      simp only [mul_assoc, hb]
    · obtain ⟨u, hu⟩ := ih (p := p + 1) (by omega) (by omega) (by omega) (by omega)
      refine ⟨u * ε, ?_⟩
      have hc : T (j + 1) * T p = (ε : ℤ) • (T p * T (j + 1)) := by
        rw [hF.t_comm p (j + 1) hp (by omega) (by omega), eps_smul_eps_smul]
      rw [← mul_assoc, hu, smul_mul_assoc, mul_assoc, hc, mul_smul_comm, smul_smul,
        Units.val_mul, mul_assoc]

/-- HW (5.26)–(5.27), KL II (11): `1_{i^{(n+1)}} T_s ⋯ T_{s+n-1} (1_{i^{(n)}} ⊗ 1) =
T_s ⋯ T_{s+n-1} (1_{i^{(n)}} ⊗ 1)`, the sub-block on the first `n` strands. -/
theorem idem_mul_chL_mul_idem {s' l : ℕ} (hs : s ≤ s') (hn : s' + l + 1 ≤ s + n) :
    idem ε s n X T s' (l + 1) * (chL T s' l * idem ε s n X T s' l) =
      chL T s' l * idem ε s n X T s' l := by
  refine idem_mul_of_forall fun r h₁ h₂ => ?_
  rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
  · obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    rw [chL_succ, ← mul_assoc, ← mul_assoc, hF.dem_mul_t hs (by omega)]
  · obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨u, hu⟩ := hF.t_mul_chL (p := s') (l := l) (j := r) hs (by omega) (by omega) (by omega)
    rw [hF.dem_eq (by omega) (by omega), sub_mul, one_mul, mul_assoc, ← mul_assoc (T (r + 1)),
      hu, smul_mul_assoc, mul_assoc, hF.t_mul_idem hs (by omega) (by omega) (by omega),
      mul_zero, smul_zero, mul_zero, sub_zero]

/-- HW (5.26)–(5.27), KL II (11): `1_{i^{(n+1)}} T_{s+n-1} ⋯ T_s (1 ⊗ 1_{i^{(n)}}) =
T_{s+n-1} ⋯ T_s (1 ⊗ 1_{i^{(n)}})`, the sub-block on the last `n` strands. -/
theorem idem_mul_chR_mul_idem {s' l : ℕ} (hs : s ≤ s') (hn : s' + l + 1 ≤ s + n) :
    idem ε s n X T s' (l + 1) * (chR T s' l * idem ε s n X T (s' + 1) l) =
      chR T s' l * idem ε s n X T (s' + 1) l := by
  refine idem_mul_of_forall fun r h₁ h₂ => ?_
  by_cases hr : r + 2 ≤ s' + l
  · obtain ⟨u, hu⟩ := hF.t_mul_chR (p := s') (l := l) (j := r) hs (by omega) h₁ hr
    rw [hF.dem_eq (by omega) (by omega), sub_mul, one_mul, mul_assoc, ← mul_assoc (T r),
      hu, smul_mul_assoc, mul_assoc, hF.t_mul_idem (by omega) (by omega) (by omega) (by omega),
      mul_zero, smul_zero, mul_zero, sub_zero]
  · obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    obtain rfl : r = s' + l := by omega
    rw [chR_succ', ← mul_assoc, ← mul_assoc, hF.dem_mul_t (by omega) (by omega)]

/-! ### Annihilators -/

/-- HW Lemma 5.8, KL II (12), in the Demazure normalization:
`T_{s+n-1} ⋯ T_s X_s^a 1_{i^{(n+1)}}` is zero for `a < n` and `ε^{n(n-1)/2} 1_{i^{(n+1)}}` for
`a = n`. -/
theorem chR_mul_x_pow_mul_idem {s' l a : ℕ} (hs : s ≤ s') (hn : s' + l + 1 ≤ s + n)
    (ha : a ≤ l) :
    chR T s' l * (X s' ^ a * idem ε s n X T s' (l + 1)) =
      if a = l then ((ε : ℤ) ^ l.choose 2) • idem ε s n X T s' (l + 1) else 0 := by
  induction l generalizing s' a with
  | zero =>
    obtain rfl : a = 0 := by omega
    simp
  | succ l ih =>
    set E := idem ε s n X T s' (l + 1 + 1)
    have hE : idem ε s n X T (s' + 1) (l + 1) * E = E := hF.idem_succ_mul_idem_succ s' (l + 1)
    have hterm : ∀ b ∈ Finset.range a, chR T (s' + 1) l *
        (((ε : ℤ) ^ b) • (X (s' + 1) ^ b * (X s' ^ (a - 1 - b) * E))) =
        if b = l then ((ε : ℤ) ^ b * (ε : ℤ) ^ l.choose 2) • E else 0 := by
      intro b hb
      rw [Finset.mem_range] at hb
      rw [mul_smul_comm]
      by_cases hbl : b = l
      · subst hbl
        obtain rfl : a = b + 1 := by omega
        rw [ite_eq_left rfl, show b + 1 - 1 - b = 0 by omega, pow_zero, one_mul,
          show X (s' + 1) ^ b * E = X (s' + 1) ^ b * idem ε s n X T (s' + 1) (b + 1) * E by
            rw [mul_assoc, hE],
          ← mul_assoc, ih (s' := s' + 1) (by omega) (by omega) le_rfl, ite_eq_left rfl,
          smul_mul_assoc, hE,
          smul_smul]
      · rw [ite_eq_right hbl]
        obtain ⟨u, hu⟩ := (((hF.signComm_x_x (a := s') (b := s' + 1) hs (by omega) (by omega)
          (by omega) (by omega)).pow_left (a - 1 - b)).pow_right b).exists_mul_mul E
        obtain ⟨v, hv⟩ := ((hF.signComm_x_chR (a := s') (p := s' + 1) (l := l) hs (by omega)
          (by omega) (by omega) (by omega)).pow_left (a - 1 - b)).exists_mul_mul
          (X (s' + 1) ^ b * E)
        rw [hu, mul_smul_comm, hv, ← hE, ← mul_assoc (X (s' + 1) ^ b), ← mul_assoc (chR T _ _),
          ih (s' := s' + 1) (by omega) (by omega) (by omega), ite_eq_right hbl]
        simp only [zero_mul, mul_zero, smul_zero]
    rw [chR_succ, mul_assoc, hF.tx_pow hs (by omega), hF.t_mul_idem hs hn le_rfl (by omega),
      mul_zero, smul_zero, add_zero, Finset.mul_sum, Finset.sum_congr rfl hterm]
    rcases Nat.lt_or_ge a (l + 1) with hal | hal
    · rw [ite_eq_right (by omega), Finset.sum_eq_zero fun b hb => by
        rw [Finset.mem_range] at hb; rw [ite_eq_right (by omega)]]
    · obtain rfl : a = l + 1 := by omega
      rw [ite_eq_left rfl, Finset.sum_range_succ, Finset.sum_eq_zero fun b hb => by
        rw [Finset.mem_range] at hb; rw [ite_eq_right (by omega)], ite_eq_left rfl, zero_add,
        ← pow_add,
        Nat.choose_succ_succ', Nat.choose_one_right]

/-- HW Lemma 5.8, KL II (13), in the Demazure normalization:
`T_s ⋯ T_{s+n-1} X_{s+n}^a 1_{i^{(n+1)}}` is zero for `a < n` and
`(-1)^n ε^{n(n+1)/2} 1_{i^{(n+1)}}` for `a = n`. -/
theorem chL_mul_x_pow_mul_idem {s' l a : ℕ} (hs : s ≤ s') (hn : s' + l + 1 ≤ s + n)
    (ha : a ≤ l) :
    chL T s' l * (X (s' + l) ^ a * idem ε s n X T s' (l + 1)) =
      if a = l then ((-1 : ℤ) ^ l * (ε : ℤ) ^ (l + 1).choose 2) • idem ε s n X T s' (l + 1)
      else 0 := by
  induction l generalizing a with
  | zero =>
    obtain rfl : a = 0 := by omega
    simp
  | succ l ih =>
    set E := idem ε s n X T s' (l + 1 + 1)
    have hE : idem ε s n X T s' (l + 1) * E = E := hF.idem_mul_idem_succ s' (l + 1)
    have hterm : ∀ b ∈ Finset.range a, chL T s' l *
        ((-(ε : ℤ) ^ (b + 1)) • (X (s' + l) ^ b * (X (s' + l + 1) ^ (a - 1 - b) * E))) =
        if b = l then (-(ε : ℤ) ^ (b + 1) * ((-1 : ℤ) ^ l * (ε : ℤ) ^ (l + 1).choose 2)) • E
        else 0 := by
      intro b hb
      rw [Finset.mem_range] at hb
      rw [mul_smul_comm]
      by_cases hbl : b = l
      · subst hbl
        obtain rfl : a = b + 1 := by omega
        rw [ite_eq_left rfl, show b + 1 - 1 - b = 0 by omega, pow_zero, one_mul,
          show X (s' + b) ^ b * E = X (s' + b) ^ b * idem ε s n X T s' (b + 1) * E by
            rw [mul_assoc, hE],
          ← mul_assoc, ih (by omega) le_rfl, ite_eq_left rfl, smul_mul_assoc, hE, smul_smul]
      · rw [ite_eq_right hbl]
        obtain ⟨u, hu⟩ := (((hF.signComm_x_x (a := s' + l + 1) (b := s' + l) (by omega)
          (by omega) (by omega) (by omega) (by omega)).pow_left (a - 1 - b)).pow_right
          b).exists_mul_mul E
        obtain ⟨v, hv⟩ := ((hF.signComm_x_chL (a := s' + l + 1) (p := s') (l := l) (by omega)
          (by omega) hs (by omega) (by omega)).pow_left (a - 1 - b)).exists_mul_mul
          (X (s' + l) ^ b * E)
        rw [hu, mul_smul_comm, hv, ← hE, ← mul_assoc (X (s' + l) ^ b), ← mul_assoc (chL T _ _),
          ih (by omega) (by omega), ite_eq_right hbl]
        simp only [zero_mul, mul_zero, smul_zero]
    rw [chL_succ', mul_assoc, show s' + (l + 1) = s' + l + 1 from rfl,
      hF.tx_succ_pow (j := s' + l) (by omega) (by omega),
      hF.t_mul_idem hs hn (by omega) (by omega), mul_zero, smul_zero, add_zero, Finset.mul_sum,
      Finset.sum_congr rfl hterm]
    rcases Nat.lt_or_ge a (l + 1) with hal | hal
    · rw [ite_eq_right (by omega), Finset.sum_eq_zero fun b hb => by
        rw [Finset.mem_range] at hb; rw [ite_eq_right (by omega)]]
    · obtain rfl : a = l + 1 := by omega
      rw [ite_eq_left rfl, Finset.sum_range_succ, Finset.sum_eq_zero fun b hb => by
        rw [Finset.mem_range] at hb; rw [ite_eq_right (by omega)], ite_eq_left rfl, zero_add,
        Nat.choose_succ_succ' (l + 1) 1, Nat.choose_one_right, pow_add]
      congr 1
      ring

end IsSignedNilHeckeFamily

end OddMath.QuiverHecke.SignedNilHecke
