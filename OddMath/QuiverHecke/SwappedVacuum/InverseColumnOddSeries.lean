/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuum.InverseColumnSeries
import OddMath.QuiverHecke.SwappedVacuumBubbleSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.NoncommRing

/-! # The odd-colour inverse-column moments are the substituted series

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8 (the left-bubble series of `AdjunctionBubbleSeries.left_odd`).

At an odd colour the reservoir moments `T_l = u ≫ y^(N-1+l) ≫ ell` are
`T_(2r) = a_r` and `T_(2r+1) = a_r · e`, where `a_r` are the coefficients of
`1/C(-w)` and `e` is the signed odd coefficient, of square zero
(`tensorPowerVacuumCap_moment_even`, `tensorPowerVacuumCap_moment_odd`). So
`T(z) = A(z²)(1 + e z)` with `A(w) C(-w) = 1`. With the odd probe
`(x² + 1)^M`, positive height `H` and `H + N = 2M`,
`reservoirSeries_mul_probe_mul_column` gives `T(z)(1 + z²)^M B(-z) = 1`, hence

  `B(-z) = (1 - e z) · (C(-w) (1 + w)^(-M))|_(w = z²)`.

Thus the even column moments `B_(2s) = a ≫ x^(H-1+2s) ≫ v` are the coefficients
of the substituted series `C(-w)(1 + w)^(-M)`
(`VacuumSeries.substitutedSeries` with `SYM.probeSeries`), and the odd ones
are `e` times them (`odd_inverse_column_moments`). No commutation of `e` with
the polynomial coefficients is needed. See
`docs/Nondegeneracy/InverseColumnMoments.md`.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedVacuum

open Finset PowerSeries

universe u

/-- Power series with scalar coefficients commute with every power series. -/
theorem commute_map_algebraMap {k R : Type*} [CommRing k] [Ring R] [Algebra k R]
    (f : PowerSeries k) (g : PowerSeries R) :
    Commute (PowerSeries.map (algebraMap k R) f) g := by
  show _ * _ = _ * _
  ext n
  rw [coeff_mul, coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
  refine sum_congr rfl fun p _ => ?_
  simp only [Prod.fst_swap, Prod.snd_swap, coeff_map]
  exact Algebra.commutes _ _

/-- If `T = A (1 + e z)` with `e² = 0`, `A G = 1` and `A₀ = 1`, the right
inverse of `T` is `(1 - e z) G`. -/
theorem eq_of_mul_one_add_square_zero {R : Type*} [Ring R] {A G T Y : PowerSeries R}
    (e : R) (he : e * e = 0) (hAG : A * G = 1) (hA0 : constantCoeff A = 1)
    (hT : T = A * (1 + C e * X)) (hTY : T * Y = 1) : Y = (1 - C e * X) * G := by
  have hsq : C e * X * (C e * X) = 0 := by
    calc C e * X * (C e * X) = C e * C e * (X * X) := by
          rw [mul_assoc, ← mul_assoc X, ← (commute_X (C e)).eq]; noncomm_ring
      _ = 0 := by rw [← map_mul, he, map_zero, zero_mul]
  have hkey : (1 + C e * X) * (1 - C e * X) = 1 := by
    calc (1 + C e * X) * (1 - C e * X) = 1 - C e * X * (C e * X) := by noncomm_ring
      _ = 1 := by rw [hsq, sub_zero]
  have hT0 : constantCoeff T = ((1 : Rˣ) : R) := by
    rw [hT, map_mul, hA0, map_add, map_one, map_mul, constantCoeff_X, mul_zero, add_zero,
      one_mul, Units.val_one]
  have h1 : T * ((1 - C e * X) * G) = 1 := by
    rw [hT, mul_assoc, ← mul_assoc (1 + C e * X), hkey, one_mul, hAG]
  have hl := invOfUnit_mul T 1 hT0
  calc Y = (invOfUnit T 1 * T) * Y := by rw [hl, one_mul]
    _ = invOfUnit T 1 * (T * ((1 - C e * X) * G)) := by rw [mul_assoc, hTY, h1]
    _ = (1 - C e * X) * G := by rw [← mul_assoc, hl, one_mul]

section Coefficients

variable {S R : Type*} [CommRing S] [Ring R] (φ : S →+* R) (e : R) (F : PowerSeries S)

theorem coeff_even_one_sub_mul_expand (s : ℕ) :
    coeff (2 * s) ((1 - C e * X) * PowerSeries.map φ (expand 2 two_ne_zero F)) =
      φ (coeff s F) := by
  rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_map, coeff_expand_mul]
  rcases s with _ | s
  · rw [mul_zero, coeff_zero_X_mul, mul_zero, sub_zero]
  · rw [show 2 * (s + 1) = (2 * s + 1) + 1 by ring, coeff_succ_X_mul, coeff_map,
      coeff_expand_of_not_dvd 2 two_ne_zero _ (by omega), map_zero, mul_zero, sub_zero]

theorem coeff_odd_one_sub_mul_expand (s : ℕ) :
    coeff (2 * s + 1) ((1 - C e * X) * PowerSeries.map φ (expand 2 two_ne_zero F)) =
      -(e * φ (coeff s F)) := by
  rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_map, coeff_map,
    coeff_expand_of_not_dvd 2 two_ne_zero _ (by omega), coeff_expand_mul, map_zero, zero_sub]

end Coefficients

/-- The coefficientwise form of the odd reservoir moments gives
`T(z) = A(z²)(1 + e z)`. -/
theorem mk_eq_expand_mul_one_add {S R : Type*} [CommRing S] [Ring R] (φ : S →+* R)
    (A : PowerSeries S) (e : R) (T : ℕ → R)
    (heven : ∀ r, T (2 * r) = φ (coeff r A)) (hodd : ∀ r, T (2 * r + 1) = φ (coeff r A) * e) :
    PowerSeries.mk T = PowerSeries.map φ (expand 2 two_ne_zero A) * (1 + C e * X) := by
  ext n
  rw [coeff_mk, mul_add, mul_one, map_add, ← mul_assoc]
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [heven, coeff_map, coeff_expand_mul]
    rcases r with _ | r
    · rw [mul_zero, coeff_zero_mul_X, add_zero]
    · rw [show 2 * (r + 1) = (2 * r + 1) + 1 by ring, coeff_succ_mul_X, coeff_mul_C, coeff_map,
        coeff_expand_of_not_dvd 2 two_ne_zero _ (by omega), map_zero, zero_mul, add_zero]
  · rw [hodd, coeff_succ_mul_X, coeff_mul_C, coeff_map, coeff_map, coeff_expand_mul,
      coeff_expand_of_not_dvd 2 two_ne_zero _ (by omega), map_zero, zero_add]

section Probe

variable {k : Type*} [CommRing k]

/-- The odd probe `(x² + 1)^M` is monic of degree `2M`. -/
theorem square_add_one_coeff_top (M : ℕ) :
    ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ M).coeff (2 * M) = 1 := by
  have he : (Polynomial.X ^ 2 + 1 : Polynomial k) ^ M =
      Polynomial.expand k 2 ((Polynomial.X + 1) ^ M) := by
    simp only [map_pow, map_add, Polynomial.expand_X, map_one]
  rw [he, Polynomial.coeff_expand_mul' (by decide), Polynomial.coeff_X_add_one_pow,
    Nat.choose_self, Nat.cast_one]

/-- The reversed coefficients of the odd probe `(x² + 1)^M` form the series
`(1 + z²)^M`. -/
theorem reversed_square_add_one (M : ℕ) :
    PowerSeries.mk (fun r => if r ≤ 2 * M then
        ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ M).coeff (2 * M - r) else 0) =
      expand 2 two_ne_zero ((1 + X : PowerSeries k) ^ M) := by
  have hpow : ((1 + X : PowerSeries k) ^ M) = (((1 + Polynomial.X) ^ M : Polynomial k) :
      PowerSeries k) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  have he : (Polynomial.X ^ 2 + 1 : Polynomial k) ^ M =
      Polynomial.expand k 2 ((Polynomial.X + 1) ^ M) := by
    simp only [map_pow, map_add, Polynomial.expand_X, map_one]
  ext n
  rw [coeff_mk, coeff_expand, hpow, Polynomial.coeff_coe, add_comm (1 : Polynomial k),
    Polynomial.coeff_X_add_one_pow]
  split_ifs with h1 h2 h2
  · rw [he, Polynomial.coeff_expand (by decide), ite_eq_left (by omega),
      Polynomial.coeff_X_add_one_pow]
    congr 1
    rw [show (2 * M - n) / 2 = M - n / 2 by omega, Nat.choose_symm (by omega)]
  · rw [he, Polynomial.coeff_expand (by decide), ite_eq_right (by omega)]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  · rfl

end Probe

variable {I X' : Type u} [AddCommGroup X'] {k : Type u} [CommRing k]

/-- At an odd colour the probe inverse series `(1 + w)^M`. -/
theorem probeSeriesInv_odd (D : SKM.Datum I X') (M : I → ℕ) (i : I) (hi : D.parity i = 1) :
    SKM.SYM.probeSeriesInv D k M i = (1 + X : PowerSeries k) ^ M i := by
  rw [SKM.SYM.probeSeriesInv, SKM.SYM.colourScale, ite_eq_left hi, map_sub, rescale_X]
  congr 1
  rw [show (PowerSeries.C (1 : k)) = 1 from map_one _, map_one, map_neg, map_one, neg_one_mul,
    sub_neg_eq_add]

/-- **Odd-colour inverse-column moments.** Under the hypotheses of
`reservoirSeries_mul_probe_mul_column` with `q = -1` and the odd probe
`(x² + 1)^M` (`H + N = 2M`), if the reservoir moments are
`T(z) = A(z²)(1 + e z)` with `A = 1/C(-w)` mapped along `φ` and `e² = 0`, then
the even column moments are the coefficients of the substituted series
`C(-w)(1 + w)^(-M)` and the odd ones are `e` times them. -/
theorem odd_inverse_column_moments (D : SKM.Datum I X') {R : Type*} [Ring R] [Algebra k R]
    (φ : MvPolynomial (I × ℕ) k →ₐ[k] R) (P : I → ℕ) (i : I) (hi : D.parity i = 1)
    (H N : ℕ) (hH : 0 < H) (hN : 0 < N) (hP : H + N = 2 * P i) (e : R) (he : e * e = 0)
    (b t : ℕ → R)
    (hb : ∀ j < H, b j = if j + 1 = H then 1 else 0)
    (ht : ∀ j < N, t j = if j + 1 = N then 1 else 0)
    (hrel : ∀ d, ∑ n ∈ range (H + N + 1),
      ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ P i).coeff n •
        ∑ j ∈ range n, (-1 : k) ^ (n - j) • (t (d + (n - 1 - j)) * b j) = 0)
    (hhigh : ∀ m, ∑ n ∈ range (H + N + 1),
      ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ P i).coeff n • b (n + m) = 0)
    (hT : PowerSeries.mk (fun l => t (N - 1 + l)) =
      PowerSeries.map φ.toRingHom (expand 2 two_ne_zero
        (invOfUnit (rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) * (1 + C e * X))
    (s : ℕ) :
    b (H - 1 + 2 * s) = φ (coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k P) i)) ∧
      b (H + 2 * s) = e * φ (coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k P) i)) := by
  set c : ℕ → k := fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ P i).coeff n
  set Gs := rescale (-1 : MvPolynomial (I × ℕ) k) (SKM.SYM.generatorSeries k i)
  have hGs0 : constantCoeff Gs = ((1 : (MvPolynomial (I × ℕ) k)ˣ) : _) :=
    VacuumSeries.constantCoeff_rescale_generatorSeries k i
  set f : MvPolynomial (I × ℕ) k →+* R := φ.toRingHom
  set A := PowerSeries.map f (expand 2 two_ne_zero (invOfUnit Gs 1))
  set G := PowerSeries.map f (expand 2 two_ne_zero Gs)
  have hAG : A * G = 1 := by
    rw [← map_mul, ← map_mul, invOfUnit_mul _ _ hGs0, map_one, map_one]
  have hA0 : constantCoeff A = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, ← mul_zero 2, coeff_expand_mul,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_invOfUnit]
    simp
  have hsupp : ∀ r ≤ H + N, (-1 : k) ^ r * c (H + N - r) = c (H + N - r) := by
    intro r hr
    rw [hP] at hr ⊢
    exact square_add_one_reversed_support (P i) r hr
  have hc : c (H + N) = 1 := by rw [hP]; exact square_add_one_coeff_top (P i)
  have hser := reservoirSeries_mul_probe_mul_column (-1) (by norm_num) H N hH hN c hc b t hsupp
    hb ht hrel hhigh
  set Bq := PowerSeries.mk (fun m => (-1 : k) ^ m • b (H - 1 + m))
  have hhat : PowerSeries.mk (fun r => if r ≤ H + N then algebraMap k R (c (H + N - r)) else 0) =
      PowerSeries.map (algebraMap k R) (expand 2 two_ne_zero ((1 + X : PowerSeries k) ^ P i)) := by
    rw [← reversed_square_add_one (P i), hP]
    ext n
    simp only [coeff_mk, coeff_map]
    split_ifs <;> simp [c]
  rw [hhat] at hser
  have hY := eq_of_mul_one_add_square_zero e he hAG hA0 hT hser
  -- The inverse probe.
  set Q := PowerSeries.map (algebraMap k R) (expand 2 two_ne_zero (SKM.SYM.probeSeries D k P i))
  have hQ : Q * PowerSeries.map (algebraMap k R)
      (expand 2 two_ne_zero ((1 + X : PowerSeries k) ^ P i)) = 1 := by
    rw [← map_mul, ← map_mul, ← probeSeriesInv_odd D P i hi, SKM.SYM.probeSeries_mul_inv,
      map_one, map_one]
  have hB : Bq = (1 - C e * X) * PowerSeries.map f (expand 2 two_ne_zero
      (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k P) i)) := by
    calc Bq = Q * (PowerSeries.map (algebraMap k R)
          (expand 2 two_ne_zero ((1 + X : PowerSeries k) ^ P i)) * Bq) := by
          rw [← mul_assoc, hQ, one_mul]
      _ = Q * ((1 - C e * X) * G) := by rw [hY]
      _ = (1 - C e * X) * (G * Q) := by
          rw [← mul_assoc, (commute_map_algebraMap _ _).eq, mul_assoc,
            (commute_map_algebraMap _ G).eq]
      _ = _ := by
          congr 1
          rw [VacuumSeries.substitutedSeries, map_mul, map_mul]
          congr 1
          rw [← map_expand, ← RingHom.comp_apply, ← PowerSeries.map_comp]
          ext x
          simp [f, Q]
  constructor
  · have h := congrArg (coeff (2 * s)) hB
    rw [coeff_mk, coeff_even_one_sub_mul_expand, pow_mul, neg_one_sq, one_pow, one_smul] at h
    exact h
  · have h := congrArg (coeff (2 * s + 1)) hB
    rw [coeff_mk, coeff_odd_one_sub_mul_expand, pow_succ, pow_mul, neg_one_sq, one_pow,
      one_mul, neg_one_smul, show H - 1 + (2 * s + 1) = H + 2 * s by omega] at h
    exact neg_injective h

end OddMath.QuiverHecke.SwappedVacuum
