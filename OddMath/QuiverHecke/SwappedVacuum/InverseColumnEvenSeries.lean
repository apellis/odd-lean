/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuum.InverseColumnOddSeries

/-! # The even-colour inverse-column moments are the substituted series

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8 (the left-bubble series of `AdjunctionBubbleSeries.left_even`).

At an even colour the reservoir moments `T_l = u ≫ y^(N-1+l) ≫ ell` are the
coefficients of `A(z) = 1/E(-z)` and the probe is `(x - 1)^P` with
`P = H + N`, whose reversed coefficients form `(1 - z)^P`. With `q = 1`,
`reservoirSeries_mul_probe_mul_column` gives `T(z)(1 - z)^P B(z) = 1`, hence

  `B(z) = E(-z)(1 - z)^(-P)`,

the substituted series of `left_even` (`even_inverse_column_moments`). See
`docs/Nondegeneracy/InverseColumnMoments.md`.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedVacuum

open Finset PowerSeries

universe u

section Probe

variable {k : Type*} [CommRing k]

/-- The even probe `(x - 1)^P` is monic of degree `P`. -/
theorem sub_one_pow_coeff_top (P : ℕ) :
    ((Polynomial.X - 1 : Polynomial k) ^ P).coeff P = 1 := by
  have h := Polynomial.coeff_X_add_C_pow (-1 : k) P P
  simpa only [map_neg, map_one, sub_eq_add_neg, Nat.choose_self, Nat.cast_one,
    Nat.sub_self, pow_zero, mul_one] using h

/-- The reversed coefficients of the even probe `(x - 1)^P` form `(1 - z)^P`. -/
theorem reversed_sub_one_pow (P : ℕ) :
    PowerSeries.mk (fun r => if r ≤ P then
        ((Polynomial.X - 1 : Polynomial k) ^ P).coeff (P - r) else 0) =
      (1 - X : PowerSeries k) ^ P := by
  have hpow : (1 - X : PowerSeries k) ^ P =
      rescale (-1 : k) ((((1 + Polynomial.X) ^ P : Polynomial k) : PowerSeries k)) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X, map_pow,
      map_add, map_one, rescale_X, map_neg, map_one, neg_one_mul, ← sub_eq_add_neg]
  have hX : (Polynomial.X - 1 : Polynomial k) = Polynomial.X + Polynomial.C (-1) := by
    rw [map_neg, map_one, sub_eq_add_neg]
  ext n
  rw [coeff_mk, hpow, coeff_rescale, Polynomial.coeff_coe, add_comm (1 : Polynomial k),
    Polynomial.coeff_X_add_one_pow]
  split_ifs with h
  · rw [hX, Polynomial.coeff_X_add_C_pow, show P - (P - n) = n by omega,
      Nat.choose_symm h]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

end Probe

variable {I X' : Type u} [AddCommGroup X'] {k : Type u} [CommRing k]

/-- At an even colour the probe inverse series `(1 - w)^M`. -/
theorem probeSeriesInv_even (D : SKM.Datum I X') (M : I → ℕ) (i : I) (hi : D.parity i = 0) :
    SKM.SYM.probeSeriesInv D k M i = (1 - X : PowerSeries k) ^ M i := by
  rw [SKM.SYM.probeSeriesInv, SKM.SYM.colourScale, ite_eq_right (by rw [hi]; decide)]
  simp

/-- **Even-colour inverse-column moments.** Under the hypotheses of
`reservoirSeries_mul_probe_mul_column` with `q = 1` and the even probe
`(x - 1)^P` (`H + N = P`), if the reservoir moments are the coefficients of
`A = 1/E(-z)` mapped along `φ`, then the column moments `B_(H-1+s)` are the
coefficients of the substituted series `E(-z)(1 - z)^(-P)`. -/
theorem even_inverse_column_moments (D : SKM.Datum I X') {R : Type*} [Ring R] [Algebra k R]
    (φ : MvPolynomial (I × ℕ) k →ₐ[k] R) (P : I → ℕ) (i : I) (hi : D.parity i = 0)
    (H N : ℕ) (hH : 0 < H) (hN : 0 < N) (hP : H + N = P i)
    (b t : ℕ → R)
    (hb : ∀ j < H, b j = if j + 1 = H then 1 else 0)
    (ht : ∀ j < N, t j = if j + 1 = N then 1 else 0)
    (hrel : ∀ d, ∑ n ∈ range (H + N + 1),
      ((Polynomial.X - 1 : Polynomial k) ^ P i).coeff n •
        ∑ j ∈ range n, (1 : k) ^ (n - j) • (t (d + (n - 1 - j)) * b j) = 0)
    (hhigh : ∀ m, ∑ n ∈ range (H + N + 1),
      ((Polynomial.X - 1 : Polynomial k) ^ P i).coeff n • b (n + m) = 0)
    (hT : PowerSeries.mk (fun l => t (N - 1 + l)) =
      PowerSeries.map φ.toRingHom (invOfUnit (rescale (-1) (SKM.SYM.generatorSeries k i)) 1))
    (s : ℕ) :
    b (H - 1 + s) = φ (coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k P) i)) := by
  set c : ℕ → k := fun n => ((Polynomial.X - 1 : Polynomial k) ^ P i).coeff n
  set Gs := rescale (-1 : MvPolynomial (I × ℕ) k) (SKM.SYM.generatorSeries k i)
  have hGs0 : constantCoeff Gs = ((1 : (MvPolynomial (I × ℕ) k)ˣ) : _) :=
    VacuumSeries.constantCoeff_rescale_generatorSeries k i
  set f : MvPolynomial (I × ℕ) k →+* R := φ.toRingHom
  set A := PowerSeries.map f (invOfUnit Gs 1)
  set G := PowerSeries.map f Gs
  have hAG : A * G = 1 := by rw [← map_mul, invOfUnit_mul _ _ hGs0, map_one]
  have hA0 : constantCoeff A = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_invOfUnit]
    simp
  have hsupp : ∀ r ≤ H + N, (1 : k) ^ r * c (H + N - r) = c (H + N - r) := fun r _ => by
    rw [one_pow, one_mul]
  have hc : c (H + N) = 1 := by rw [hP]; exact sub_one_pow_coeff_top (P i)
  have hser := reservoirSeries_mul_probe_mul_column 1 (by norm_num) H N hH hN c hc b t hsupp
    hb ht hrel hhigh
  set Bq := PowerSeries.mk (fun m => (1 : k) ^ m • b (H - 1 + m))
  have hhat : PowerSeries.mk (fun r => if r ≤ H + N then algebraMap k R (c (H + N - r)) else 0) =
      PowerSeries.map (algebraMap k R) ((1 - X : PowerSeries k) ^ P i) := by
    rw [← reversed_sub_one_pow (P i), hP]
    ext n
    simp only [coeff_mk, coeff_map]
    split_ifs <;> simp [c]
  rw [hhat] at hser
  have hT' : PowerSeries.mk (fun l => t (N - 1 + l)) = A * (1 + C (0 : R) * X) := by
    rw [hT, map_zero, zero_mul, add_zero, mul_one]
  have hY := eq_of_mul_one_add_square_zero (0 : R) (mul_zero 0) hAG hA0 hT' hser
  rw [map_zero, zero_mul, sub_zero, one_mul] at hY
  set Q := PowerSeries.map (algebraMap k R) (SKM.SYM.probeSeries D k P i)
  have hQ : Q * PowerSeries.map (algebraMap k R) ((1 - X : PowerSeries k) ^ P i) = 1 := by
    rw [← map_mul, ← probeSeriesInv_even D P i hi, SKM.SYM.probeSeries_mul_inv, map_one]
  have hB : Bq = PowerSeries.map f
      (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k P) i) := by
    calc Bq = Q * (PowerSeries.map (algebraMap k R) ((1 - X : PowerSeries k) ^ P i) * Bq) := by
          rw [← mul_assoc, hQ, one_mul]
      _ = Q * G := by rw [hY]
      _ = G * Q := (commute_map_algebraMap _ G).eq
      _ = _ := by
          rw [VacuumSeries.substitutedSeries, map_mul]
          congr 1
          rw [← RingHom.comp_apply, ← PowerSeries.map_comp]
          ext x
          simp [f, Q]
  have h := congrArg (coeff s) hB
  rw [coeff_mk, one_pow, one_smul, coeff_map] at h
  exact h

end OddMath.QuiverHecke.SwappedVacuum
