/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuum.InverseCapSeries
import OddMath.QuiverHecke.SwappedVacuum.InverseColumnEvenSeries

/-! # Nonpositive-height cap moments are the reciprocal substituted series

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8. This is equation (12) of
`docs/Nondegeneracy/SwappedVacuumNonpositiveBubbles.md`, at negative and at
zero height. With the reservoir moments in the form proved for the vacuum
(`tensorPowerVacuumCap_moment_even`, `tensorPowerVacuumCap_moment_odd`),

* odd colour, probe `(x² + 1)^M`: `T(z) = A(z²)(1 + e z)` with `A = 1/C(-w)`,
  and the cap moments satisfy `K(z) = (1 + z²)^M A(z²)(1 + e z)`, so
  `K_(2r)` and `K_(2r+1)` are the coefficients of `(1 + w)^M / C(-w)` and
  those coefficients times `e`;
* even colour, probe `(x - 1)^P`: `T(z) = 1/E(-z)` and
  `K(z) = (1 - z)^P / E(-z)`.

The series `(1 + w)^M / C(-w)` and `(1 - z)^P / E(-z)` are
`VacuumSeries.momentSeries` at `SKM.SYM.probeSeriesInv`, the reciprocals of
the positive-height substituted series. Neither `e² = 0` nor any
commutation of `e` with the polynomial coefficients is used. See
`docs/Nondegeneracy/InverseCapSeries.md`.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedVacuum

open Finset PowerSeries

universe u u₁ v₁

/-- The coefficients of `F(z²)(1 + e z)`. -/
theorem coeff_expand_mul_one_add {S R : Type*} [CommRing S] [Ring R] (φ : S →+* R)
    (F : PowerSeries S) (e : R) (s : ℕ) :
    coeff (2 * s) (PowerSeries.map φ (expand 2 two_ne_zero F) * (1 + C e * X)) =
        φ (coeff s F) ∧
      coeff (2 * s + 1) (PowerSeries.map φ (expand 2 two_ne_zero F) * (1 + C e * X)) =
        φ (coeff s F) * e := by
  constructor
  · rw [mul_add, mul_one, map_add, ← mul_assoc, coeff_map, coeff_expand_mul]
    rcases s with _ | s
    · rw [mul_zero, coeff_zero_mul_X, add_zero]
    · rw [show 2 * (s + 1) = (2 * s + 1) + 1 by ring, coeff_succ_mul_X, coeff_mul_C, coeff_map,
        coeff_expand_of_not_dvd 2 two_ne_zero _ (by omega), map_zero, zero_mul, add_zero]
  · rw [mul_add, mul_one, map_add, ← mul_assoc, coeff_succ_mul_X, coeff_mul_C, coeff_map,
      coeff_map, coeff_expand_mul, coeff_expand_of_not_dvd 2 two_ne_zero _ (by omega), map_zero,
      zero_add]

/-- The odd probe `(x² + 1)^M` has no odd coefficients, so it satisfies the
`q = -1` support condition of the signed slide. -/
theorem square_add_one_coeff_mul_neg_one_pow {k : Type*} [CommRing k] (M n : ℕ) :
    ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ M).coeff n * (-1 : k) ^ n =
      ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ M).coeff n := by
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, mul_one]
  · have he : (Polynomial.X ^ 2 + 1 : Polynomial k) ^ M =
        Polynomial.expand k 2 ((Polynomial.X + 1) ^ M) := by
      simp only [map_pow, map_add, Polynomial.expand_X, map_one]
    have hnd : ¬ 2 ∣ n := by
      obtain ⟨m, hm⟩ := ho
      omega
    rw [he, Polynomial.coeff_expand (by decide), ite_eq_right hnd, zero_mul]

variable {I X' : Type u} [AddCommGroup X'] {k : Type u} [CommRing k]

/-- **Odd-colour cap moments.** If the cap moments are the reversed-probe
convolution `K(z) = (1 + z²)^M T(z)` and `T(z) = A(z²)(1 + e z)` with
`A = 1/C(-w)` mapped along `φ`, then `K_(2r)` is the `r`th coefficient of
`(1 + w)^M / C(-w)` and `K_(2r+1)` is that coefficient times `e`. -/
theorem odd_cap_moments (D : SKM.Datum I X') {R : Type*} [Ring R] [Algebra k R]
    (φ : MvPolynomial (I × ℕ) k →ₐ[k] R) (P : I → ℕ) (i : I) (hi : D.parity i = 1)
    (B : ℕ) (e : R) (K t : ℕ → R)
    (hK : PowerSeries.mk K = PowerSeries.mk (fun r => if r ≤ 2 * P i then
        algebraMap k R (((Polynomial.X ^ 2 + 1 : Polynomial k) ^ P i).coeff (2 * P i - r))
        else 0) * PowerSeries.mk (fun l => t (B + l)))
    (hT : PowerSeries.mk (fun l => t (B + l)) =
      PowerSeries.map φ.toRingHom (expand 2 two_ne_zero
        (invOfUnit (rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) * (1 + C e * X))
    (r : ℕ) :
    K (2 * r) = φ (coeff r (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k P) i)) ∧
      K (2 * r + 1) =
        φ (coeff r (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k P) i)) * e := by
  have hhat : PowerSeries.mk (fun r => if r ≤ 2 * P i then
      algebraMap k R (((Polynomial.X ^ 2 + 1 : Polynomial k) ^ P i).coeff (2 * P i - r))
      else 0) = PowerSeries.map (algebraMap k R)
        (expand 2 two_ne_zero ((1 + X : PowerSeries k) ^ P i)) := by
    rw [← reversed_square_add_one (P i)]
    ext n
    simp only [coeff_mk, coeff_map]
    split_ifs <;> simp
  have hM : PowerSeries.map φ.toRingHom (expand 2 two_ne_zero
      (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k P) i)) =
      PowerSeries.map (algebraMap k R) (expand 2 two_ne_zero ((1 + X : PowerSeries k) ^ P i)) *
        PowerSeries.map φ.toRingHom (expand 2 two_ne_zero
          (invOfUnit (rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) := by
    rw [VacuumSeries.momentSeries, probeSeriesInv_odd D P i hi, map_mul, map_mul]
    congr 1
    rw [← map_expand, ← RingHom.comp_apply, ← PowerSeries.map_comp,
      show φ.toRingHom.comp (algebraMap k (MvPolynomial (I × ℕ) k)) = algebraMap k R from
        RingHom.ext fun a => by simp]
  have hKser : PowerSeries.mk K = PowerSeries.map φ.toRingHom (expand 2 two_ne_zero
      (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k P) i)) * (1 + C e * X) := by
    rw [hK, hhat, hT, hM, mul_assoc]
  have h := coeff_expand_mul_one_add φ.toRingHom
    (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k P) i) e r
  rw [← hKser, coeff_mk, coeff_mk] at h
  exact h

/-- **Even-colour cap moments.** If `K(z) = (1 - z)^P T(z)` and `T = 1/E(-z)`
mapped along `φ`, then `K_l` is the `l`th coefficient of `(1 - z)^P / E(-z)`. -/
theorem even_cap_moments (D : SKM.Datum I X') {R : Type*} [Ring R] [Algebra k R]
    (φ : MvPolynomial (I × ℕ) k →ₐ[k] R) (P : I → ℕ) (i : I) (hi : D.parity i = 0)
    (B : ℕ) (K t : ℕ → R)
    (hK : PowerSeries.mk K = PowerSeries.mk (fun r => if r ≤ P i then
        algebraMap k R (((Polynomial.X - 1 : Polynomial k) ^ P i).coeff (P i - r))
        else 0) * PowerSeries.mk (fun l => t (B + l)))
    (hT : PowerSeries.mk (fun l => t (B + l)) =
      PowerSeries.map φ.toRingHom (invOfUnit (rescale (-1) (SKM.SYM.generatorSeries k i)) 1))
    (l : ℕ) :
    K l = φ (coeff l (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k P) i)) := by
  have hhat : PowerSeries.mk (fun r => if r ≤ P i then
      algebraMap k R (((Polynomial.X - 1 : Polynomial k) ^ P i).coeff (P i - r))
      else 0) = PowerSeries.map (algebraMap k R) ((1 - X : PowerSeries k) ^ P i) := by
    rw [← reversed_sub_one_pow (P i)]
    ext n
    simp only [coeff_mk, coeff_map]
    split_ifs <;> simp
  have hM : PowerSeries.map φ.toRingHom
      (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k P) i) =
      PowerSeries.map (algebraMap k R) ((1 - X : PowerSeries k) ^ P i) *
        PowerSeries.map φ.toRingHom
          (invOfUnit (rescale (-1) (SKM.SYM.generatorSeries k i)) 1) := by
    rw [VacuumSeries.momentSeries, probeSeriesInv_even D P i hi, map_mul]
    congr 1
    ext n
    simp
  have hKser : PowerSeries.mk K = PowerSeries.map φ.toRingHom
      (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k P) i) := by
    rw [hK, hhat, hT, hM]
  have h := congrArg (coeff l) hKser
  rw [coeff_mk, coeff_map] at h
  exact h

section Category

open CategoryTheory SwappedAssembly

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C] {V X Y : C}

end Category

end OddMath.QuiverHecke.SwappedVacuum
