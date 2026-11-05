/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuum.NegativeCapInverse
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! # Moments of the nonpositive-height inverse cap

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8. This formalizes equations (11)–(13) of
`docs/Nondegeneracy/SwappedVacuumNonpositiveBubbles.md` in operator and
power-series form. At height `H = P - N < 0` the prescribed extreme
inverse cap is `λ g(y)` (`negative_inverse_cap_eq_polynomial`); at `H = 0`
the principal inverse satisfies `v j = λ g(y)` (`principal_inverse_cap`).
Writing `T_l = u ≫ y^(N-1+l) ≫ ell` for the reservoir moments and
`ĉ_r = c_(P-r)` for the reversed probe coefficients, the normalized cap
moments `K_l` are the coefficients of `ĉ(z) · T(z)`:

  `H < 0`: `K_l = u ≫ y^(N-P-1+l) ≫ b`,
  `H = 0`: `K_0 = 1`, `K_l = u ≫ y^(l-1) ≫ j ≫ v` (`l ≥ 1`).

The terms whose reservoir exponent lies below `N - 1` are removed by the
coefficient-extraction window; no exponent of `y` is negative. No bubble
formula is assumed. See `docs/Nondegeneracy/InverseCapSeries.md`.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedVacuum

open CategoryTheory Finset SwappedAssembly

universe u v w

variable {k : Type w} [CommRing k]

/-- Reindexing the probe-polynomial moment by the reversed coefficients.
Terms whose index lies below the window bound `B` vanish. -/
theorem probe_cap_convolution {R : Type*} [AddCommGroup R] [Module k R] (c : ℕ → k)
    (P B m l : ℕ) (hml : m + P = B + l) (t : ℕ → R) (ht : ∀ j < B, t j = 0) :
    ∑ n ∈ range (P + 1), c n • t (n + m) = ∑ r ∈ range (l + 1),
      if r ≤ P then c (P - r) • t (B + l - r) else 0 := by
  apply sum_bij_ne_zero (fun n _ _ => P - n)
  · intro n hn hne
    rw [mem_range] at hn ⊢
    have : B ≤ n + m := by
      by_contra h
      exact hne (by rw [ht _ (by omega), smul_zero])
    omega
  · intro n₁ hn₁ _ n₂ hn₂ _ heq
    rw [mem_range] at hn₁ hn₂
    omega
  · intro r hr hne
    rw [mem_range] at hr
    by_cases h : r ≤ P
    · refine ⟨P - r, mem_range.mpr (by omega), ?_, by omega⟩
      rw [ite_eq_left h] at hne
      rwa [show P - r + m = B + l - r by omega]
    · exact absurd (ite_eq_right h) hne
  · intro n hn _
    rw [mem_range] at hn
    rw [ite_eq_left (show P - n ≤ P by omega), show P - (P - n) = n by omega,
      show B + l - (P - n) = n + m by omega]

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] {V X Y : C}

/-- The linear scalar action on `V ⟶ V` is left multiplication by `algebraMap` in `End V`. -/
theorem linear_smul_eq_algebraMap_mul (a : k) (f : V ⟶ V) :
    a • f = algebraMap k (End V) a * (show End V from f) := by
  have hr : algebraMap k (End V) a = a • 𝟙 V := Algebra.algebraMap_eq_smul_one a
  erw [hr, End.mul_def, Linear.comp_smul, Category.comp_id]

/-- **Negative-height cap moments**, equation (11): the moments of the
prescribed extreme inverse cap are the reversed-probe convolution of the
reservoir moments. -/
theorem negative_inverse_cap_moment (q : k) (x : End X) (y : End Y)
    (s : X ⟶ Y) (u : V ⟶ Y) (v : X ⟶ V) (ell : Y ⟶ V)
    (N P : ℕ) (hPN : P < N) (c : ℕ → k) (hmonic : c P = 1)
    (hsupport : ∀ n ≤ P, c n * q ^ n = c n)
    (hslide : s ≫ y - q • (x ≫ s) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V else 0)
    (hprobe : capPolynomial c P x = 0)
    (j : Y ⟶ X) (B : Fin (N - P) → (Y ⟶ V))
    (H : ProbeWindow.IsCupInverse s (fun n => u ≫ (y ^ n.val)) j B) (l : ℕ) :
    u ≫ (y ^ (N - P - 1 + l)) ≫ B ⟨N - P - 1, by omega⟩ = ∑ r ∈ range (l + 1),
      if r ≤ P then c (P - r) • (u ≫ (y ^ (N - 1 + l - r)) ≫ ell) else 0 := by
  rw [negative_inverse_cap_eq_polynomial q x y s u v ell N P hPN c hmonic hsupport hslide
    hwindow hprobe j B H, coefficient_polynomial_moment]
  exact probe_cap_convolution c P (N - 1) (N - P - 1 + l) l (by omega)
    (fun i => u ≫ (y ^ i) ≫ ell)
    (fun i hi => by rw [hwindow i (by omega), ite_eq_right (by omega)])

/-- The negative-height moments as a power series: `K(z) = ĉ(z) T(z)`. -/
theorem negative_inverse_cap_series (q : k) (x : End X) (y : End Y)
    (s : X ⟶ Y) (u : V ⟶ Y) (v : X ⟶ V) (ell : Y ⟶ V)
    (N P : ℕ) (hPN : P < N) (c : ℕ → k) (hmonic : c P = 1)
    (hsupport : ∀ n ≤ P, c n * q ^ n = c n)
    (hslide : s ≫ y - q • (x ≫ s) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V else 0)
    (hprobe : capPolynomial c P x = 0)
    (j : Y ⟶ X) (B : Fin (N - P) → (Y ⟶ V))
    (H : ProbeWindow.IsCupInverse s (fun n => u ≫ (y ^ n.val)) j B) :
    PowerSeries.mk (R := End V)
        (fun l => u ≫ (y ^ (N - P - 1 + l)) ≫ B ⟨N - P - 1, by omega⟩) =
      PowerSeries.mk (fun r => if r ≤ P then algebraMap k (End V) (c (P - r)) else 0) *
        PowerSeries.mk (R := End V) (fun l => u ≫ (y ^ (N - 1 + l)) ≫ ell) := by
  ext l
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    negative_inverse_cap_moment q x y s u v ell N P hPN c hmonic hsupport hslide hwindow
      hprobe j B H l]
  refine sum_congr rfl fun r hr => ?_
  rw [mem_range] at hr
  simp only [PowerSeries.coeff_mk]
  split_ifs with h
  · rw [linear_smul_eq_algebraMap_mul, show N - 1 + l - r = N - 1 + (l - r) by omega]
  · exact (zero_mul _).symm

/-- The normalized zero-height moments: the fake value `K_0 = 1` and
`K_l = u ≫ y^(l-1) ≫ j ≫ v` for `l ≥ 1`. -/
def zeroHeightMoment (y : End Y) (s : X ≅ Y) (u : V ⟶ Y) (v : X ⟶ V) (l : ℕ) : End V :=
  if l = 0 then 𝟙 V else u ≫ (y ^ (l - 1)) ≫ s.inv ≫ v

/-- **Zero-height cap moments**, equation (13): the same convolution, with
the principal inverse in place of the extreme cap. -/
theorem zero_height_moment (q : k) (x : End X) (y : End Y)
    (s : X ≅ Y) (u : V ⟶ Y) (v : X ⟶ V) (ell : Y ⟶ V)
    (N : ℕ) (hN : 0 < N) (c : ℕ → k) (hmonic : c N = 1)
    (hsupport : ∀ n ≤ N, c n • q ^ n = c n)
    (hslide : s.hom ≫ y - q • (x ≫ s.hom) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V else 0)
    (hprobe : capPolynomial c N x = 0) (l : ℕ) :
    zeroHeightMoment y s u v l = ∑ r ∈ range (l + 1),
      if r ≤ N then c (N - r) • (u ≫ (y ^ (N - 1 + l - r)) ≫ ell) else 0 := by
  rcases l with _ | l
  · rw [zeroHeightMoment, ite_eq_left rfl, zero_add, sum_range_one,
      ite_eq_left (Nat.zero_le _)]
    simp only [Nat.sub_zero, Nat.add_zero]
    rw [hmonic, one_smul, hwindow (N - 1) (by omega), ite_eq_left (by omega)]
  · rw [zeroHeightMoment, ite_eq_right (Nat.succ_ne_zero l), Nat.add_sub_cancel,
      principal_inverse_right_moment q x y s u v ell N hN c hmonic hsupport hslide hwindow
        hprobe l]
    exact probe_cap_convolution c N (N - 1) l (l + 1) (by omega)
      (fun i => u ≫ (y ^ i) ≫ ell)
      (fun i hi => by rw [hwindow i (by omega), ite_eq_right (by omega)])

/-- The zero-height moments as a power series: `K(z) = ĉ(z) T(z)`. -/
theorem zero_height_series (q : k) (x : End X) (y : End Y)
    (s : X ≅ Y) (u : V ⟶ Y) (v : X ⟶ V) (ell : Y ⟶ V)
    (N : ℕ) (hN : 0 < N) (c : ℕ → k) (hmonic : c N = 1)
    (hsupport : ∀ n ≤ N, c n • q ^ n = c n)
    (hslide : s.hom ≫ y - q • (x ≫ s.hom) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V else 0)
    (hprobe : capPolynomial c N x = 0) :
    PowerSeries.mk (zeroHeightMoment y s u v) =
      PowerSeries.mk (fun r => if r ≤ N then algebraMap k (End V) (c (N - r)) else 0) *
        PowerSeries.mk (R := End V) (fun l => u ≫ (y ^ (N - 1 + l)) ≫ ell) := by
  ext l
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    zero_height_moment q x y s u v ell N hN c hmonic hsupport hslide hwindow hprobe l]
  refine sum_congr rfl fun r hr => ?_
  rw [mem_range] at hr
  simp only [PowerSeries.coeff_mk]
  split_ifs with h
  · rw [linear_smul_eq_algebraMap_mul, show N - 1 + l - r = N - 1 + (l - r) by omega]
  · exact (zero_mul _).symm

end OddMath.QuiverHecke.SwappedVacuum
