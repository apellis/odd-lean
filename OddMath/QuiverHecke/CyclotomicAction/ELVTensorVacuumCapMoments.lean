/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumColumnMoments
import OddMath.QuiverHecke.SwappedVacuum.InverseCapColourSeries
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerEvenColourSeries
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvenCentralSlide
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvenVacuumPolynomial

/-! # Inverse-cap moments at nonpositive height on the tensor vacuum

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8 (the left-bubble series of `AdjunctionBubbleSeries.left_odd` at colours
with `hᵢ(μ) ≤ 0`).

On the prescribed tensor vacuum at an odd colour, let `x` be the shifted pre
dot, `y` the evaluated post dot, `s` the actual A6 bend, `u` the adjunction
unit, `v` the shifted pre cap and `ℓ` the prescribed reservoir cap. With
probe exponent `M` and reservoir cutoff `N`:

* at negative height `2M < N`, for any entrywise inverse `[j; B]` of the cup
  window `[s, u, u ≫ y, …, u ≫ y^(N-2M-1)]`, the moments of the extreme
  inverse cap `B_(N-2M-1)` act on the coefficient chart as the coefficients
  of `(1 + w)^M / C(-w)` and those coefficients times the normalized odd
  coefficient `(-1)^(N+1) δ` (`tensorVacuumNegativeCap_odd_moments`);
* at zero height `2M = N`, for the bend as an isomorphism, the moments
  `u ≫ y^(2r) ≫ s⁻¹ ≫ v` and `u ≫ y^(2r+1) ≫ s⁻¹ ≫ v` are `δ` times the
  `r`th and the `(r+1)`st coefficient (`tensorVacuumZeroHeightCap_odd_moments`).

These instantiate `SwappedVacuum.odd_cap_moments` with the actual slide,
window, probe polynomial and the reservoir moments
`tensorPowerVacuumCap_moment_even/odd`, transported to linear operators on
the coefficient quotient by `tensorVacuumEndDecode`. No bubble value or
inverse row is assumed beyond the stated inverse. See
`docs/Nondegeneracy/InverseCapSeries.md`.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient ProbeVacuumCap
open Finset
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "W₀" => Functor.obj (restriction (contentInclusion D Sc cutoff bound (0 : Multiset I)))
  (weightedVacuum D Sc cutoff L)
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound W₀
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m
local notation "V" => Superfunctor.obj H N₀
local notation "star" => (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff bound 0)
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L

variable (i : I)

local notation "K" => contentAppend D Sc cutoff bound (0 : Multiset I) [i]

/-- Left multiplication by the polynomial coefficients on the coefficient quotient. -/
private def capCoefficientLmul : MvPolynomial (I × ℕ) k →ₐ[k] Module.End k AQ :=
  (Algebra.lmul k AQ).comp (polynomialToPower D cutoff L)

private theorem unit_cap_moment (hN : 0 < cutoff i) (n : ℕ) :
    (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN = tensorUnitCapClosure D Sc m cutoff L i hN n := by
  rw [tensorUnitCapClosure, unitDotColumn_eq_restrictedDotEnd, Category.assoc]
  rfl

private theorem odd_probe_polynomial (hi : D.parity i = 1) :
    SwappedVacuum.capPolynomial
      (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff n) (2 * m i)
      (shiftedPreDot D Sc m R₀ i H) = 0 := by
  have hb : (Polynomial.X ^ 2 + 1 : Polynomial k).natDegree ≤ 2 :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le (Polynomial.natDegree_X_pow_le 2) (by simp))
  have hd : ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).natDegree ≤ 2 * m i := by
    calc
      _ ≤ m i * (Polynomial.X ^ 2 + 1 : Polynomial k).natDegree := Polynomial.natDegree_pow_le
      _ ≤ m i * 2 := Nat.mul_le_mul_left (m i) hb
      _ = 2 * m i := Nat.mul_comm _ _
  rw [SwappedVacuum.capPolynomial,
    ← Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hd) (shiftedPreDot D Sc m R₀ i H)]
  simp only [map_pow, map_add, Polynomial.aeval_X, map_one]
  exact shiftedPreDot_odd_polynomial D Sc m R₀ i hi H

/-- The reservoir series of the tensor vacuum at an odd colour, in the decode
chart: `T(z) = A(z²)(1 + e z)` with `A = 1/C(-w)` and `e = (-1)^(N+1) δ`. -/
private theorem odd_reservoir_series (hi : D.parity i = 1) (hN : 0 < cutoff i) :
    PowerSeries.mk (fun l => tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + l)) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN)) =
      PowerSeries.map (capCoefficientLmul D cutoff L).toRingHom (PowerSeries.expand 2 two_ne_zero
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) *
        (1 + PowerSeries.C (Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩))) * PowerSeries.X) := by
  have hcomm (p : MvPolynomial (I × ℕ) k) : Commute (polynomialToPower D cutoff L p)
      ((-1 : k) ^ (cutoff i + 1) •
        coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) :=
    (((SKM.SYM.polynomialInclude_commute D k p (SKM.SYM.delta D k ⟨i, hi⟩)).map
      (coefficientPowerQuotientMap D cutoff L)).smul_right _)
  refine SwappedVacuum.mk_eq_expand_mul_one_add (capCoefficientLmul D cutoff L).toRingHom _ _ _
    (fun r => ?_) (fun r => ?_)
  · ext1 w
    obtain ⟨z, rfl⟩ := (tensorVacuumDecodeEquiv D Sc m cutoff L).surjective w
    change tensorVacuumEndDecode D Sc m cutoff L _ (tensorVacuumDecodeLinear D Sc m cutoff L z) = _
    rw [unit_cap_moment D Sc m cutoff L i hN, tensorVacuumEndDecode_apply,
      tensorPowerVacuumCap_moment_even D Sc m cutoff L i hi hN r z]
    rfl
  · ext1 w
    obtain ⟨z, rfl⟩ := (tensorVacuumDecodeEquiv D Sc m cutoff L).surjective w
    change tensorVacuumEndDecode D Sc m cutoff L _ (tensorVacuumDecodeLinear D Sc m cutoff L z) = _
    rw [unit_cap_moment D Sc m cutoff L i hN, tensorVacuumEndDecode_apply,
      tensorPowerVacuumCap_moment_odd D Sc m cutoff L i hi hN r z]
    change _ = polynomialToPower D cutoff L _ * (((-1 : k) ^ (cutoff i + 1) •
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z)
    rw [← mul_assoc, (hcomm _).eq]
    simp only [smul_mul_assoc]
    rfl

private theorem delta_commute (hi : D.parity i = 1) (p : MvPolynomial (I × ℕ) k) :
    Commute (polynomialToPower D cutoff L p) ((-1 : k) ^ (cutoff i + 1) •
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) :=
  (((SKM.SYM.polynomialInclude_commute D k p (SKM.SYM.delta D k ⟨i, hi⟩)).map
    (coefficientPowerQuotientMap D cutoff L)).smul_right _)

/-- Transport of a reversed-probe convolution along the decode chart. -/
private theorem decode_convolution (c : ℕ → k) (P B : ℕ) (Kf : ℕ → End V) (t : ℕ → End V)
    (hK : ∀ l, Kf l = ∑ r ∈ range (l + 1), if r ≤ P then c (P - r) • t (B + l - r) else 0) :
    PowerSeries.mk (fun l => tensorVacuumEndDecode D Sc m cutoff L (Kf l)) =
      PowerSeries.mk (fun r => if r ≤ P then algebraMap k (Module.End k AQ) (c (P - r)) else 0) *
        PowerSeries.mk (fun l => tensorVacuumEndDecode D Sc m cutoff L (t (B + l))) := by
  ext l
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    hK l, map_sum]
  refine sum_congr rfl fun r hr => ?_
  rw [mem_range] at hr
  simp only [PowerSeries.coeff_mk]
  split_ifs with h
  · rw [SwappedVacuum.linear_smul_eq_algebraMap_mul, map_mul, AlgHom.commutes,
      show B + l - r = B + (l - r) by omega]
  · rw [map_zero, zero_mul]

include sy hc in
/-- **Odd colour, negative height, on the tensor vacuum.** For probe exponent
`M = m i` and reservoir cutoff `N = cutoff i` with `2M < N`, and any entrywise
inverse `[j; B]` of the cup window of the actual A6 bend with the unit/post-dot
rows, the decoded moments of the extreme inverse cap are the coefficients of
`(1 + w)^M / C(-w)`, and the odd moments carry the normalized odd coefficient
`(-1)^(N+1) δ`. -/
theorem tensorVacuumNegativeCap_odd_moments
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        (((adjunction K).unit.app V ≫
          (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 2 * m i - 1 + 2 * r)) ≫
            B ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z ∧
    tensorVacuumDecodeLinear D Sc m cutoff L
        (((adjunction K).unit.app V ≫
          (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 2 * m i - 1 + (2 * r + 1))) ≫
            B ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        (polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
          tensorVacuumDecodeLinear D Sc m cutoff L z) := by
  set ρ := tensorVacuumEndDecode D Sc m cutoff L
  set δq : AQ := (-1 : k) ^ (cutoff i + 1) •
    coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)
  have hs := evaluatedMixedBend_odd_slide D Sc m cutoff bound sy hc i hi hP H
  have hs' : evaluatedMixedBend D Sc m cutoff bound i hP H ≫
        evaluatedPostDot D Sc m cutoff bound i H -
      (-1 : k) • (shiftedPreDot D Sc m R₀ i H ≫
        evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V := by
    simpa only [hi, koszulSign_one_one, neg_one_zsmul, neg_one_smul] using hs
  have hwin : ∀ a < cutoff i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ a) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = cutoff i then 𝟙 V else 0 :=
    fun a ha => tensorPowerVacuumCap_window D Sc m cutoff L i hN a ha
  have hK := decode_convolution D Sc m cutoff L
    (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff n) (2 * m i) (cutoff i - 1)
    (fun l => (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 2 * m i - 1 + l)) ≫
        B ⟨cutoff i - 2 * m i - 1, by omega⟩)
    (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN)
    (SwappedVacuum.negative_inverse_cap_moment (-1) (shiftedPreDot D Sc m R₀ i H)
      (evaluatedPostDot D Sc m cutoff bound i H) (evaluatedMixedBend D Sc m cutoff bound i hP H)
      ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H)
      (tensorPowerVacuumCap D Sc m cutoff L i hN) (cutoff i) (2 * m i) hPN
      (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff n)
      (SwappedVacuum.square_add_one_coeff_top (m i))
      (fun n _ => SwappedVacuum.square_add_one_coeff_mul_neg_one_pow (m i) n)
      hs' hwin (odd_probe_polynomial D Sc m cutoff L i hi) j B hB)
  obtain ⟨h1, h2⟩ := SwappedVacuum.odd_cap_moments D (capCoefficientLmul D cutoff L) m i hi
    (cutoff i - 1) (Algebra.lmul k AQ δq) _ _ hK
    (odd_reservoir_series D Sc m cutoff L i hi hN) r
  constructor
  · have h3 := congrArg (fun f : Module.End k AQ => f (tensorVacuumDecodeLinear D Sc m cutoff L z)) h1
    simp only [ρ, tensorVacuumEndDecode_apply] at h3
    exact h3
  · have h3 := congrArg (fun f : Module.End k AQ => f (tensorVacuumDecodeLinear D Sc m cutoff L z)) h2
    simp only [ρ, tensorVacuumEndDecode_apply] at h3
    rw [h3]
    change polynomialToPower D cutoff L _ * (δq * _) = δq * (polynomialToPower D cutoff L _ * _)
    rw [← mul_assoc, ← mul_assoc, (delta_commute D cutoff L i hi _).eq]

include sy hc in
/-- **Odd colour, zero height, on the tensor vacuum.** For `cutoff i = 2 M`,
`M = m i`, and the A6 bend an isomorphism `s`, the decoded moments of the
principal inverse are `u ≫ y^(2r) ≫ s⁻¹ ≫ v = δ · A_r` and
`u ≫ y^(2r+1) ≫ s⁻¹ ≫ v = A_(r+1)`, where `A_r` is the `r`th coefficient of
`(1 + w)^M / C(-w)` and `δ` the normalized odd coefficient `(-1)^(N+1) δ`. -/
theorem tensorVacuumZeroHeightCap_odd_moments
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (hcut : cutoff i = 2 * m i)
    (s : shiftedPreSourceObject D Sc m R₀ i H ≅ _)
    (hsb : s.hom = evaluatedMixedBend D Sc m cutoff bound i hP H)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        (((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (2 * r)) ≫
          s.inv ≫ shiftedPreCap D Sc m R₀ i hP H).total star z) =
      ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        (polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
          tensorVacuumDecodeLinear D Sc m cutoff L z) ∧
    tensorVacuumDecodeLinear D Sc m cutoff L
        (((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (2 * r + 1)) ≫
          s.inv ≫ shiftedPreCap D Sc m R₀ i hP H).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff (r + 1)
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  set δq : AQ := (-1 : k) ^ (cutoff i + 1) •
    coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)
  have hs := evaluatedMixedBend_odd_slide D Sc m cutoff bound sy hc i hi hP H
  have hs' : s.hom ≫ evaluatedPostDot D Sc m cutoff bound i H -
      (-1 : k) • (shiftedPreDot D Sc m R₀ i H ≫ s.hom) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V := by
    rw [hsb]
    simpa only [hi, koszulSign_one_one, neg_one_zsmul, neg_one_smul] using hs
  have hwin : ∀ a < 2 * m i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ a) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = 2 * m i then 𝟙 V else 0 := by
    intro a ha
    rw [← hcut]
    exact tensorPowerVacuumCap_window D Sc m cutoff L i hN a (by omega)
  have hK := decode_convolution D Sc m cutoff L
    (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff n) (2 * m i) (cutoff i - 1)
    (SwappedVacuum.zeroHeightMoment (evaluatedPostDot D Sc m cutoff bound i H) s
      ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H))
    (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN)
    (fun l => by
      rw [SwappedVacuum.zero_height_moment (-1) (shiftedPreDot D Sc m R₀ i H)
        (evaluatedPostDot D Sc m cutoff bound i H) s ((adjunction K).unit.app V)
        (shiftedPreCap D Sc m R₀ i hP H) (tensorPowerVacuumCap D Sc m cutoff L i hN) (2 * m i)
        (by omega) (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff n)
        (SwappedVacuum.square_add_one_coeff_top (m i))
        (fun n _ => by
          rw [smul_eq_mul]
          exact SwappedVacuum.square_add_one_coeff_mul_neg_one_pow (m i) n)
        hs' hwin (odd_probe_polynomial D Sc m cutoff L i hi) l,
        show 2 * m i - 1 = cutoff i - 1 by omega])
  have hA := fun r => SwappedVacuum.odd_cap_moments D (capCoefficientLmul D cutoff L) m i hi
    (cutoff i - 1) (Algebra.lmul k AQ δq) _ _ hK (odd_reservoir_series D Sc m cutoff L i hi hN) r
  have h₀ := congrArg (fun f : Module.End k AQ => f (tensorVacuumDecodeLinear D Sc m cutoff L z))
    (hA r).2
  have h₁ := congrArg (fun f : Module.End k AQ => f (tensorVacuumDecodeLinear D Sc m cutoff L z))
    (hA (r + 1)).1
  simp only [SwappedVacuum.zeroHeightMoment, ite_eq_right (show 2 * r + 1 ≠ 0 by omega),
    ite_eq_right (show 2 * (r + 1) ≠ 0 by omega), show 2 * r + 1 - 1 = 2 * r by omega,
    show 2 * (r + 1) - 1 = 2 * r + 1 by omega, tensorVacuumEndDecode_apply] at h₀ h₁
  refine ⟨?_, h₁⟩
  rw [h₀]
  change polynomialToPower D cutoff L _ * (δq * _) = δq * (polynomialToPower D cutoff L _ * _)
  rw [← mul_assoc, ← mul_assoc, (delta_commute D cutoff L i hi _).eq]

/-! ### Even colour -/

private theorem even_probe_polynomial (hi : D.parity i = 0) :
    SwappedVacuum.capPolynomial
      (fun n => ((Polynomial.X - 1 : Polynomial k) ^ m i).coeff n) (m i)
      (shiftedPreDot D Sc m R₀ i H) = 0 := by
  have hb : (Polynomial.X - 1 : Polynomial k).natDegree ≤ 1 :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le Polynomial.natDegree_X_le (by simp))
  have hd : ((Polynomial.X - 1 : Polynomial k) ^ m i).natDegree ≤ m i := by
    calc
      _ ≤ m i * (Polynomial.X - 1 : Polynomial k).natDegree := Polynomial.natDegree_pow_le
      _ ≤ m i * 1 := Nat.mul_le_mul_left (m i) hb
      _ = m i := Nat.mul_one _
  rw [SwappedVacuum.capPolynomial,
    ← Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hd) (shiftedPreDot D Sc m R₀ i H)]
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one]
  exact shiftedPreDot_even_polynomial D Sc m R₀ i hi H

/-- The reservoir series of the tensor vacuum at an even colour, in the decode
chart: `T(z) = 1/E(-z)`, the complete coefficients. -/
private theorem even_reservoir_series (hi : D.parity i = 0) (hN : 0 < cutoff i) :
    PowerSeries.mk (fun l => tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + l)) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN)) =
      PowerSeries.map (capCoefficientLmul D cutoff L).toRingHom
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1) := by
  refine PowerSeries.ext fun l => ?_
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_map]
  ext1 w
  obtain ⟨z, rfl⟩ := (tensorVacuumDecodeEquiv D Sc m cutoff L).surjective w
  change tensorVacuumEndDecode D Sc m cutoff L _ (tensorVacuumDecodeLinear D Sc m cutoff L z) = _
  rw [unit_cap_moment D Sc m cutoff L i hN, tensorVacuumEndDecode_apply,
    tensorPowerVacuumCap_moment_apply, even_colour_signedMoment D Sc cutoff L i hi hN l]
  rfl

include sy hc in
/-- **Even colour, negative height, on the tensor vacuum.** For probe exponent
`M = m i` and reservoir cutoff `N = cutoff i` with `M < N`, and any entrywise
inverse `[j; B]` of the cup window of the actual bend with the unit/post-dot
rows, the decoded moments of the extreme inverse cap are the coefficients of
`(1 - w)^M / E(-w)`. -/
theorem tensorVacuumNegativeCap_even_moments
    (hi : D.parity i = 0) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (hPN : m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - m i) → (_ ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (l : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        (((adjunction K).unit.app V ≫
          (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - m i - 1 + l)) ≫
            B ⟨cutoff i - m i - 1, by omega⟩).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff l
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  have hs := evaluatedMixedBend_even_slide D Sc m cutoff bound sy hc i hi hP H
  have hs' : evaluatedMixedBend D Sc m cutoff bound i hP H ≫
        evaluatedPostDot D Sc m cutoff bound i H -
      (1 : k) • (shiftedPreDot D Sc m R₀ i H ≫
        evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V := by
    rw [one_smul]
    simpa only [hi, koszulSign_zero_left, one_smul] using hs
  have hwin : ∀ a < cutoff i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ a) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = cutoff i then 𝟙 V else 0 :=
    fun a ha => tensorPowerVacuumCap_window D Sc m cutoff L i hN a ha
  have hK := decode_convolution D Sc m cutoff L
    (fun n => ((Polynomial.X - 1 : Polynomial k) ^ m i).coeff n) (m i) (cutoff i - 1)
    (fun l => (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - m i - 1 + l)) ≫
        B ⟨cutoff i - m i - 1, by omega⟩)
    (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN)
    (SwappedVacuum.negative_inverse_cap_moment 1 (shiftedPreDot D Sc m R₀ i H)
      (evaluatedPostDot D Sc m cutoff bound i H) (evaluatedMixedBend D Sc m cutoff bound i hP H)
      ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H)
      (tensorPowerVacuumCap D Sc m cutoff L i hN) (cutoff i) (m i) hPN
      (fun n => ((Polynomial.X - 1 : Polynomial k) ^ m i).coeff n)
      (SwappedVacuum.sub_one_pow_coeff_top (m i))
      (fun n _ => by rw [one_pow, mul_one])
      hs' hwin (even_probe_polynomial D Sc m cutoff L i hi) j B hB)
  have h1 := SwappedVacuum.even_cap_moments D (capCoefficientLmul D cutoff L) m i hi
    (cutoff i - 1) _ _ hK (even_reservoir_series D Sc m cutoff L i hi hN) l
  have h3 := congrArg (fun f : Module.End k AQ => f (tensorVacuumDecodeLinear D Sc m cutoff L z)) h1
  simp only [tensorVacuumEndDecode_apply] at h3
  exact h3

include sy hc in
/-- **Even colour, zero height, on the tensor vacuum.** For `cutoff i = M`,
`M = m i`, and the bend an isomorphism `s`, the decoded moments of the
principal inverse are `u ≫ y^l ≫ s⁻¹ ≫ v = A_(l+1)`, where `A_r` is the `r`th
coefficient of `(1 - w)^M / E(-w)`. -/
theorem tensorVacuumZeroHeightCap_even_moments
    (hi : D.parity i = 0) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (hcut : cutoff i = m i)
    (s : shiftedPreSourceObject D Sc m R₀ i H ≅ _)
    (hsb : s.hom = evaluatedMixedBend D Sc m cutoff bound i hP H)
    (l : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        (((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ l) ≫
          s.inv ≫ shiftedPreCap D Sc m R₀ i hP H).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff (l + 1)
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  have hs := evaluatedMixedBend_even_slide D Sc m cutoff bound sy hc i hi hP H
  have hs' : s.hom ≫ evaluatedPostDot D Sc m cutoff bound i H -
      (1 : k) • (shiftedPreDot D Sc m R₀ i H ≫ s.hom) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V := by
    rw [hsb, one_smul]
    simpa only [hi, koszulSign_zero_left, one_smul] using hs
  have hwin : ∀ a < m i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ a) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = m i then 𝟙 V else 0 := by
    intro a ha
    rw [← hcut]
    exact tensorPowerVacuumCap_window D Sc m cutoff L i hN a (by omega)
  have hK := decode_convolution D Sc m cutoff L
    (fun n => ((Polynomial.X - 1 : Polynomial k) ^ m i).coeff n) (m i) (cutoff i - 1)
    (SwappedVacuum.zeroHeightMoment (evaluatedPostDot D Sc m cutoff bound i H) s
      ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H))
    (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN)
    (fun l => by
      rw [SwappedVacuum.zero_height_moment 1 (shiftedPreDot D Sc m R₀ i H)
        (evaluatedPostDot D Sc m cutoff bound i H) s ((adjunction K).unit.app V)
        (shiftedPreCap D Sc m R₀ i hP H) (tensorPowerVacuumCap D Sc m cutoff L i hN) (m i)
        (by omega) (fun n => ((Polynomial.X - 1 : Polynomial k) ^ m i).coeff n)
        (SwappedVacuum.sub_one_pow_coeff_top (m i))
        (fun n _ => by rw [one_pow, smul_eq_mul, mul_one])
        hs' hwin (even_probe_polynomial D Sc m cutoff L i hi) l,
        show m i - 1 = cutoff i - 1 by omega])
  have h1 := SwappedVacuum.even_cap_moments D (capCoefficientLmul D cutoff L) m i hi
    (cutoff i - 1) _ _ hK (even_reservoir_series D Sc m cutoff L i hi hN) (l + 1)
  have h3 := congrArg (fun f : Module.End k AQ => f (tensorVacuumDecodeLinear D Sc m cutoff L z)) h1
  simp only [SwappedVacuum.zeroHeightMoment, ite_eq_right (show l + 1 ≠ 0 by omega),
    Nat.add_sub_cancel, tensorVacuumEndDecode_apply] at h3
  exact h3

end OddMath.QuiverHecke.ELVOld
