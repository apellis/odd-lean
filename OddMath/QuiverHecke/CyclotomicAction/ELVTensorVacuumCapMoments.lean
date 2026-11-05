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
  coefficient `(-1)^(N+1) δ` (`tensorVacuumNegativeCap_odd_moments_even`,
  `tensorVacuumNegativeCap_odd_moments_odd`);
* at zero height `2M = N`, for the bend as an isomorphism, the moments
  `u ≫ y^(2r) ≫ s⁻¹ ≫ v` and `u ≫ y^(2r+1) ≫ s⁻¹ ≫ v` are `δ` times the
  `r`th and the `(r+1)`st coefficient (`tensorVacuumZeroHeightCap_odd_moments_even`,
  `tensorVacuumZeroHeightCap_odd_moments_odd`).

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

section Generic

variable {k' : Type u} [CommRing k'] {C : Type*} [Category C]
  [Preadditive C] [Linear k' C] {Xo Yo V' : C}

/-- Transport of a reversed-probe convolution of endomorphisms along an algebra map. -/
private theorem map_probe_convolution {R : Type*} [Ring R] [Algebra k' R]
    (ρ : End V' →ₐ[k'] R) (c : ℕ → k') (P B : ℕ) (Kf t : ℕ → End V')
    (hK : ∀ l, Kf l = ∑ r ∈ range (l + 1), if r ≤ P then c (P - r) • t (B + l - r) else 0) :
    PowerSeries.mk (fun l => ρ (Kf l)) =
      PowerSeries.mk (fun r => if r ≤ P then algebraMap k' R (c (P - r)) else 0) *
        PowerSeries.mk (fun l => ρ (t (B + l))) := by
  ext l
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    hK l, map_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [mem_range] at hr
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases h : r ≤ P
  · rw [ite_eq_left h, ite_eq_left h, map_smul, Algebra.smul_def,
      show B + l - r = B + (l - r) by omega]
  · rw [ite_eq_right h, ite_eq_right h, map_zero, zero_mul]

variable {I' X' : Type u} [AddCommGroup X']

/-- Odd colour, negative height, read through an algebra map `ρ`. -/
private theorem odd_negative_cap_moments_of_slide (D : SKM.Datum I' X') {R : Type*} [Ring R]
    [Algebra k' R] (φ : MvPolynomial (I' × ℕ) k' →ₐ[k'] R) (ρ : End V' →ₐ[k'] R)
    (P : I' → ℕ) (i : I') (hi : D.parity i = 1)
    (x : End Xo) (y : End Yo) (s : Xo ⟶ Yo) (u : V' ⟶ Yo) (v : Xo ⟶ V') (ell : Yo ⟶ V')
    (N : ℕ) (hPN : 2 * P i < N) (e : R) (hcomm : ∀ p, Commute (φ p) e)
    (hslide : s ≫ y - (-1 : k') • (x ≫ s) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V' else 0)
    (hprobe : SwappedVacuum.capPolynomial
      (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k') ^ P i).coeff n) (2 * P i) x = 0)
    (j : Yo ⟶ Xo) (B : Fin (N - 2 * P i) → (Yo ⟶ V'))
    (H : SwappedAssembly.ProbeWindow.IsCupInverse s (fun n => u ≫ (y ^ n.val)) j B)
    (hT : PowerSeries.mk (fun l => ρ (u ≫ (y ^ (N - 1 + l)) ≫ ell)) =
      PowerSeries.map φ.toRingHom (PowerSeries.expand 2 two_ne_zero
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k' i)) 1)) *
          (1 + PowerSeries.C e * PowerSeries.X))
    (r : ℕ) :
    ρ (u ≫ (y ^ (N - 2 * P i - 1 + 2 * r)) ≫ B ⟨N - 2 * P i - 1, by omega⟩) =
        φ (PowerSeries.coeff r
          (VacuumSeries.momentSeries k' (SKM.SYM.probeSeriesInv D k' P) i)) ∧
      ρ (u ≫ (y ^ (N - 2 * P i - 1 + (2 * r + 1))) ≫ B ⟨N - 2 * P i - 1, by omega⟩) =
        e * φ (PowerSeries.coeff r
          (VacuumSeries.momentSeries k' (SKM.SYM.probeSeriesInv D k' P) i)) := by
  have h := SwappedVacuum.odd_cap_moments D φ P i hi (N - 1) e
    (fun l => ρ (u ≫ (y ^ (N - 2 * P i - 1 + l)) ≫ B ⟨N - 2 * P i - 1, by omega⟩))
    (fun n => ρ (u ≫ (y ^ n) ≫ ell))
    (map_probe_convolution ρ (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k') ^ P i).coeff n)
      (2 * P i) (N - 1)
      (fun l => u ≫ (y ^ (N - 2 * P i - 1 + l)) ≫ B ⟨N - 2 * P i - 1, by omega⟩)
      (fun n => u ≫ (y ^ n) ≫ ell)
      (SwappedVacuum.negative_inverse_cap_moment (-1) x y s u v ell N (2 * P i) hPN
        (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k') ^ P i).coeff n)
        (SwappedVacuum.square_add_one_coeff_top (P i))
        (fun n _ => SwappedVacuum.square_add_one_coeff_mul_neg_one_pow (P i) n)
        hslide hwindow hprobe j B H)) hT r
  exact ⟨h.1, h.2.trans (hcomm _).eq⟩

/-- Odd colour, zero height, read through an algebra map `ρ`. -/
private theorem odd_zero_cap_moments_of_slide (D : SKM.Datum I' X') {R : Type*} [Ring R]
    [Algebra k' R] (φ : MvPolynomial (I' × ℕ) k' →ₐ[k'] R) (ρ : End V' →ₐ[k'] R)
    (P : I' → ℕ) (i : I') (hi : D.parity i = 1) (hP : 0 < P i)
    (x : End Xo) (y : End Yo) (s : Xo ≅ Yo) (u : V' ⟶ Yo) (v : Xo ⟶ V') (ell : Yo ⟶ V')
    (e : R) (N : ℕ) (hNP : N = 2 * P i)
    (hslide : s.hom ≫ y - (-1 : k') • (x ≫ s.hom) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V' else 0)
    (hprobe : SwappedVacuum.capPolynomial
      (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k') ^ P i).coeff n) (2 * P i) x = 0)
    (hT : PowerSeries.mk (fun l => ρ (u ≫ (y ^ (N - 1 + l)) ≫ ell)) =
      PowerSeries.map φ.toRingHom (PowerSeries.expand 2 two_ne_zero
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k' i)) 1)) *
          (1 + PowerSeries.C e * PowerSeries.X))
    (r : ℕ) :
    ρ (u ≫ (y ^ (2 * r)) ≫ s.inv ≫ v) =
        φ (PowerSeries.coeff r
          (VacuumSeries.momentSeries k' (SKM.SYM.probeSeriesInv D k' P) i)) * e ∧
      ρ (u ≫ (y ^ (2 * r + 1)) ≫ s.inv ≫ v) =
        φ (PowerSeries.coeff (r + 1)
          (VacuumSeries.momentSeries k' (SKM.SYM.probeSeriesInv D k' P) i)) := by
  subst hNP
  have hK := map_probe_convolution ρ
    (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k') ^ P i).coeff n) (2 * P i) (2 * P i - 1)
    (SwappedVacuum.zeroHeightMoment y s u v) (fun n => u ≫ (y ^ n) ≫ ell)
    (SwappedVacuum.zero_height_moment (-1) x y s u v ell (2 * P i) (by omega)
      (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k') ^ P i).coeff n)
      (SwappedVacuum.square_add_one_coeff_top (P i))
      (fun n _ => by
        rw [smul_eq_mul]
        exact SwappedVacuum.square_add_one_coeff_mul_neg_one_pow (P i) n)
      hslide hwindow hprobe)
  have h₀ := (SwappedVacuum.odd_cap_moments D φ P i hi (2 * P i - 1) e
    (fun l => ρ (SwappedVacuum.zeroHeightMoment y s u v l)) (fun n => ρ (u ≫ (y ^ n) ≫ ell))
    hK hT r).2
  have h₁ := (SwappedVacuum.odd_cap_moments D φ P i hi (2 * P i - 1) e
    (fun l => ρ (SwappedVacuum.zeroHeightMoment y s u v l)) (fun n => ρ (u ≫ (y ^ n) ≫ ell))
    hK hT (r + 1)).1
  rw [SwappedVacuum.zeroHeightMoment, ite_eq_right (show 2 * r + 1 ≠ 0 by omega),
    show 2 * r + 1 - 1 = 2 * r by omega] at h₀
  rw [SwappedVacuum.zeroHeightMoment, ite_eq_right (show 2 * (r + 1) ≠ 0 by omega),
    show 2 * (r + 1) - 1 = 2 * r + 1 by omega] at h₁
  exact ⟨h₀, h₁⟩

/-- Even colour, negative height, read through an algebra map `ρ`. -/
private theorem even_negative_cap_moments_of_slide (D : SKM.Datum I' X') {R : Type*} [Ring R]
    [Algebra k' R] (φ : MvPolynomial (I' × ℕ) k' →ₐ[k'] R) (ρ : End V' →ₐ[k'] R)
    (P : I' → ℕ) (i : I') (hi : D.parity i = 0)
    (x : End Xo) (y : End Yo) (s : Xo ⟶ Yo) (u : V' ⟶ Yo) (v : Xo ⟶ V') (ell : Yo ⟶ V')
    (N : ℕ) (hPN : P i < N)
    (hslide : s ≫ y - (1 : k') • (x ≫ s) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V' else 0)
    (hprobe : SwappedVacuum.capPolynomial
      (fun n => ((Polynomial.X - 1 : Polynomial k') ^ P i).coeff n) (P i) x = 0)
    (j : Yo ⟶ Xo) (B : Fin (N - P i) → (Yo ⟶ V'))
    (H : SwappedAssembly.ProbeWindow.IsCupInverse s (fun n => u ≫ (y ^ n.val)) j B)
    (hT : PowerSeries.mk (fun l => ρ (u ≫ (y ^ (N - 1 + l)) ≫ ell)) =
      PowerSeries.map φ.toRingHom
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k' i)) 1))
    (l : ℕ) :
    ρ (u ≫ (y ^ (N - P i - 1 + l)) ≫ B ⟨N - P i - 1, by omega⟩) =
      φ (PowerSeries.coeff l
        (VacuumSeries.momentSeries k' (SKM.SYM.probeSeriesInv D k' P) i)) :=
  SwappedVacuum.even_cap_moments D φ P i hi (N - 1)
    (fun l => ρ (u ≫ (y ^ (N - P i - 1 + l)) ≫ B ⟨N - P i - 1, by omega⟩))
    (fun n => ρ (u ≫ (y ^ n) ≫ ell))
    (map_probe_convolution ρ (fun n => ((Polynomial.X - 1 : Polynomial k') ^ P i).coeff n)
      (P i) (N - 1)
      (fun l => u ≫ (y ^ (N - P i - 1 + l)) ≫ B ⟨N - P i - 1, by omega⟩)
      (fun n => u ≫ (y ^ n) ≫ ell)
      (SwappedVacuum.negative_inverse_cap_moment 1 x y s u v ell N (P i) hPN
        (fun n => ((Polynomial.X - 1 : Polynomial k') ^ P i).coeff n)
        (SwappedVacuum.sub_one_pow_coeff_top (P i))
        (fun n _ => by rw [one_pow, mul_one])
        hslide hwindow hprobe j B H)) hT l

/-- Even colour, zero height, read through an algebra map `ρ`. -/
private theorem even_zero_cap_moments_of_slide (D : SKM.Datum I' X') {R : Type*} [Ring R]
    [Algebra k' R] (φ : MvPolynomial (I' × ℕ) k' →ₐ[k'] R) (ρ : End V' →ₐ[k'] R)
    (P : I' → ℕ) (i : I') (hi : D.parity i = 0) (hP : 0 < P i)
    (x : End Xo) (y : End Yo) (s : Xo ≅ Yo) (u : V' ⟶ Yo) (v : Xo ⟶ V') (ell : Yo ⟶ V')
    (N : ℕ) (hNP : N = P i)
    (hslide : s.hom ≫ y - (1 : k') • (x ≫ s.hom) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V' else 0)
    (hprobe : SwappedVacuum.capPolynomial
      (fun n => ((Polynomial.X - 1 : Polynomial k') ^ P i).coeff n) (P i) x = 0)
    (hT : PowerSeries.mk (fun l => ρ (u ≫ (y ^ (N - 1 + l)) ≫ ell)) =
      PowerSeries.map φ.toRingHom
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k' i)) 1))
    (l : ℕ) :
    ρ (u ≫ (y ^ l) ≫ s.inv ≫ v) =
      φ (PowerSeries.coeff (l + 1)
        (VacuumSeries.momentSeries k' (SKM.SYM.probeSeriesInv D k' P) i)) := by
  subst hNP
  have hK := map_probe_convolution ρ
    (fun n => ((Polynomial.X - 1 : Polynomial k') ^ P i).coeff n) (P i) (P i - 1)
    (SwappedVacuum.zeroHeightMoment y s u v) (fun n => u ≫ (y ^ n) ≫ ell)
    (SwappedVacuum.zero_height_moment 1 x y s u v ell (P i) hP
      (fun n => ((Polynomial.X - 1 : Polynomial k') ^ P i).coeff n)
      (SwappedVacuum.sub_one_pow_coeff_top (P i))
      (fun n _ => by rw [one_pow, smul_eq_mul, mul_one])
      hslide hwindow hprobe)
  have h := SwappedVacuum.even_cap_moments D φ P i hi (P i - 1)
    (fun l => ρ (SwappedVacuum.zeroHeightMoment y s u v l)) (fun n => ρ (u ≫ (y ^ n) ≫ ell))
    hK hT (l + 1)
  rw [SwappedVacuum.zeroHeightMoment, ite_eq_right (show l + 1 ≠ 0 by omega),
    Nat.add_sub_cancel] at h
  exact h

end Generic

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

omit [Fintype I] in
/-- A power series whose coefficients are the images of those of `g` is the image of `g`. -/
private theorem mk_eq_map_of_coeff {S R : Type*} [CommRing S] [Ring R] (φ : S →+* R)
    (f : ℕ → R) (g : PowerSeries S) (h : ∀ l, f l = φ (PowerSeries.coeff l g)) :
    PowerSeries.mk f = PowerSeries.map φ g := by
  ext l
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_map]
  exact h l

/-- Left multiplication by the polynomial coefficients on the coefficient quotient. -/
def capCoefficientLmul : MvPolynomial (I × ℕ) k →ₐ[k] Module.End k AQ :=
  (Algebra.lmul k AQ).comp (polynomialToPower D cutoff L)

omit [Fintype I] in
theorem capCoefficientLmul_apply (p : MvPolynomial (I × ℕ) k) (w : AQ) :
    capCoefficientLmul D cutoff L p w = polynomialToPower D cutoff L p * w := rfl

omit [Fintype I] in
private theorem capCoefficientLmul_ringHom_apply (p : MvPolynomial (I × ℕ) k) (w : AQ) :
    (capCoefficientLmul D cutoff L).toRingHom p w = polynomialToPower D cutoff L p * w := rfl

omit [Fintype I] in
private theorem cap_lmul_apply (a w : AQ) : Algebra.lmul k AQ a w = a * w := rfl

omit [Fintype I] in
private theorem cap_end_mul_apply (f g : Module.End k AQ) (w : AQ) : (f * g) w = f (g w) := rfl

private theorem unit_cap_moment (hN : 0 < cutoff i) (n : ℕ) :
    (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN = tensorUnitCapClosure D Sc m cutoff L i hN n := by
  rw [tensorUnitCapClosure, unitDotColumn_eq_restrictedDotEnd, Category.assoc]
  rfl

omit [Fintype I] in
private theorem delta_commute (hi : D.parity i = 1) (p : MvPolynomial (I × ℕ) k) :
    Commute (polynomialToPower D cutoff L p) ((-1 : k) ^ (cutoff i + 1) •
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) :=
  (((SKM.SYM.polynomialInclude_commute D k p (SKM.SYM.delta D k ⟨i, hi⟩)).map
    (coefficientPowerQuotientMap D cutoff L)).smul_right _)

private theorem odd_reservoir_even (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + 2 * r)) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN) =
      (capCoefficientLmul D cutoff L).toRingHom (PowerSeries.coeff r
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) := by
  refine tensorVacuumEndDecode_eq_of D Sc m cutoff L _ _ fun z => ?_
  rw [unit_cap_moment D Sc m cutoff L i hN, capCoefficientLmul_ringHom_apply]
  have hm := tensorPowerVacuumCap_moment_even D Sc m cutoff L i hi hN r z
  show _ = completeCoefficient D cutoff L i r * _
  convert hm using 3

private theorem odd_reservoir_odd (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫
          (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + (2 * r + 1))) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN) =
      (capCoefficientLmul D cutoff L).toRingHom (PowerSeries.coeff r
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) *
        Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) := by
  refine tensorVacuumEndDecode_eq_of D Sc m cutoff L _ _ fun z => ?_
  rw [unit_cap_moment D Sc m cutoff L i hN, cap_end_mul_apply, cap_lmul_apply,
    capCoefficientLmul_ringHom_apply, ← mul_assoc, (delta_commute D cutoff L i hi _).eq,
    smul_mul_assoc]
  convert tensorPowerVacuumCap_moment_odd D Sc m cutoff L i hi hN r z using 3
  rfl

/-- The reservoir series of the tensor vacuum at an odd colour, in the decode
chart: `T(z) = A(z²)(1 + e z)` with `A = 1/C(-w)` and `e = (-1)^(N+1) δ`. -/
private theorem odd_reservoir_series (hi : D.parity i = 1) (hN : 0 < cutoff i) :
    PowerSeries.mk (fun l => tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + l)) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN)) =
      PowerSeries.map (capCoefficientLmul D cutoff L).toRingHom (PowerSeries.expand 2 two_ne_zero
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) *
        (1 + PowerSeries.C (Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩))) * PowerSeries.X) :=
  SwappedVacuum.mk_eq_expand_mul_one_add (capCoefficientLmul D cutoff L).toRingHom _ _ _
    (odd_reservoir_even D Sc m cutoff L i hi hN)
    (odd_reservoir_odd D Sc m cutoff L i hi hN)

private theorem even_reservoir_coefficient (hi : D.parity i = 0) (hN : 0 < cutoff i) (l : ℕ) :
    tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + l)) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN) =
      (capCoefficientLmul D cutoff L).toRingHom (PowerSeries.coeff l
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) := by
  have hm := fun z => (tensorPowerVacuumCap_moment_apply D Sc m cutoff L i hN
    (cutoff i - 1 + l) z).trans (congrFun (congrArg HMul.hMul
      (even_colour_signedMoment D Sc cutoff L i hi hN l))
        (tensorVacuumDecodeLinear D Sc m cutoff L z))
  refine tensorVacuumEndDecode_eq_of D Sc m cutoff L _ _ fun z => ?_
  rw [unit_cap_moment D Sc m cutoff L i hN, capCoefficientLmul_ringHom_apply]
  show _ = completeCoefficient D cutoff L i l * _
  convert hm z using 3

/-- The reservoir series of the tensor vacuum at an even colour, in the decode
chart: `T(z) = 1/E(-z)`, the complete coefficients. -/
theorem tensorVacuum_even_reservoir_series (hi : D.parity i = 0) (hN : 0 < cutoff i) :
    PowerSeries.mk (fun l => tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + l)) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN)) =
      PowerSeries.map (capCoefficientLmul D cutoff L).toRingHom
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1) :=
  mk_eq_map_of_coeff _ _ _ (even_reservoir_coefficient D Sc m cutoff L i hi hN)

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

/-- At an even colour the probe dot satisfies `(x - 1)^(m i) = 0` as a cap polynomial. -/
theorem shiftedPreDot_even_capPolynomial (hi : D.parity i = 0) :
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

include sy hc in
private theorem odd_slide (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫ evaluatedPostDot D Sc m cutoff bound i H -
      (-1 : k) • (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V := by
  have hs := evaluatedMixedBend_odd_slide D Sc m cutoff bound sy hc i hi hP H
  simpa only [hi, koszulSign_one_one, neg_one_zsmul, neg_one_smul] using hs

include sy hc in
/-- The even-colour central slide of the A6 bend, with the unit Koszul sign made explicit. -/
theorem evaluatedMixedBend_even_slide_sub (hi : D.parity i = 0) (hP : 0 < probeCutoff D m i) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫ evaluatedPostDot D Sc m cutoff bound i H -
      (1 : k) • (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V := by
  have hs := evaluatedMixedBend_even_slide D Sc m cutoff bound sy hc i hi hP H
  rw [one_smul]
  simpa only [hi, koszulSign_zero_left, one_smul] using hs

include sy hc in
/-- The decoded endomorphism form of both odd negative-height moment identities. -/
private theorem odd_negative_decoded
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (r : ℕ) :
    tensorVacuumEndDecode D Sc m cutoff L ((adjunction K).unit.app V ≫
        (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 2 * m i - 1 + 2 * r)) ≫
          B ⟨cutoff i - 2 * m i - 1, by omega⟩) =
        capCoefficientLmul D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) ∧
      tensorVacuumEndDecode D Sc m cutoff L ((adjunction K).unit.app V ≫
        (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 2 * m i - 1 + (2 * r + 1))) ≫
          B ⟨cutoff i - 2 * m i - 1, by omega⟩) =
        Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        capCoefficientLmul D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) := by
  have hwin : ∀ a < cutoff i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ a) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = cutoff i then 𝟙 V else 0 :=
    fun a ha => tensorPowerVacuumCap_window D Sc m cutoff L i hN a ha
  have h := odd_negative_cap_moments_of_slide D (capCoefficientLmul D cutoff L)
    (tensorVacuumEndDecode D Sc m cutoff L) m i hi (shiftedPreDot D Sc m R₀ i H)
    (evaluatedPostDot D Sc m cutoff bound i H) (evaluatedMixedBend D Sc m cutoff bound i hP H)
    ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H)
    (tensorPowerVacuumCap D Sc m cutoff L i hN) (cutoff i) hPN
    (Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)))
    (fun p => (delta_commute D cutoff L i hi p).map (Algebra.lmul k AQ))
    (odd_slide D Sc m cutoff L sy hc i hi hP) hwin (odd_probe_polynomial D Sc m cutoff L i hi)
    j B hB (odd_reservoir_series D Sc m cutoff L i hi hN) r
  exact h

/-- The carrier `res (ind V)` of the restricted reservoir dot on the tensor vacuum value,
written as in `evaluatedPostDot`. -/
abbrev unitColumnCarrier := (restriction K).obj ((induction K).obj ((H).obj N₀))

/-- The unit column `η ≫ xᵉ ≫ B n` of a family `B` of maps into the tensor vacuum value. -/
abbrev rightwardUnitColumn {w : ℕ} (B : Fin w → (unitColumnCarrier D Sc m cutoff L i ⟶ V))
    (e : ℕ) (n : Fin w) : V ⟶ V :=
  (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ e) ≫ B n

/-- The normalized odd coefficient `(-1)^(N+1) δ` in the coefficient quotient. -/
def oddMomentScalar (hi : D.parity i = 1) : CoefficientPowerQuotient (k := k) D cutoff L :=
  (-1 : k) ^ (cutoff i + 1) • coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)

include sy hc in
/-- **Odd colour, negative height, on the tensor vacuum: even moments.** For
probe exponent `M = m i` and reservoir cutoff `N = cutoff i` with `2M < N`, and
any entrywise inverse `[j; B]` of the cup window of the A6 bend with the
unit/post-dot rows, the decoded even moments of the extreme inverse cap are the
coefficients of `(1 + w)^M / C(-w)`. -/
theorem tensorVacuumNegativeCap_odd_moments_even
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (unitColumnCarrier D Sc m cutoff L i ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((rightwardUnitColumn D Sc m cutoff L i B (cutoff i - 2 * m i - 1 + 2 * r)
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  have h := odd_negative_decoded D Sc m cutoff L sy hc i hi hP hN hPN j B hB r
  have e1 := LinearMap.congr_fun h.1 (tensorVacuumDecodeLinear D Sc m cutoff L z)
  rw [tensorVacuumEndDecode_apply, capCoefficientLmul_apply] at e1
  exact e1

include sy hc in
/-- **Odd colour, negative height, on the tensor vacuum: odd moments.** Under
the hypotheses of `tensorVacuumNegativeCap_odd_moments_even`, the decoded odd
moments carry the normalized odd coefficient `(-1)^(N+1) δ` in front of the
coefficients of `(1 + w)^M / C(-w)`. -/
theorem tensorVacuumNegativeCap_odd_moments_odd
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (unitColumnCarrier D Sc m cutoff L i ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((rightwardUnitColumn D Sc m cutoff L i B (cutoff i - 2 * m i - 1 + (2 * r + 1))
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      oddMomentScalar D cutoff L i hi *
        (polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
          tensorVacuumDecodeLinear D Sc m cutoff L z) := by
  have h := odd_negative_decoded D Sc m cutoff L sy hc i hi hP hN hPN j B hB r
  have e2 := LinearMap.congr_fun h.2 (tensorVacuumDecodeLinear D Sc m cutoff L z)
  rw [tensorVacuumEndDecode_apply] at e2
  unfold oddMomentScalar
  exact e2

include sy hc in
/-- **Odd colour, negative height: the last unit column.** Both moment identities of
`tensorVacuumNegativeCap_odd_moments_even` and `tensorVacuumNegativeCap_odd_moments_odd`. -/
theorem rightwardUnitColumn_odd_moments
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (unitColumnCarrier D Sc m cutoff L i ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((rightwardUnitColumn D Sc m cutoff L i B (cutoff i - 2 * m i - 1 + 2 * r)
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z ∧
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((rightwardUnitColumn D Sc m cutoff L i B (cutoff i - 2 * m i - 1 + (2 * r + 1))
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      oddMomentScalar D cutoff L i hi *
        (polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
          tensorVacuumDecodeLinear D Sc m cutoff L z) :=
  ⟨tensorVacuumNegativeCap_odd_moments_even D Sc m cutoff L sy hc i hi hP
      (Nat.pos_of_ne_zero (by omega)) hPN j B hB r z,
    tensorVacuumNegativeCap_odd_moments_odd D Sc m cutoff L sy hc i hi hP
      (Nat.pos_of_ne_zero (by omega)) hPN j B hB r z⟩

include sy hc in
/-- **Odd colour, zero height, on the tensor vacuum: even moments.** For
`cutoff i = 2 M`, `M = m i`, and the A6 bend an isomorphism `s`, the decoded
moment `u ≫ y^(2r) ≫ s⁻¹ ≫ v` is `δ · A_r`, where `A_r` is the `r`th
coefficient of `(1 + w)^M / C(-w)` and `δ` the normalized odd coefficient
`(-1)^(N+1) δ`. -/
theorem tensorVacuumZeroHeightCap_odd_moments_even
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (hcut : cutoff i = 2 * m i)
    (s : shiftedPreSourceObject D Sc m R₀ i H ≅ (restriction K).obj ((induction K).obj V))
    (hsb : s.hom = evaluatedMixedBend D Sc m cutoff bound i hP H)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        (((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (2 * r)) ≫
          s.inv ≫ shiftedPreCap D Sc m R₀ i hP H).total star z) =
      ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        (polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
          tensorVacuumDecodeLinear D Sc m cutoff L z) := by
  have hs := odd_slide D Sc m cutoff L sy hc i hi hP
  rw [← hsb] at hs
  have hwin : ∀ a < cutoff i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ a) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = cutoff i then 𝟙 V else 0 :=
    fun a ha => tensorPowerVacuumCap_window D Sc m cutoff L i hN a ha
  obtain ⟨h1, -⟩ := odd_zero_cap_moments_of_slide D (capCoefficientLmul D cutoff L)
    (tensorVacuumEndDecode D Sc m cutoff L) m i hi (by omega) (shiftedPreDot D Sc m R₀ i H)
    (evaluatedPostDot D Sc m cutoff bound i H) s
    ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H)
    (tensorPowerVacuumCap D Sc m cutoff L i hN)
    (Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)))
    (cutoff i) hcut hs hwin (odd_probe_polynomial D Sc m cutoff L i hi)
    (odd_reservoir_series D Sc m cutoff L i hi hN) r
  have e1 := LinearMap.congr_fun
    (h1.trans ((delta_commute D cutoff L i hi _).map (Algebra.lmul k AQ)).eq)
    (tensorVacuumDecodeLinear D Sc m cutoff L z)
  rw [tensorVacuumEndDecode_apply, cap_end_mul_apply, cap_lmul_apply, cap_lmul_apply] at e1
  convert e1 using 3

include sy hc in
/-- **Odd colour, zero height, on the tensor vacuum: odd moments.** Under the
hypotheses of `tensorVacuumZeroHeightCap_odd_moments_even`, the decoded moment
`u ≫ y^(2r+1) ≫ s⁻¹ ≫ v` is `A_(r+1)`. -/
theorem tensorVacuumZeroHeightCap_odd_moments_odd
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (hcut : cutoff i = 2 * m i)
    (s : shiftedPreSourceObject D Sc m R₀ i H ≅ (restriction K).obj ((induction K).obj V))
    (hsb : s.hom = evaluatedMixedBend D Sc m cutoff bound i hP H)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        (((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (2 * r + 1)) ≫
          s.inv ≫ shiftedPreCap D Sc m R₀ i hP H).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff (r + 1)
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  have hs := odd_slide D Sc m cutoff L sy hc i hi hP
  rw [← hsb] at hs
  have hwin : ∀ a < cutoff i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ a) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = cutoff i then 𝟙 V else 0 :=
    fun a ha => tensorPowerVacuumCap_window D Sc m cutoff L i hN a ha
  obtain ⟨-, h2⟩ := odd_zero_cap_moments_of_slide D (capCoefficientLmul D cutoff L)
    (tensorVacuumEndDecode D Sc m cutoff L) m i hi (by omega) (shiftedPreDot D Sc m R₀ i H)
    (evaluatedPostDot D Sc m cutoff bound i H) s
    ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H)
    (tensorPowerVacuumCap D Sc m cutoff L i hN)
    (Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)))
    (cutoff i) hcut hs hwin (odd_probe_polynomial D Sc m cutoff L i hi)
    (odd_reservoir_series D Sc m cutoff L i hi hN) r
  have e2 := LinearMap.congr_fun h2 (tensorVacuumDecodeLinear D Sc m cutoff L z)
  rw [tensorVacuumEndDecode_apply, capCoefficientLmul_apply] at e2
  convert e2 using 3

/-! ### Even colour -/

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
  have hwin : ∀ a < cutoff i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ a) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = cutoff i then 𝟙 V else 0 :=
    fun a ha => tensorPowerVacuumCap_window D Sc m cutoff L i hN a ha
  have h1 := even_negative_cap_moments_of_slide D (capCoefficientLmul D cutoff L)
    (tensorVacuumEndDecode D Sc m cutoff L) m i hi (shiftedPreDot D Sc m R₀ i H)
    (evaluatedPostDot D Sc m cutoff bound i H) (evaluatedMixedBend D Sc m cutoff bound i hP H)
    ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H)
    (tensorPowerVacuumCap D Sc m cutoff L i hN) (cutoff i) hPN
    (evaluatedMixedBend_even_slide_sub D Sc m cutoff L sy hc i hi hP) hwin
    (shiftedPreDot_even_capPolynomial D Sc m cutoff L i hi)
    j B hB (tensorVacuum_even_reservoir_series D Sc m cutoff L i hi hN) l
  have e1 := LinearMap.congr_fun h1 (tensorVacuumDecodeLinear D Sc m cutoff L z)
  rw [tensorVacuumEndDecode_apply, capCoefficientLmul_apply] at e1
  exact e1

include sy hc in
/-- **Even colour, zero height, on the tensor vacuum.** For `cutoff i = M`,
`M = m i`, and the bend an isomorphism `s`, the decoded moments of the
principal inverse are `u ≫ y^l ≫ s⁻¹ ≫ v = A_(l+1)`, where `A_r` is the `r`th
coefficient of `(1 - w)^M / E(-w)`. -/
theorem tensorVacuumZeroHeightCap_even_moments
    (hi : D.parity i = 0) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (hcut : cutoff i = m i)
    (s : shiftedPreSourceObject D Sc m R₀ i H ≅ (restriction K).obj ((induction K).obj V))
    (hsb : s.hom = evaluatedMixedBend D Sc m cutoff bound i hP H)
    (l : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        (((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ l) ≫
          s.inv ≫ shiftedPreCap D Sc m R₀ i hP H).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff (l + 1)
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  have hs := evaluatedMixedBend_even_slide_sub D Sc m cutoff L sy hc i hi hP
  rw [← hsb] at hs
  have hwin : ∀ a < cutoff i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ a) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = cutoff i then 𝟙 V else 0 :=
    fun a ha => tensorPowerVacuumCap_window D Sc m cutoff L i hN a ha
  have h1 := even_zero_cap_moments_of_slide D (capCoefficientLmul D cutoff L)
    (tensorVacuumEndDecode D Sc m cutoff L) m i hi (by omega) (shiftedPreDot D Sc m R₀ i H)
    (evaluatedPostDot D Sc m cutoff bound i H) s
    ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H)
    (tensorPowerVacuumCap D Sc m cutoff L i hN) (cutoff i) hcut hs hwin
    (shiftedPreDot_even_capPolynomial D Sc m cutoff L i hi)
    (tensorVacuum_even_reservoir_series D Sc m cutoff L i hi hN) l
  have e1 := LinearMap.congr_fun h1 (tensorVacuumDecodeLinear D Sc m cutoff L z)
  rw [tensorVacuumEndDecode_apply, capCoefficientLmul_apply] at e1
  convert e1 using 3

end OddMath.QuiverHecke.ELVOld
