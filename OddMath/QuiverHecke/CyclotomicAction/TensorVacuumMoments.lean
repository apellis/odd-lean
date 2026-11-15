import OddMath.QuiverHecke.CyclotomicAction.ProbeCentral
import OddMath.QuiverHecke.SwappedVacuum.InverseCapColourSeries
import OddMath.QuiverHecke.CyclotomicAction.CoefficientPowerSeries
import OddMath.QuiverHecke.CyclotomicAction.ProbePaddedVacuum
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumBends
import OddMath.QuiverHecke.SwappedVacuum.InverseColumnEvenSeries
import OddMath.QuiverHecke.CyclotomicAction.ParameterUntwist

/-!
# Tensor vacuum moments

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
namespace OddMath.QuiverHecke.ELV
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

local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "W₀" => Functor.obj (restriction (contentInclusion D Sc cutoff bound (0 : Multiset I)))
  (weightedVacuum D Sc cutoff L)
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound W₀
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m
local notation "V" => Superfunctor.obj H N₀
local notation "star" => (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff bound 0)
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L

variable (hdot :
  TruncatedAppendDotNilpotent D Sc cutoff (SKM.SYM.elvPowerWeightBound D cutoff L + 1))

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

include hdot in
private theorem odd_slide (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫ evaluatedPostDot D Sc m cutoff bound i H -
      (-1 : k) • (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V :=
  evaluatedMixedBend_odd_slide_neg D Sc m cutoff _ hdot i hi hP H

include hdot in
/-- The even-colour central slide of the A6 bend, with the unit Koszul sign made explicit. -/
theorem evaluatedMixedBend_even_slide_sub (hi : D.parity i = 0) (hP : 0 < probeCutoff D m i) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫ evaluatedPostDot D Sc m cutoff bound i H -
      (1 : k) • (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V :=
  evaluatedMixedBend_even_slide_one D Sc m cutoff _ hdot i hi hP H

include hdot in
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
    (odd_slide D Sc m cutoff L hdot i hi hP) hwin (odd_probe_polynomial D Sc m cutoff L i hi)
    j B hB (odd_reservoir_series D Sc m cutoff L i hi hN) r
  exact h

include hdot in
/-- **Odd colour, negative height, on the tensor vacuum: even moments.** For
probe exponent `M = m i` and reservoir cutoff `N = cutoff i` with `2M < N`, and
any entrywise inverse `[j; B]` of the cup window of the A6 bend with the
unit/post-dot rows, the decoded even moments of the extreme inverse cap are the
coefficients of `(1 + w)^M / C(-w)`. -/
theorem tensorVacuumNegativeCap_odd_moments_even
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
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  have h := odd_negative_decoded D Sc m cutoff L hdot i hi hP hN hPN j B hB r
  have e1 := LinearMap.congr_fun h.1 (tensorVacuumDecodeLinear D Sc m cutoff L z)
  rw [tensorVacuumEndDecode_apply, capCoefficientLmul_apply] at e1
  exact e1

include hdot in
/-- **Odd colour, negative height, on the tensor vacuum: odd moments.** Under
the hypotheses of `tensorVacuumNegativeCap_odd_moments_even`, the decoded odd
moments carry the normalized odd coefficient `(-1)^(N+1) δ` in front of the
coefficients of `(1 + w)^M / C(-w)`. -/
theorem tensorVacuumNegativeCap_odd_moments_odd
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
          (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 2 * m i - 1 + (2 * r + 1))) ≫
            B ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        (polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
          tensorVacuumDecodeLinear D Sc m cutoff L z) := by
  have h := odd_negative_decoded D Sc m cutoff L hdot i hi hP hN hPN j B hB r
  have e2 := LinearMap.congr_fun h.2 (tensorVacuumDecodeLinear D Sc m cutoff L z)
  rw [tensorVacuumEndDecode_apply] at e2
  exact e2

include hdot in
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
  have hs := odd_slide D Sc m cutoff L hdot i hi hP
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

include hdot in
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
  have hs := odd_slide D Sc m cutoff L hdot i hi hP
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

include hdot in
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
    (evaluatedMixedBend_even_slide_sub D Sc m cutoff L hdot i hi hP) hwin
    (shiftedPreDot_even_capPolynomial D Sc m cutoff L i hi)
    j B hB (tensorVacuum_even_reservoir_series D Sc m cutoff L i hi hN) l
  have e1 := LinearMap.congr_fun h1 (tensorVacuumDecodeLinear D Sc m cutoff L z)
  rw [tensorVacuumEndDecode_apply, capCoefficientLmul_apply] at e1
  exact e1

include hdot in
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
  have hs := evaluatedMixedBend_even_slide_sub D Sc m cutoff L hdot i hi hP
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Even moments of the leftward vacuum bubble entries

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8 (the left-bubble series of `AdjunctionBubbleSeries.left_even`).

The even-colour counterpart of `ELVTensorVacuumColumnMoments` and
`ELVTensorVacuumLeftwardMoments`. On the prescribed tensor vacuum at an even
colour, with the actual mate slide (`q = 1`), the probe `(x - 1)^m`, the
reservoir window and the reservoir moments `1/E(-z)`, the decoded moments of a
positive-height inverse column `a` are the coefficients of the substituted
series `E(-w)(1 - w)^(-m)` (`tensorVacuumColumn_even_moments`). Leftward data
satisfying the positive inverse equations at the vacuum sector give such an
inverse whose column products with the native cap rows are the conjugated
evaluated left bubble entries `dcup n ≫ ε xᴺ`
(`vacuumLeftwardCapInverse_even`, `tensorVacuum_leftward_even_moments`).
No inverse, moment or bubble value is assumed. See
`docs/Nondegeneracy/InverseColumnMoments.md`.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient ProbeVacuumCap
open Finset
universe u

section Generic

variable {I' X' k' : Type u} [AddCommGroup X'] [CommRing k'] {C : Type*} [Category C]
  [Preadditive C] [Linear k' C] {Xo Yo V' : C}

/-- The even inverse-column moment identity for an arbitrary column `a`, read through
an algebra map `ρ` on `End V'`: with the mate slide at `q = 1`, the even probe
`(x - 1)^P`, the two windows and the reservoir series `1/E(-z)`, the column moments
are the substituted-series coefficients. -/
theorem even_column_moments_of_slide (D : SKM.Datum I' X') {R : Type*} [Ring R]
    [Algebra k' R] (φ : MvPolynomial (I' × ℕ) k' →ₐ[k'] R) (ρ : End V' →ₐ[k'] R)
    (P : I' → ℕ) (i : I') (hi : D.parity i = 0) (h N : ℕ) (hh : 0 < h) (hN : 0 < N)
    (hhN : h + N = P i) (x : End Xo) (y : End Yo) (s : Xo ⟶ Yo) (u : V' ⟶ Yo)
    (v : Xo ⟶ V') (ell : Yo ⟶ V') (a : V' ⟶ Xo)
    (hslide : s ≫ y - (1 : k') • (x ≫ s) = v ≫ u) (has : a ≫ s = 0)
    (hprobe : SwappedVacuum.capPolynomial
      (fun n => ((Polynomial.X - 1 : Polynomial k') ^ P i).coeff n) (h + N) x = 0)
    (hcol : ∀ j < h, a ≫ (x ^ j) ≫ v = if j + 1 = h then 𝟙 V' else 0)
    (hwin : ∀ j < N, u ≫ (y ^ j) ≫ ell = if j + 1 = N then 𝟙 V' else 0)
    (hT : PowerSeries.mk (fun l => ρ (u ≫ (y ^ (N - 1 + l)) ≫ ell)) =
      PowerSeries.map φ.toRingHom
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k' i)) 1))
    (n : ℕ) :
    ρ (a ≫ (x ^ (h - 1 + n)) ≫ v) = φ (PowerSeries.coeff n
        (VacuumSeries.substitutedSeries k' (SKM.SYM.probeSeries D k' P) i)) := by
  refine SwappedVacuum.even_inverse_column_moments D φ P i hi h N hh hN hhN
    (fun j => ρ (a ≫ (x ^ j) ≫ v)) (fun j => ρ (u ≫ (y ^ j) ≫ ell)) ?_ ?_ ?_ ?_ hT n
  · intro j hj
    simp only [hcol j hj]
    split_ifs
    exacts [map_one ρ, map_zero ρ]
  · intro j hj
    simp only [hwin j hj]
    split_ifs
    exacts [map_one ρ, map_zero ρ]
  · intro d
    have h0 := congrArg ρ (SwappedVacuum.column_reservoir_relation (1 : k') (by norm_num)
      x y s u v ell a (h + N) _ hslide has hprobe d)
    rw [map_zero, map_sum] at h0
    rw [← h0]
    refine sum_congr rfl fun n _ => ?_
    rw [map_smul, map_sum]
    refine congrArg _ (sum_congr rfl fun j _ => ?_)
    rw [map_smul, ← map_mul, End.mul_def]
  · intro mm
    have h0 := congrArg ρ (SwappedVacuum.column_probe_relation x v a (h + N) _ hprobe mm)
    rw [map_zero, map_sum] at h0
    rw [← h0]
    refine sum_congr rfl fun n _ => ?_
    rw [map_smul]

end Generic

section Tensor

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1

variable (hdot :
  TruncatedAppendDotNilpotent D Sc cutoff (SKM.SYM.elvPowerWeightBound D cutoff L + 1))
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

include hdot in
/-- **Even-colour column moments on the tensor vacuum.** For a column `a`
killed by the actual A6 bend with the column window of height `h`, where
`h + cutoff i = m i`, the decoded column moments `a ≫ x^(h-1+s) ≫ v` are the
coefficients of the substituted series of `AdjunctionBubbleSeries.left_even`. -/
theorem tensorVacuumColumn_even_moments
    (hi : D.parity i = 0) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (h : ℕ) (hh : 0 < h) (hhN : h + cutoff i = m i)
    (a : V ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (has : a ≫ evaluatedMixedBend D Sc m cutoff bound i hP H = 0)
    (hcol : ∀ j < h, a ≫ (shiftedPreDot D Sc m R₀ i H ^ j) ≫ shiftedPreCap D Sc m R₀ i hP H =
      if j + 1 = h then 𝟙 V else 0)
    (s : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((a ≫ (shiftedPreDot D Sc m R₀ i H ^ (h - 1 + s)) ≫
          shiftedPreCap D Sc m R₀ i hP H).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  have hwin : ∀ j < cutoff i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ j) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if j + 1 = cutoff i then 𝟙 V else 0 :=
    fun j hj => tensorPowerVacuumCap_window D Sc m cutoff L i hN j hj
  have hmom := even_column_moments_of_slide D (capCoefficientLmul D cutoff L)
    (tensorVacuumEndDecode D Sc m cutoff L) m i hi h (cutoff i) hh hN hhN
    (shiftedPreDot D Sc m R₀ i H)
    (evaluatedPostDot D Sc m cutoff bound i H) (evaluatedMixedBend D Sc m cutoff bound i hP H)
    ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H)
    (tensorPowerVacuumCap D Sc m cutoff L i hN) a
    (evaluatedMixedBend_even_slide_sub D Sc m cutoff L
      hdot i hi hP) has
    (by rw [hhN]; exact shiftedPreDot_even_capPolynomial D Sc m cutoff L i hi) hcol hwin
    (tensorVacuum_even_reservoir_series D Sc m cutoff L i hi hN) s
  have e1 := tensorVacuumEndDecode_apply D Sc m cutoff L
    (a ≫ (shiftedPreDot D Sc m R₀ i H ^ (h - 1 + s)) ≫ shiftedPreCap D Sc m R₀ i hP H) z
  rw [hmom, capCoefficientLmul_apply] at e1
  exact e1.symm

include hdot in
/-- **Chosen inverse column, even colour.** If the cap window `[bend; x^n ≫ v]_(n < h)` of
the actual A6 bend has an entrywise inverse `(j, A)`, its last padded column `A (h - 1)` has
the substituted-series moments of `tensorVacuumColumn_even_moments`. -/
theorem tensorVacuumCapInverse_even_moments
    (hi : D.parity i = 0) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (h : ℕ) (hh : 0 < h) (hhN : h + cutoff i = m i)
    (jY : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (A : Fin h → (V ⟶ shiftedPreSourceObject D Sc m R₀ i H))
    (hA : SwappedAssembly.ProbeWindow.IsCapInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n : Fin h => (shiftedPreDot D Sc m R₀ i H ^ (n : ℕ)) ≫ shiftedPreCap D Sc m R₀ i hP H)
      jY A)
    (s : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((A ⟨h - 1, by omega⟩ ≫ (shiftedPreDot D Sc m R₀ i H ^ (h - 1 + s)) ≫
          shiftedPreCap D Sc m R₀ i hP H).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  have hcol : ∀ j < h, A ⟨h - 1, by omega⟩ ≫ (shiftedPreDot D Sc m R₀ i H ^ j) ≫
      shiftedPreCap D Sc m R₀ i hP H = if j + 1 = h then 𝟙 V else 0 := by
    intro j hj
    have e := hA.2.2.2.1 ⟨h - 1, by omega⟩ ⟨j, hj⟩
    dsimp only at e
    rw [e]
    by_cases hj' : j + 1 = h
    · have hf : (⟨h - 1, by omega⟩ : Fin h) = ⟨j, hj⟩ := Fin.ext (by dsimp only; omega)
      simp only [hf, hj', ↓reduceIte]
    · have hf : ¬((⟨h - 1, by omega⟩ : Fin h) = ⟨j, hj⟩) := fun e => hj' (by
        rw [Fin.ext_iff] at e; dsimp only at e; omega)
      simp only [hf, hj', ↓reduceIte]
  exact tensorVacuumColumn_even_moments D Sc m cutoff L hdot i hi hP hN h hh hhN
    (A ⟨h - 1, by omega⟩) (hA.2.1 _) hcol s z

end Tensor

end OddMath.QuiverHecke.ELV

namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly ProbeVacuumCap PowerVacuumCoefficient
universe u

local instance leftwardEvenMomentsHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

section Generic

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance leftwardEvenMomentsZero [Fact Sc.PureNilpotent] (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (i : I)
local notation "p₀" => SPath.centralUpDn i (SKM.wt D ν₀ [SKM.dn i]) ν₀ ((0, 0) : Sector I)
  ⟨true, trivial⟩

include hdot in
/-- **The leftward vacuum cap inverse in the native chart (even colour).** Leftward
data satisfying the positive inverse equations at the vacuum sector give an
entrywise inverse of the native cap window `[bend; x ^ n ≫ v]_(n < h)` of the
evaluated A6 bend, whose columns are the explicit `vacuumLeftwardColumn`. -/
theorem vacuumLeftwardCapInverse_even [Fact Sc.PureNilpotent] (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (HP : (P).PosInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0) :
    ∃ j, ProbeWindow.IsCapInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (D.h i ν₀).toNat => (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ (n : ℕ)) ≫
          ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H)) j
        (fun n => vacuumLeftwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i Z hZ dc n) := by
  subst hZ
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by
    simp [StepValid]
  have hd : ¬StepValid (SKM.dn i) true ((0, 0) : Sector I) := by
    simp [StepValid]
  have h₁ := (P).isCapInverse_centralPadded_of_posInverseAt
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀ ((0, 0) : Sector I)
    (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) lc dc HP hu hd
  have h₃ := (h₁.coordinates (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm
    (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm).target
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H)
  have hs : (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
      (P).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i
        ((0, 0) : Sector I) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
        (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) :=
    (Iso.inv_comp_eq _).2 (paddedVacuumDx_even D Sc m cutoff bound ΛP ΛR hcP hcR H i
      hdot hP hi)
  have hw : ∀ n : ℕ, (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
      (P).centralPaddedCap i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true n ≫
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom =
      (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := fun n =>
    (Iso.inv_comp_eq _).2 (paddedVacuumCap_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i hP n)
  simp only [Iso.symm_hom, Iso.symm_inv, Category.assoc, hs, hw] at h₃
  exact ⟨_, h₃⟩

include hdot in
/-- **Leftward vacuum cap inverse with bubble-entry columns.** For leftward data
satisfying the positive inverse equations at an input equal to the vacuum sector
input, the native cap window of the evaluated A6 bend has an entrywise inverse
whose column products with the native cap rows `x ^ N ≫ v` are the evaluated left
bubble entries `dcup n ≫ ε xᴺ`, conjugated by one isomorphism `c` (even colour). -/
theorem vacuumLeftwardCapInverse_bubbleEntries_even [Fact Sc.PureNilpotent] (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (HP : (P).PosInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (cc : (P).CrossCoeff) (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0) :
    ∃ (c : _ ≅ _) (j : _) (A : Fin (D.h i ν₀).toNat → _),
      (∃ h, c.hom = eqToHom h) ∧ ProbeWindow.IsCapInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (D.h i ν₀).toNat => (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ (n : ℕ)) ≫
          ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H)) j A ∧
      ∀ (n : Fin (D.h i ν₀).toNat) (N : ℕ),
        A n ≫ (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ N) ≫
          ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) =
        c.inv ≫ (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          (dc n (.nil _) p₀ ≫ (P).epsEntry cc i N ν₀ p₀ (.nil _) Z) ≫ c.hom := by
  subst hZ
  obtain ⟨j, hj⟩ := vacuumLeftwardCapInverse_even D Sc m cutoff bound ΛP ΛR hcP hcR H
    hdot i _ rfl lc dc HP hP hi
  exact ⟨paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H, j, _,
    paddedVacuumCapTargetIso_hom_eq_eqToHom D Sc m cutoff bound ΛP ΛR hcP hcR H, hj,
    fun n N => vacuumLeftwardColumn_cap_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i dc cc hP
      n N⟩

end Generic

section Tensor

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (i : I)
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff
  (PowerWordContent.powerBound D cutoff L))
local notation "ν₀" => (P).wt ((0, 0) : Sector I)
local notation "Zt" => (SupportedSectors.tensorVacuum D Sc m cutoff L ΛP ΛR).obj
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D
  (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)
local notation "p₀" => SPath.centralUpDn i (SKM.wt D ν₀ [SKM.dn i]) ν₀ ((0, 0) : Sector I)
  ⟨true, trivial⟩

omit [Fintype I] in
private theorem even_probeCutoff' (hi : D.parity i = 0) : probeCutoff D m i = m i := by
  simp [probeCutoff, probeDotExponent, hi]

include hdot in
/-- **Even moments of the leftward vacuum bubble entries.** For an even colour with
`0 < N_i < P_i` and `h = P_i - N_i`, leftward data satisfying the positive inverse
equations at the tensor vacuum give an entrywise inverse `(j, A)` of the native cap
window of the tensor vacuum bend such that every column product
`A n ≫ x ^ N ≫ v` is the evaluated left bubble entry `dcup n ≫ ε xᴺ` conjugated by
one isomorphism `c`, and the last column has the substituted-series moments: the
shift `h - 1 + s` decodes to multiplication by the `s`-th coefficient of the
substituted probe series. -/
theorem tensorVacuum_leftward_even_moments [Fact Sc.PureNilpotent] (hi : D.parity i = 0)
    (hN : 0 < cutoff i) (hlt : cutoff i < probeCutoff D m i)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Zt ⟶ ((P).pathFunctor p).obj Zt)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Zt ⟶ ((P).pathFunctor p).obj Zt)
    (HP : (P).PosInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Zt lc dc)
    (cc : (P).CrossCoeff) :
    ∃ (c : _ ≅ V) (j : _) (A : Fin (probeCutoff D m i - cutoff i) →
        (V ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H)),
      (∃ h, c.hom = eqToHom h) ∧ ProbeWindow.IsCapInverse
        (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i (hN.trans hlt) H)
        (fun n : Fin (probeCutoff D m i - cutoff i) =>
          (shiftedPreDot D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H ^
              (n : ℕ)) ≫
            shiftedPreCap D (parameterTwist D Sc) m
              (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
              (hN.trans hlt) H) j A ∧
      (∀ (n : Fin (probeCutoff D m i - cutoff i)) (N : ℕ),
        A n ≫ (shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H ^ N) ≫
          shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
            (hN.trans hlt) H =
        c.inv ≫ (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          (dc n (.nil _) p₀ ≫ (P).epsEntry cc i N ν₀ p₀ (.nil _) Zt) ≫ c.hom) ∧
      ∀ (s : ℕ) (z : (V).obj star),
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
            ((A ⟨probeCutoff D m i - cutoff i - 1, by omega⟩ ≫
              (shiftedPreDot D (parameterTwist D Sc) m
                (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H ^
                (probeCutoff D m i - cutoff i - 1 + s)) ≫
              shiftedPreCap D (parameterTwist D Sc) m
                (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
                (hN.trans hlt) H).total star z) =
          polynomialToPower D cutoff L (PowerSeries.coeff s
              (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
            tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z := by
  classical
  have hP : 0 < probeCutoff D m i := hN.trans hlt
  have hlen := SupportedSectors.vacuum_positive_window_length D Sc m cutoff bound ΛP ΛR
    hcP hcR i
  have hex := vacuumLeftwardCapInverse_bubbleEntries_even D Sc m cutoff bound ΛP ΛR hcP hcR
    (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) hdot i Zt
    (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hcP hcR).symm lc dc HP cc hP hi
  rw [show vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) = H from
    tensorOutputAt_empty D (parameterTwist D Sc) m cutoff L ΛR, hlen] at hex
  obtain ⟨c, j, A, hceq, hA, hcap⟩ := hex
  have hhN : probeCutoff D m i - cutoff i + cutoff i = m i := by
    rw [← even_probeCutoff' D m i hi]
    omega
  exact ⟨c, j, A, hceq, hA, hcap, fun s z =>
    tensorVacuumCapInverse_even_moments D (parameterTwist D Sc) m cutoff L hdot i hi hP hN _
      (by omega) hhN j A hA s z⟩

end Tensor

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end

section

/-! # The rightward unit columns of the tensor vacuum

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

For a family `B` of maps into the tensor vacuum value `V`, the unit column
`η ≫ xᵉ ≫ B n : V ⟶ V` (`rightwardUnitColumn`) is the product of the native unit row
`η xᵉ` of the cup window with the `n`-th column of `B`. For an entrywise inverse
`(j, B)` of the cup window at an odd colour with `0 < 2 M < N`, the last unit column
has the decoded moments of `tensorVacuumNegativeCap_odd_moments_even/odd`
(`rightwardUnitColumn_odd_moments`). The column is named so that statements made with
other hom-category instances refer to this one composite.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient ProbeVacuumCap
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1

variable (hdot :
  TruncatedAppendDotNilpotent D Sc cutoff (SKM.SYM.elvPowerWeightBound D cutoff L + 1))
local notation "W₀" => Functor.obj (restriction (contentInclusion D Sc cutoff bound (0 : Multiset I)))
  (weightedVacuum D Sc cutoff L)
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound W₀
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m
local notation "V" => Superfunctor.obj H N₀
local notation "star" => (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff bound 0)

variable (i : I)

local notation "K" => contentAppend D Sc cutoff bound (0 : Multiset I) [i]

/-- The unit column `u ≫ xᵉ ≫ B n` of a family `B` of maps out of the object of an
endomorphism `x`, for a unit `u` into that object. It is generic in its objects, so its
instances are never written out. -/
abbrev rightwardUnitColumn {C : Type*} {_ : Category C} {Y Z : C} (u : Y ⟶ Z) (x : End Z)
    {w : ℕ} (B : Fin w → (Z ⟶ Y)) (e : ℕ) (n : Fin w) : Y ⟶ Y :=
  u ≫ (x ^ e) ≫ B n

/-- The decoded value of the last unit column `η xᵉ ≫ B (N - 2M - 1)` at shift `e`. -/
def rightwardLastColumnDecode (hPN : 2 * m i < cutoff i)
    (B : Fin (cutoff i - 2 * m i) → ((induction K ⋙ restriction K).obj V ⟶ V)) (e : ℕ) (z : (V).obj star) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  tensorVacuumDecodeLinear D Sc m cutoff L
    ((rightwardUnitColumn ((adjunction K).unit.app V)
      (evaluatedPostDot D Sc m cutoff bound i H) B e
      ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z)

/-- The normalized odd coefficient `(-1)^(N+1) δ_i` in the coefficient power quotient. -/
def rightwardOddScalar (hi : D.parity i = 1) : CoefficientPowerQuotient (k := k) D cutoff L :=
  coefficientPowerQuotientMap D cutoff L ((-1 : k) ^ (cutoff i + 1) • SKM.SYM.delta D k ⟨i, hi⟩)

omit [Fintype I] in
theorem rightwardOddScalar_eq (hi : D.parity i = 1) :
    rightwardOddScalar D cutoff L i hi =
      coefficientPowerQuotientMap D cutoff L
        ((-1 : k) ^ (cutoff i + 1) • SKM.SYM.delta D k ⟨i, hi⟩) := rfl

include hdot in
/-- `tensorVacuumNegativeCap_odd_moments_even` for `rightwardLastColumnDecode`, at a shift
`e` given by an equation, so that the shift is compared as a variable. -/
theorem rightwardLastColumnDecode_even
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (r e : ℕ) (he : e = cutoff i - 2 * m i - 1 + 2 * r) (z : (V).obj star) :
    rightwardLastColumnDecode D Sc m cutoff L i hPN B e z =
      polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  have h := tensorVacuumNegativeCap_odd_moments_even D Sc m cutoff L
      hdot i hi hP
    (Nat.pos_of_ne_zero (by omega)) hPN j B hB r z
  rw [← he] at h
  unfold rightwardLastColumnDecode
  exact h

include hdot in
/-- `tensorVacuumNegativeCap_odd_moments_odd` for `rightwardLastColumnDecode`, at a shift
`e` given by an equation, so that the shift is compared as a variable. -/
theorem rightwardLastColumnDecode_odd
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (r e : ℕ) (he : e = cutoff i - 2 * m i - 1 + (2 * r + 1)) (z : (V).obj star) :
    rightwardLastColumnDecode D Sc m cutoff L i hPN B e z =
      rightwardOddScalar D cutoff L i hi *
        (polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
          tensorVacuumDecodeLinear D Sc m cutoff L z) := by
  have h := tensorVacuumNegativeCap_odd_moments_odd D Sc m cutoff L
      hdot i hi hP
    (Nat.pos_of_ne_zero (by omega)) hPN j B hB r z
  rw [← he] at h
  unfold rightwardLastColumnDecode
  rw [rightwardOddScalar_eq, map_smul]
  exact h

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Odd moments of the rightward vacuum bubble entries

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

At negative height of the tensor vacuum (`2 M < N` for `M = m i`, `N = cutoff i`,
odd colour), leftward data satisfying the negative inverse equations give an
entrywise inverse `(j, B)` of the native cup window of the evaluated A6 bend
(`vacuumRightwardCupInverse_bubbleEntries`). Its products with the native unit rows
are the conjugated evaluated right bubble entries `η xᴺ ≫ dcap n`, and the extreme
column has the decoded moments of `rightwardUnitColumn_odd_moments_even/odd`:
the coefficients of `(1 + w)^M / C(-w)`, the odd ones multiplied by the normalized odd
coefficient. No inverse, moment or bubble value
is assumed.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly ProbeVacuumCap PowerVacuumCoefficient
universe u

local instance rightwardVacuumMomentsHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (i : I)
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff
  (PowerWordContent.powerBound D cutoff L))
local notation "ν₀" => (P).wt ((0, 0) : Sector I)
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D
  (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)
local notation "K" => contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i]
local notation "q₀" => SPath.centralDnUp i (SKM.wt D ν₀ [SKM.up i]) ν₀ ((0, 0) : Sector I)
  ⟨false, trivial⟩

omit [Fintype I] in
private theorem odd_probeCutoff_right (hi : D.parity i = 1) : probeCutoff D m i = 2 * m i := by
  simp [probeCutoff, probeDotExponent, hi]

include hdot in
/-- The rightward vacuum bubble entries of `vacuumRightwardCupInverse_bubbleEntries`,
restated on the tensor vacuum value: window length `N - 2M` and the tensor probe functor. -/
theorem tensorVacuum_rightward_odd_bubbleEntries [Fact Sc.PureNilpotent] (hi : D.parity i = 1)
    (hP : 0 < probeCutoff D m i)
    (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = tensorSectorInput D Sc m cutoff L ΛR ΛP hcP hcR)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z)
    (HN : (P).NegInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (cc : (P).CrossCoeff) :
    ∃ (c : _ ≅ V) (j : _ ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m
        (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H)
      (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V)),
      ProbeWindow.IsCupInverse (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H)
        (fun n => (adjunction K).unit.app V ≫
          (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ n.val)) j B ∧
      (∃ h, c.hom = eqToHom h) ∧
      (∀ (n : Fin (cutoff i - 2 * m i)) (N : ℕ),
        rightwardUnitColumn ((adjunction K).unit.app V)
          (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H) B N n =
        c.inv ≫ (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          ((P).etaEntry cc i N ν₀ (.nil _) q₀ Z ≫ dc n q₀ (.nil _)) ≫ c.hom) := by
  have hlen : (-D.h i ν₀).toNat = cutoff i - 2 * m i := by
    rw [SupportedSectors.vacuum_negative_window_length D Sc m cutoff bound ΛP ΛR hcP hcR i,
      odd_probeCutoff_right D m i hi]
  have hex := vacuumRightwardCupInverse_bubbleEntries D Sc m cutoff bound ΛP ΛR hcP hcR
    (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) hdot i Z hZ lc dc HN cc hP hi
  rw [show vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) = H from
    tensorOutputAt_empty D (parameterTwist D Sc) m cutoff L ΛR, hlen] at hex
  simp only [unitDotColumn_eq_restrictedDotEnd, Category.assoc] at hex
  exact hex

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end

section

/-! # Even moments of the rightward vacuum bubble entries

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

Even-colour analogue of `ELVTensorVacuumRightwardMoments`. At negative height of the
vacuum sector, leftward data satisfying the negative inverse equations (1.14) give an
entrywise inverse of the native cup window of the evaluated even A6 bend
(`vacuumRightwardCupInverse_even`, via `paddedVacuumDx_even`), whose products
with the native unit rows are the conjugated evaluated right bubble entries
`η xᴺ ≫ dcap n` (`vacuumRightwardCupInverse_bubbleEntries_even`). On the tensor
vacuum (`0 < M < N`, `M = m i`, `N = cutoff i`), the extreme column has the decoded
moments of `tensorVacuumNegativeCap_even_moments`: the coefficients of
`(1 - w)^M / E(-w)` (`tensorVacuum_rightward_even_moments`). No inverse, moment or
bubble value is assumed.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u

local instance rightwardEvenMomentsHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

section Native

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance rightwardEvenCupInverseZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (i : I)
local notation "q₀" => SPath.centralDnUp i (SKM.wt D ν₀ [SKM.up i]) ν₀ ((0, 0) : Sector I)
  ⟨false, trivial⟩

include hdot in
/-- **The rightward vacuum cup inverse in the native chart (even colour).** Leftward
data satisfying the negative inverse equations at the vacuum sector give an
entrywise inverse of the native cup window `[bend, unit ≫ xⁿ]_(n < -h)` of the
evaluated even A6 bend, `h = h_i(ν₀)`, whose columns are `vacuumRightwardColumn`. -/
theorem vacuumRightwardCupInverse_even [Fact Sc.PureNilpotent] (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z)
    (HN : (P).NegInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0) :
    ∃ j, ProbeWindow.IsCupInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (-D.h i ν₀).toNat =>
          unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
            (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
              (0 : Multiset I) i)
            ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
              (probeOldVacuumRegular D (parameterTwist D Sc) m)) n) j
        (fun n => vacuumRightwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i Z hZ dc n) := by
  subst hZ
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by
    simp [StepValid]
  have hd : ¬StepValid (SKM.dn i) true ((0, 0) : Sector I) := by
    simp [StepValid]
  have h₁ := (P).isCupInverse_centralPadded_of_negInverseAt
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀ ((0, 0) : Sector I)
    (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) lc dc HN hu hd
  have h₃ := (h₁.coordinates
    (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm
    (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm).target
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H)
  have hs : (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
      (P).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i
        ((0, 0) : Sector I) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
        (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) :=
    (Iso.inv_comp_eq _).2 (paddedVacuumDx_even D Sc m cutoff bound ΛP ΛR hcP hcR H i
      hdot hP hi)
  have hw : ∀ n : ℕ, (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).inv ≫
      (P).centralPaddedUnit i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) false n ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
        (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
          (0 : Multiset I) i)
        ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
          (probeOldVacuumRegular D (parameterTwist D Sc) m)) n := fun n =>
    (Iso.inv_comp_eq _).2 (paddedVacuumUnit_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i n)
  simp only [Iso.symm_hom, Iso.symm_inv] at h₃
  rw [hs] at h₃
  simp only [hw] at h₃
  exact ⟨_, h₃⟩

include hdot in
/-- **Rightward vacuum cup inverse with bubble-entry columns (even colour).** For
leftward data satisfying the negative inverse equations at an input equal to the
vacuum sector input, the native cup window of the evaluated even A6 bend has an
entrywise inverse whose products with the native unit rows `unit ≫ xᴺ` are the
evaluated right bubble entries `η xᴺ ≫ dcap n`, conjugated by one isomorphism `c`. -/
theorem vacuumRightwardCupInverse_bubbleEntries_even [Fact Sc.PureNilpotent] (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z)
    (HN : (P).NegInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (cc : (P).CrossCoeff) (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0) :
    ∃ (c : _ ≅ _) (j : _) (B : Fin (-D.h i ν₀).toNat → _),
      ProbeWindow.IsCupInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (-D.h i ν₀).toNat =>
          unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
            (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
              (0 : Multiset I) i)
            ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
              (probeOldVacuumRegular D (parameterTwist D Sc) m)) n) j B ∧
      (∃ h, c.hom = eqToHom h) ∧
      ∀ (n : Fin (-D.h i ν₀).toNat) (N : ℕ),
        unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
            (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
              (0 : Multiset I) i)
            ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
              (probeOldVacuumRegular D (parameterTwist D Sc) m)) N ≫ B n =
        c.inv ≫ (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          ((P).etaEntry cc i N ν₀ (.nil _) q₀ Z ≫ dc n q₀ (.nil _)) ≫ c.hom := by
  subst hZ
  obtain ⟨j, hj⟩ := vacuumRightwardCupInverse_even D Sc m cutoff bound ΛP ΛR hcP hcR H
    hdot i _ rfl lc dc HN hP hi
  exact ⟨paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H, j, _, hj,
    paddedVacuumCapTargetIso_hom_eq_eqToHom D Sc m cutoff bound ΛP ΛR hcP hcR H,
    fun n N => vacuumRightwardColumn_unit D Sc m cutoff bound ΛP ΛR hcP hcR H i cc dc n N⟩

end Native

end OddMath.QuiverHecke.ELV.WeightTensorVacuum

namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly ProbeVacuumCap PowerVacuumCoefficient
universe u

local instance rightwardEvenVacuumMomentsHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (i : I)
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff
  (PowerWordContent.powerBound D cutoff L))
local notation "ν₀" => (P).wt ((0, 0) : Sector I)
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D
  (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)
local notation "K" => contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i]
local notation "q₀" => SPath.centralDnUp i (SKM.wt D ν₀ [SKM.up i]) ν₀ ((0, 0) : Sector I)
  ⟨false, trivial⟩

omit [Fintype I] in
private theorem even_probeCutoff_right (hi : D.parity i = 0) : probeCutoff D m i = m i := by
  simp [probeCutoff, probeDotExponent, hi]

include hdot in
/-- The even rightward vacuum bubble entries of `vacuumRightwardCupInverse_bubbleEntries_even`,
restated on the tensor vacuum value: window length `N - M` and the tensor probe functor. -/
theorem tensorVacuum_rightward_even_bubbleEntries [Fact Sc.PureNilpotent] (hi : D.parity i = 0)
    (hP : 0 < probeCutoff D m i)
    (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = tensorSectorInput D Sc m cutoff L ΛR ΛP hcP hcR)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z)
    (HN : (P).NegInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (cc : (P).CrossCoeff) :
    ∃ (c : _ ≅ V) (j : _ ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m
        (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H)
      (B : Fin (cutoff i - m i) → (_ ⟶ V)),
      ProbeWindow.IsCupInverse (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H)
        (fun n => (adjunction K).unit.app V ≫
          (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ n.val)) j B ∧
      (∃ h, c.hom = eqToHom h) ∧
      (∀ (n : Fin (cutoff i - m i)) (N : ℕ),
        (adjunction K).unit.app V ≫
          (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ N) ≫ B n =
        c.inv ≫ (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          ((P).etaEntry cc i N ν₀ (.nil _) q₀ Z ≫ dc n q₀ (.nil _)) ≫ c.hom) := by
  have hlen : (-D.h i ν₀).toNat = cutoff i - m i := by
    rw [SupportedSectors.vacuum_negative_window_length D Sc m cutoff bound ΛP ΛR hcP hcR i,
      even_probeCutoff_right D m i hi]
  have hex := vacuumRightwardCupInverse_bubbleEntries_even D Sc m cutoff bound ΛP ΛR hcP hcR
    (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) hdot i Z
    hZ lc dc HN cc
    hP hi
  rw [show vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) = H from
    tensorOutputAt_empty D (parameterTwist D Sc) m cutoff L ΛR, hlen] at hex
  simp only [unitDotColumn_eq_restrictedDotEnd, Category.assoc] at hex
  exact hex

include hdot in
/-- The decoded moments of the extreme column of an entrywise inverse of the native cup
window of the tensor vacuum bend, at an even colour with `0 < M < N`. -/
theorem tensorVacuum_rightward_even_extreme_moments (hi : D.parity i = 0)
    (hP : 0 < probeCutoff D m i) (hPN : m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m
        (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H)
    (B : Fin (cutoff i - m i) → (_ ⟶ V))
    (hB : ProbeWindow.IsCupInverse
      (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫
        (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ n.val)) j B)
    (l : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
        (((adjunction K).unit.app V ≫
          (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^
            (cutoff i - m i - 1 + l)) ≫
            B ⟨cutoff i - m i - 1, by omega⟩).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff l
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z :=
  tensorVacuumNegativeCap_even_moments D (parameterTwist D Sc) m cutoff L
    hdot i hi hP (by omega) hPN j B hB l z

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end
