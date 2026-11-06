/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumMomentMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumCap
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCentralSlide
import OddMath.QuiverHecke.SwappedVacuum.NegativeCapMoments
import Mathlib.Algebra.Polynomial.Expand
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCentralSlide
import OddMath.QuiverHecke.SwappedVacuum.NegativeCapMoments
import Mathlib.Algebra.Polynomial.Expand
import OddMath.QuiverHecke.SwappedVacuum.InverseColumnOddSeries
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.CapWindows

/-! # Column moments of a positive-height inverse on the tensor vacuum

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8 (the left-bubble series of `AdjunctionBubbleSeries.left_odd`).

On the prescribed tensor vacuum at an odd colour, take any column
`a : V ⟶ X` of positive height `h` against the actual A6 bend: `a` is killed
by the bend and `a ≫ x^j ≫ v = δ_(j,h-1)` for `j < h`, where `x` is the
shifted pre dot and `v` the shifted pre cap. With the actual mate slide
(`q = -1`), the probe `(x² + 1)^m`, the reservoir window and the reservoir
moments `tensorPowerVacuumCap_moment_even/odd`, the decoded column moments
are the coefficients of the substituted series of `left_odd`
(`tensorVacuumColumn_odd_moments`): the moment `a ≫ x^(h-1+2s) ≫ v` acts
on the coefficient chart as left multiplication by the `s`-th coefficient
of `C(-w)(1 + w)^(-m)`, and `a ≫ x^(h+2s) ≫ v` by `±δ` times it.

The identity is transported from `End V` to linear operators on the
coefficient quotient by evaluating at the vacuum point and conjugating with
the decode chart (`tensorVacuumEndDecode`). No bubble value, inverse row or
factor action is assumed; the column is arbitrary subject to its defining
window. See `docs/Nondegeneracy/InverseColumnMoments.md`.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient ProbeVacuumCap
open Finset
universe u

section Generic

variable {I' X' k' : Type u} [AddCommGroup X'] [CommRing k'] {C : Type*} [Category C]
  [Preadditive C] [Linear k' C] {Xo Yo V' : C}

/-- The odd inverse-column moment identity for an arbitrary column `a`, read through
an algebra map `ρ` on `End V'`: with the mate slide at `q = -1`, the odd probe, the
two windows and the reservoir series `T(z) = A(z²)(1 + e z)`, the column moments are
the substituted-series coefficients. -/
theorem column_moments_of_slide (D : SKM.Datum I' X') {R : Type*} [Ring R] [Algebra k' R]
    (φ : MvPolynomial (I' × ℕ) k' →ₐ[k'] R) (ρ : End V' →ₐ[k'] R) (P : I' → ℕ) (i : I')
    (hi : D.parity i = 1) (h N : ℕ) (hh : 0 < h) (hN : 0 < N) (hhN : h + N = 2 * P i)
    (e : R) (he : e * e = 0) (x : End Xo) (y : End Yo) (s : Xo ⟶ Yo) (u : V' ⟶ Yo)
    (v : Xo ⟶ V') (ell : Yo ⟶ V') (a : V' ⟶ Xo)
    (hslide : s ≫ y - (-1 : k') • (x ≫ s) = v ≫ u) (has : a ≫ s = 0)
    (hprobe : SwappedVacuum.capPolynomial
      (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k') ^ P i).coeff n) (h + N) x = 0)
    (hcol : ∀ j < h, a ≫ (x ^ j) ≫ v = if j + 1 = h then 𝟙 V' else 0)
    (hwin : ∀ j < N, u ≫ (y ^ j) ≫ ell = if j + 1 = N then 𝟙 V' else 0)
    (hT : PowerSeries.mk (fun l => ρ (u ≫ (y ^ (N - 1 + l)) ≫ ell)) =
      PowerSeries.map φ.toRingHom (PowerSeries.expand 2 two_ne_zero
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k' i)) 1)) *
        (1 + PowerSeries.C e * PowerSeries.X))
    (n : ℕ) :
    ρ (a ≫ (x ^ (h - 1 + 2 * n)) ≫ v) = φ (PowerSeries.coeff n
        (VacuumSeries.substitutedSeries k' (SKM.SYM.probeSeries D k' P) i)) ∧
      ρ (a ≫ (x ^ (h + 2 * n)) ≫ v) = e * φ (PowerSeries.coeff n
        (VacuumSeries.substitutedSeries k' (SKM.SYM.probeSeries D k' P) i)) := by
  refine SwappedVacuum.odd_inverse_column_moments D φ P i hi h N hh hN hhN e he
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
    have h0 := congrArg ρ (SwappedVacuum.column_reservoir_relation (-1 : k') (by norm_num)
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

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1

variable (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound)

local notation "W₀" => Functor.obj (restriction (contentInclusion D Sc cutoff bound (0 : Multiset I)))
  (weightedVacuum D Sc cutoff L)
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound W₀
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m
local notation "V" => Superfunctor.obj H N₀
local notation "star" => (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff bound 0)
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L

/-- The decode chart of the tensor vacuum value, with its input chart as inverse. -/
def tensorVacuumDecodeEquiv : (V).obj star ≃ₗ[k] AQ :=
  LinearEquiv.ofLinearMap (tensorVacuumDecodeLinear D Sc m cutoff L)
    (tensorVacuumInputLinear D Sc m cutoff L)
    (LinearMap.ext (tensorVacuumDecode_input D Sc m cutoff L))
    (LinearMap.ext (tensorVacuumInput_decode D Sc m cutoff L))

/-- Endomorphisms of the tensor vacuum value, evaluated at the vacuum point
and read in the decode chart. -/
def tensorVacuumEndDecode : End V →ₐ[k] Module.End k AQ :=
  ((tensorVacuumDecodeEquiv D Sc m cutoff L).conjAlgEquiv k).toAlgHom.comp
    ((svecEndEvaluation ((V).obj star)).comp (supernaturalEndEvaluation V star))

theorem tensorVacuumEndDecode_apply (f : End V) (z : (V).obj star) :
    tensorVacuumEndDecode D Sc m cutoff L f (tensorVacuumDecodeLinear D Sc m cutoff L z) =
      tensorVacuumDecodeLinear D Sc m cutoff L (f.total star z) := by
  change tensorVacuumDecodeLinear D Sc m cutoff L (f.total star
    (tensorVacuumInputLinear D Sc m cutoff L (tensorVacuumDecodeLinear D Sc m cutoff L z))) = _
  rw [tensorVacuumInput_decode]

variable (i : I)
local notation "K" => contentAppend D Sc cutoff bound (0 : Multiset I) [i]

/-- An endomorphism whose evaluation at the vacuum point is read in the decode
chart as `g` decodes to `g`. -/
theorem tensorVacuumEndDecode_eq_of (f : End V) (g : Module.End k AQ)
    (hfg : ∀ z, tensorVacuumDecodeLinear D Sc m cutoff L (f.total star z) =
      g (tensorVacuumDecodeLinear D Sc m cutoff L z)) :
    tensorVacuumEndDecode D Sc m cutoff L f = g := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨z, rfl⟩ := (tensorVacuumDecodeEquiv D Sc m cutoff L).surjective w
  exact (tensorVacuumEndDecode_apply D Sc m cutoff L f z).trans (hfg z)

/-- Left multiplication by the polynomial coefficients on the coefficient quotient. -/
private def coefficientLmul : MvPolynomial (I × ℕ) k →ₐ[k] Module.End k AQ :=
  (Algebra.lmul k AQ).comp (polynomialToPower D cutoff L)

omit [Fintype I] in
private theorem coefficientLmul_apply (p : MvPolynomial (I × ℕ) k) (w : AQ) :
    coefficientLmul D cutoff L p w = polynomialToPower D cutoff L p * w := rfl

omit [Fintype I] in
private theorem coefficientLmul_ringHom_apply (p : MvPolynomial (I × ℕ) k) (w : AQ) :
    (coefficientLmul D cutoff L).toRingHom p w = polynomialToPower D cutoff L p * w := rfl

omit [Fintype I] in
private theorem lmul_apply' (a w : AQ) : Algebra.lmul k AQ a w = a * w := rfl

omit [Fintype I] in
private theorem end_mul_apply' (f g : Module.End k AQ) (w : AQ) : (f * g) w = f (g w) := rfl

private theorem unit_cap_closure (hN : 0 < cutoff i) (n : ℕ) :
    (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN = tensorUnitCapClosure D Sc m cutoff L i hN n := by
  rw [tensorUnitCapClosure, unitDotColumn_eq_restrictedDotEnd, Category.assoc]
  rfl

omit [Fintype I] in
private theorem odd_coefficient_commute (hi : D.parity i = 1) (p : MvPolynomial (I × ℕ) k) :
    Commute (polynomialToPower D cutoff L p) ((-1 : k) ^ (cutoff i + 1) •
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) :=
  (((SKM.SYM.polynomialInclude_commute D k p (SKM.SYM.delta D k ⟨i, hi⟩)).map
    (coefficientPowerQuotientMap D cutoff L)).smul_right _)

private theorem reservoir_even_coefficient (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + 2 * r)) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN) =
      (coefficientLmul D cutoff L).toRingHom (PowerSeries.coeff r
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) := by
  refine tensorVacuumEndDecode_eq_of D Sc m cutoff L _ _ fun z => ?_
  rw [unit_cap_closure D Sc m cutoff L i hN, coefficientLmul_ringHom_apply]
  have hm := tensorPowerVacuumCap_moment_even D Sc m cutoff L i hi hN r z
  show _ = completeCoefficient D cutoff L i r * _
  convert hm using 3

private theorem reservoir_odd_coefficient (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫
          (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + (2 * r + 1))) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN) =
      (coefficientLmul D cutoff L).toRingHom (PowerSeries.coeff r
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) *
        Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) := by
  refine tensorVacuumEndDecode_eq_of D Sc m cutoff L _ _ fun z => ?_
  rw [unit_cap_closure D Sc m cutoff L i hN, end_mul_apply', lmul_apply',
    coefficientLmul_ringHom_apply, ← mul_assoc, (odd_coefficient_commute D cutoff L i hi _).eq,
    smul_mul_assoc]
  convert tensorPowerVacuumCap_moment_odd D Sc m cutoff L i hi hN r z using 3
  rfl

private theorem tensorVacuum_reservoir_series (hi : D.parity i = 1) (hN : 0 < cutoff i) :
    PowerSeries.mk (fun l => tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + l)) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN)) =
      PowerSeries.map (coefficientLmul D cutoff L).toRingHom (PowerSeries.expand 2 two_ne_zero
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) *
        (1 + PowerSeries.C (Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩))) * PowerSeries.X) :=
  SwappedVacuum.mk_eq_expand_mul_one_add (coefficientLmul D cutoff L).toRingHom _ _ _
    (reservoir_even_coefficient D Sc m cutoff L i hi hN)
    (reservoir_odd_coefficient D Sc m cutoff L i hi hN)

set_option diagnostics true in
include hdot in
private theorem odd_slide_neg (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫ evaluatedPostDot D Sc m cutoff bound i H -
      (-1 : k) • (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V := by
  have hs := evaluatedMixedBend_odd_slideOf D Sc m cutoff bound hdot i hi hP H
  simpa only [hi, koszulSign_one_one, neg_one_zsmul, neg_one_smul] using hs

private theorem odd_probe_polynomial (hi : D.parity i = 1) (h : ℕ) (hhN : h + cutoff i = 2 * m i) :
    SwappedVacuum.capPolynomial
      (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff n) (h + cutoff i)
      (shiftedPreDot D Sc m R₀ i H) = 0 := by
  rw [hhN]
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

omit [Fintype I] in
private theorem odd_coefficient_sq (hi : D.parity i = 1) :
    Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
        coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
      Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
        coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) = 0 := by
  have h2 := SKM.SYM.delta_sq D k ⟨i, hi⟩
  rw [pow_two] at h2
  rw [← map_mul, smul_mul_smul_comm, ← map_mul, h2, map_zero, smul_zero, map_zero]

include hdot in
/-- **Odd-colour column moments on the tensor vacuum.** For a column `a`
killed by the actual A6 bend with the column window of height `h`, where
`h + cutoff i = 2 m i`, the decoded column moments are the coefficients of
the substituted series of `AdjunctionBubbleSeries.left_odd`; the odd moments
carry the normalized odd coefficient `(-1)^(cutoff i + 1) δ`. -/
theorem tensorVacuumColumn_odd_moments
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (h : ℕ) (hh : 0 < h) (hhN : h + cutoff i = 2 * m i)
    (a : V ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (has : a ≫ evaluatedMixedBend D Sc m cutoff bound i hP H = 0)
    (hcol : ∀ j < h, a ≫ (shiftedPreDot D Sc m R₀ i H ^ j) ≫ shiftedPreCap D Sc m R₀ i hP H =
      if j + 1 = h then 𝟙 V else 0)
    (s : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((a ≫ (shiftedPreDot D Sc m R₀ i H ^ (h - 1 + 2 * s)) ≫
          shiftedPreCap D Sc m R₀ i hP H).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z ∧
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((a ≫ (shiftedPreDot D Sc m R₀ i H ^ (h + 2 * s)) ≫
          shiftedPreCap D Sc m R₀ i hP H).total star z) =
      ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        (polynomialToPower D cutoff L (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z) := by
  have hwin : ∀ j < cutoff i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ j) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if j + 1 = cutoff i then 𝟙 V else 0 :=
    fun j hj => tensorPowerVacuumCap_window D Sc m cutoff L i hN j hj
  have hmom := column_moments_of_slide D (coefficientLmul D cutoff L)
    (tensorVacuumEndDecode D Sc m cutoff L) m i hi h (cutoff i) hh hN hhN
    _ (odd_coefficient_sq D cutoff L i hi) (shiftedPreDot D Sc m R₀ i H)
    (evaluatedPostDot D Sc m cutoff bound i H) (evaluatedMixedBend D Sc m cutoff bound i hP H)
    ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H)
    (tensorPowerVacuumCap D Sc m cutoff L i hN) a
    (odd_slide_neg D Sc m cutoff L hdot i hi hP) has
    (odd_probe_polynomial D Sc m cutoff L i hi h hhN) hcol hwin
    (tensorVacuum_reservoir_series D Sc m cutoff L i hi hN) s
  constructor
  · have e1 := tensorVacuumEndDecode_apply D Sc m cutoff L
      (a ≫ (shiftedPreDot D Sc m R₀ i H ^ (h - 1 + 2 * s)) ≫ shiftedPreCap D Sc m R₀ i hP H) z
    rw [hmom.1, coefficientLmul_apply] at e1
    exact e1.symm
  · have e2 := tensorVacuumEndDecode_apply D Sc m cutoff L
      (a ≫ (shiftedPreDot D Sc m R₀ i H ^ (h + 2 * s)) ≫ shiftedPreCap D Sc m R₀ i hP H) z
    rw [hmom.2, end_mul_apply', lmul_apply', coefficientLmul_apply] at e2
    exact e2.symm

include hdot in
/-- **Chosen inverse column.** If the cap window `[bend; x^n ≫ v]_(n < h)` of the actual A6
bend has an entrywise inverse `(j, A)` (`IsCapInverse`), its last padded column `A (h - 1)`
has the substituted-series moments of `tensorVacuumColumn_odd_moments`. -/
theorem tensorVacuumCapInverse_odd_moments
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (h : ℕ) (hh : 0 < h) (hhN : h + cutoff i = 2 * m i)
    (jY : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (A : Fin h → (V ⟶ shiftedPreSourceObject D Sc m R₀ i H))
    (hA : SwappedAssembly.ProbeWindow.IsCapInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n : Fin h => (shiftedPreDot D Sc m R₀ i H ^ (n : ℕ)) ≫ shiftedPreCap D Sc m R₀ i hP H)
      jY A)
    (s : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((A ⟨h - 1, by omega⟩ ≫ (shiftedPreDot D Sc m R₀ i H ^ (h - 1 + 2 * s)) ≫
          shiftedPreCap D Sc m R₀ i hP H).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z ∧
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((A ⟨h - 1, by omega⟩ ≫ (shiftedPreDot D Sc m R₀ i H ^ (h + 2 * s)) ≫
          shiftedPreCap D Sc m R₀ i hP H).total star z) =
      ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        (polynomialToPower D cutoff L (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
          tensorVacuumDecodeLinear D Sc m cutoff L z) :=
  by
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
  exact tensorVacuumColumn_odd_moments D Sc m cutoff L hdot i hi hP hN h hh hhN
    (A ⟨h - 1, by omega⟩) (hA.2.1 _) hcol s z

end OddMath.QuiverHecke.ELVOld
