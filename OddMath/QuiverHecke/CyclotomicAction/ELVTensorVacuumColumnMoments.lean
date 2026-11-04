/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumMomentMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumPrincipalCap
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

/-- The decode chart of the tensor vacuum value, with its input chart as inverse. -/
def tensorVacuumDecodeEquiv : (V).obj star ≃ₗ[k] AQ :=
  LinearEquiv.ofLinear (tensorVacuumDecodeLinear D Sc m cutoff L)
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

/-- Left multiplication by the polynomial coefficients on the coefficient quotient. -/
private def coefficientLmul : MvPolynomial (I × ℕ) k →ₐ[k] Module.End k AQ :=
  (Algebra.lmul k AQ).comp (polynomialToPower D cutoff L)

private theorem unit_cap_closure (hN : 0 < cutoff i) (hP : 0 < probeCutoff D m i) (n : ℕ) :
    (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN = tensorUnitCapClosure D Sc m cutoff L i hN n := by
  rw [tensorUnitCapClosure, unitDotColumn_eq_restrictedDotEnd, Category.assoc]
  rfl

include sy hc in
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
  set ρ := tensorVacuumEndDecode D Sc m cutoff L
  set c : ℕ → k := fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff n
  set δq : AQ := (-1 : k) ^ (cutoff i + 1) •
    coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)
  set dz := tensorVacuumDecodeLinear D Sc m cutoff L z
  have hs := evaluatedMixedBend_odd_slide D Sc m cutoff bound sy hc i hi hP H
  have hs' : evaluatedMixedBend D Sc m cutoff bound i hP H ≫
        evaluatedPostDot D Sc m cutoff bound i H -
      (-1 : k) • (shiftedPreDot D Sc m R₀ i H ≫
        evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V := by
    simpa only [hi, koszulSign_one_one, neg_one_zsmul, neg_one_smul] using hs
  have hp : SwappedVacuum.capPolynomial c (h + cutoff i) (shiftedPreDot D Sc m R₀ i H) = 0 := by
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
  have hdelta : δq * δq = 0 := by
    have h2 := SKM.SYM.delta_sq D k ⟨i, hi⟩
    rw [pow_two] at h2
    rw [smul_mul_smul_comm, ← map_mul, h2, map_zero, smul_zero]
  have hcomm (p : MvPolynomial (I × ℕ) k) : Commute (polynomialToPower D cutoff L p) δq :=
    (((SKM.SYM.polynomialInclude_commute D k p (SKM.SYM.delta D k ⟨i, hi⟩)).map
      (coefficientPowerQuotientMap D cutoff L)).smul_right _)
  obtain ⟨h1, h2⟩ := SwappedVacuum.odd_inverse_column_moments D
    (coefficientLmul D cutoff L) m i hi h (cutoff i) hh hN hhN (Algebra.lmul k AQ δq)
    (by rw [← map_mul, hdelta, map_zero])
    (fun j => ρ (a ≫ (shiftedPreDot D Sc m R₀ i H ^ j) ≫ shiftedPreCap D Sc m R₀ i hP H))
    (fun j => ρ ((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ j) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN))
    (fun j hj => by
      simp only
      rw [hcol j hj]
      split_ifs
      exacts [map_one ρ, map_zero ρ])
    (fun j hj => by
      simp only
      rw [show (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ j) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN = if j + 1 = cutoff i then 𝟙 V else 0 from
        tensorPowerVacuumCap_window D Sc m cutoff L i hN j hj]
      split_ifs
      exacts [map_one ρ, map_zero ρ])
    (fun d => by
      have h0 := congrArg ρ (SwappedVacuum.column_reservoir_relation (-1 : k) (by norm_num)
        (shiftedPreDot D Sc m R₀ i H) (evaluatedPostDot D Sc m cutoff bound i H)
        (evaluatedMixedBend D Sc m cutoff bound i hP H) ((adjunction K).unit.app V)
        (shiftedPreCap D Sc m R₀ i hP H) (tensorPowerVacuumCap D Sc m cutoff L i hN) a
        (h + cutoff i) c hs' has hp d)
      rw [map_zero, map_sum] at h0
      rw [← h0]
      refine sum_congr rfl fun n _ => ?_
      rw [map_smul, map_sum]
      refine congrArg _ (sum_congr rfl fun j _ => ?_)
      rw [map_smul, ← map_mul]
      rfl)
    (fun mm => by
      have h0 := congrArg ρ (SwappedVacuum.column_probe_relation (shiftedPreDot D Sc m R₀ i H)
        (shiftedPreCap D Sc m R₀ i hP H) a (h + cutoff i) c hp mm)
      rw [map_zero, map_sum] at h0
      simpa only [map_smul] using h0)
    (SwappedVacuum.mk_eq_expand_mul_one_add (coefficientLmul D cutoff L).toRingHom _ _ _
      (fun r => by
        ext1 w
        obtain ⟨z, rfl⟩ := (tensorVacuumDecodeEquiv D Sc m cutoff L).surjective w
        change ρ _ (tensorVacuumDecodeLinear D Sc m cutoff L z) = _
        rw [unit_cap_closure D Sc m cutoff L i hN hP, tensorVacuumEndDecode_apply,
          tensorPowerVacuumCap_moment_even D Sc m cutoff L i hi hN r z]
        rfl)
      (fun r => by
        ext1 w
        obtain ⟨z, rfl⟩ := (tensorVacuumDecodeEquiv D Sc m cutoff L).surjective w
        change ρ _ (tensorVacuumDecodeLinear D Sc m cutoff L z) = _
        rw [unit_cap_closure D Sc m cutoff L i hN hP, tensorVacuumEndDecode_apply,
          tensorPowerVacuumCap_moment_odd D Sc m cutoff L i hi hN r z]
        change _ = polynomialToPower D cutoff L _ * (δq * tensorVacuumDecodeLinear D Sc m cutoff L z)
        rw [← mul_assoc, (hcomm _).eq]
        simp only [δq, smul_mul_assoc]
        rfl))
    s
  constructor
  · have h3 := congrArg (fun f : Module.End k AQ => f dz) h1
    simp only [ρ, dz, tensorVacuumEndDecode_apply] at h3
    exact h3
  · have h3 := congrArg (fun f : Module.End k AQ => f dz) h2
    simp only [ρ, dz, tensorVacuumEndDecode_apply] at h3
    exact h3

include sy hc in
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
  tensorVacuumColumn_odd_moments D Sc m cutoff L sy hc i hi hP hN h hh hhN _ (hA.2.1 _)
    (fun j hj => by
      have := hA.2.2.2.1 ⟨h - 1, by omega⟩ ⟨j, hj⟩
      rw [this]
      exact if_congr (by simp only [Fin.ext_iff]; omega) rfl rfl) s z

end OddMath.QuiverHecke.ELVOld
