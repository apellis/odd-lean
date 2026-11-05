/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumEntryLift
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumDecodeFaithful
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumCoefficientDecode
import OddMath.QuiverHecke.SwappedAssembly.SupportedPointwiseLeftwardInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumRightwardMoments
import OddMath.QuiverHecke.SwappedVacuumAdjunctionBubbles

/-! # Vacuum entries of the odd right bubbles at negative height

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8
(the bubble relations of Definition 8.1 at the vacuum sector).

For an odd colour `i` with `0 < 2 M < N` (`M = m i`, `N = cutoff i`), so that the
vacuum height `h = 2 M - N` is negative, the vacuum entries of the closed diagrams
`η x^(2s - h - 1) ≫ dcap (-h - 1)` and `η x^(1 - h - 1) ≫ dcap (-h - 1)` of the tensor
target family are the coefficient actions of the `s`-th coefficient of
`(1 + w)^M / C(-w)` (`vacuumEntry_neg_odd`) and of `(-1)^(N+1) δ_i`
(`vacuumEntry_odd_neg`). These are the fields `neg_odd` and `odd_neg` of
`VacuumRightEntries`.

The proof reads the entries on the tensor vacuum value through the cup inverse of
`tensorVacuum_rightward_odd_moments`, whose extreme column has the required decoded
moments, and lifts the decoded equality with `vacuumEntry_of_decode`; faithfulness of
the decoded reading is `vacuumDecodeFaithful_tensorTarget`, and the decoded value of the
coefficient action is `vacuumDecode_tensorTargetCoefficient`.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld ELVOld.PowerVacuumCoefficient ELVOld.WeightTensorVacuum
universe u
local instance supportedVacuumRightOddHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (sy : Symmetrizer D) (hc : Sc.Homogeneous)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "E" => vacuumSectorEvaluation D Sc m cutoff N ΛP ΛR hP hR
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff N
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff N (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "ν₀" => (P).wt ((0, 0) : Sector I)
local notation "Ys" => tensorTargetFamily D Sc m cutoff ΛP ΛR L
local notation "cc" => elvProbeCrossCoeff D Sc m cutoff N ΛP ΛR hP hR sy hc
local notation "lw" => pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR sy hc

/-- The decoded value of the coefficient action at the vacuum object of the tensor target
family is left multiplication, for every comparison with the tensor vacuum value that is
an `eqToHom`. -/
def VacuumCoefficientDecode : Prop :=
  ∀ (c : (E).obj (Ys (0,0)).obj ≅ V), (∃ h, c.hom = eqToHom h) → ∀ (a : SYM D k),
    vacuumDecode D Sc m cutoff ΛP ΛR L hP hR _ c
      (tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR (0,0) a).hom =
    LinearMap.mulLeft k (coefficientPowerQuotientMap D cutoff L a)

/-- The decoded coefficient action holds: every `eqToHom` comparison reads the
coefficient action of `a` as left multiplication by the class of `a`. -/
theorem vacuumCoefficientDecode_holds : VacuumCoefficientDecode D Sc m cutoff ΛP ΛR L hP hR :=
  fun c hc a => vacuumDecode_tensorTargetCoefficient D Sc m cutoff ΛP ΛR L hP hR c hc a

omit [Fintype I] in
private theorem odd_probeCutoff_eq (i : I) (hi : D.parity i = 1) :
    probeCutoff D m i = 2 * m i := by
  simp [probeCutoff, probeDotExponent, hi]

include sy hc in
/-- The vacuum entry of `η x^e ≫ dcap n` at the shifts read off the extreme moment column,
for an odd colour at negative height: `e = N - 2M - 1 + 2s` gives the `s`-th moment and
`e = N - 2M - 1 + 1` the normalized odd coefficient. -/
private theorem vacuumEntry_odd_shift (hcoef : VacuumCoefficientDecode D Sc m cutoff ΛP ΛR L hP hR)
    (i : I) (hi : D.parity i = 1) (hP0 : 0 < probeCutoff D m i)
    (hh : D.h i ν₀ < 0) (hPN : 2 * m i < cutoff i) (e n : ℕ) (hn : n = cutoff i - 2 * m i - 1)
    (a : SYM D k)
    (hmom : ∀ (_c : (E).obj (Ys (0,0)).obj ≅ V) (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
      (z : (V).obj (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff N 0)),
      (∀ (r : ℕ) (z : (V).obj (⟨⟨[]⟩, rfl⟩ :
          ContentCategory D (parameterTwist D Sc) cutoff N 0)),
        (∀ e', e' = cutoff i - 2 * m i - 1 + 2 * r →
          ELVOld.rightwardLastColumnDecode D (parameterTwist D Sc) m cutoff L i hPN B e' z =
          polynomialToPower D cutoff L (PowerSeries.coeff r
              (VacuumSeries.momentSeries k (SYM.probeSeriesInv D k m) i)) *
            tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z) ∧
        ∀ e', e' = cutoff i - 2 * m i - 1 + (2 * r + 1) →
          ELVOld.rightwardLastColumnDecode D (parameterTwist D Sc) m cutoff L i hPN B e' z =
          ELVOld.rightwardOddScalar D cutoff L i hi *
            (polynomialToPower D cutoff L (PowerSeries.coeff r
              (VacuumSeries.momentSeries k (SYM.probeSeriesInv D k m) i)) *
              tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z)) →
      ELVOld.rightwardLastColumnDecode D (parameterTwist D Sc) m cutoff L i hPN B e z =
        coefficientPowerQuotientMap D cutoff L a *
          tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z) :
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀
      (etaL i e ++ dcapL i n) ((sChain_etaL i _).append (sChain_dcapL i _)) a := by
  have hhe := vacuum_height_eq D Sc m cutoff N ΛP ΛR hP hR i
  rw [odd_probeCutoff_eq D m i hi] at hhe hP0
  have hnZ : (n : ℤ) < -D.h i ν₀ := by rw [hhe, hn]; omega
  have hd : ¬StepValid (dn i) true ((0, 0) : Sector I) := by simp [StepValid]
  have hPi : 0 < probeCutoff D m i := by rw [odd_probeCutoff_eq D m i hi]; omega
  obtain ⟨c, j, B, hB, hceq, hcup⟩ := tensorVacuum_rightward_odd_bubbleEntries D Sc m cutoff L
    ΛP ΛR hP hR i
      (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
        (parameterTwist_homogeneous D Sc hc) _) hi hPi (Ys (0,0)).obj
    ((congrArg (fun Y => Y.obj) (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L)).trans
      (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hP hR).symm)
    (fun q p => (lw).lcrossSame i ν₀ q p (Ys (0,0)).obj)
    (fun n q r => (lw).dcap i n ν₀ q r (Ys (0,0)).obj)
    (centralPointwiseLeftward_negInverseAt D Sc m cutoff N ΛP ΛR hP hR sy hc i (0,0)
      (Ys (0,0)) hh) cc
  apply vacuumEntry_of_decode D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀ _ _ a c
    (vacuumDecodeFaithful_tensorTarget D Sc m cutoff ΛP ΛR L hP hR c) (hcoef c hceq a)
  intro z
  rw [ProbeReservoir.compDiag_etaL_dcapL_swappedGens (P) cc lw i e n ν₀ hnZ (0,0) _ hd]
  subst hn
  rw [← hcup ⟨cutoff i - 2 * m i - 1, by omega⟩ e]
  exact hmom c B z fun r z =>
    ⟨fun e' he' => ELVOld.rightwardLastColumnDecode_even D (parameterTwist D Sc) m cutoff L sy
      (parameterTwist_homogeneous D Sc hc) i hi hPi hPN j B hB r e' he' z,
     fun e' he' => ELVOld.rightwardLastColumnDecode_odd D (parameterTwist D Sc) m cutoff L sy
      (parameterTwist_homogeneous D Sc hc) i hi hPi hPN j B hB r e' he' z⟩

include sy hc in
/-- **Odd right bubbles at negative height, moments.** For an odd colour `i` with
`0 < probeCutoff` and negative vacuum height `h`, the vacuum entry of
`η x^(2s - h - 1) ≫ dcap (-h - 1)` of the tensor target family is the coefficient action
of the `s`-th coefficient of `(1 + w)^M / C(-w)`. -/
theorem vacuumEntry_neg_odd (i : I) (hi : D.parity i = 1) (hP0 : 0 < probeCutoff D m i)
    (hh : D.h i ν₀ < 0) (s : ℕ) :
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀
      (etaL i (((2 * s : ℕ) : ℤ) - D.h i ν₀ - 1).toNat ++ dcapL i (-D.h i ν₀ - 1).toNat)
      ((sChain_etaL i _).append (sChain_dcapL i _))
      (SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SYM.probeSeriesInv D k m) i))) := by
  have hhe := vacuum_height_eq D Sc m cutoff N ΛP ΛR hP hR i
  rw [odd_probeCutoff_eq D m i hi] at hhe
  have he : (((2 * s : ℕ) : ℤ) - D.h i ν₀ - 1).toNat = cutoff i - 2 * m i - 1 + 2 * s := by
    rw [hhe]; omega
  rw [he]
  refine vacuumEntry_odd_shift D Sc m cutoff ΛP ΛR L hP hR sy hc
    (vacuumCoefficientDecode_holds D Sc m cutoff ΛP ΛR L hP hR) i hi hP0 hh
    (by rw [hhe] at hh; omega) _ _
    (by rw [hhe]; omega) _ (fun c B z hm => (hm s z).1 _ rfl)

include sy hc in
/-- **Odd right bubbles at negative height, odd coefficient.** For an odd colour `i` with
`0 < probeCutoff` and negative vacuum height `h`, the vacuum entry of
`η x^(1 - h - 1) ≫ dcap (-h - 1)` of the tensor target family is the coefficient action
of `σ δ_i`, for any sign `σ = probeSign N' i` equal to `(-1)^(cutoff i + 1)`. -/
theorem vacuumEntry_odd_neg (N' : I → ℕ) (i : {i : I // D.parity i = 1})
    (hP0 : 0 < probeCutoff D m i.1)
    (hh : D.h i.1 ν₀ < 0) (hN' : SYM.probeSign D k N' i = (-1) ^ (cutoff i.1 + 1)) :
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀
      (etaL i.1 (((1 : ℕ) : ℤ) - D.h i.1 ν₀ - 1).toNat ++ dcapL i.1 (-D.h i.1 ν₀ - 1).toNat)
      ((sChain_etaL i.1 _).append (sChain_dcapL i.1 _))
      (SYM.probeSign D k N' i • SYM.delta D k i) := by
  have hhe := vacuum_height_eq D Sc m cutoff N ΛP ΛR hP hR i.1
  rw [odd_probeCutoff_eq D m i.1 i.2] at hhe
  have he : (((1 : ℕ) : ℤ) - D.h i.1 ν₀ - 1).toNat = cutoff i.1 - 2 * m i.1 - 1 + (2 * 0 + 1) := by
    rw [hhe]; omega
  rw [he]
  refine vacuumEntry_odd_shift D Sc m cutoff ΛP ΛR L hP hR sy hc
    (vacuumCoefficientDecode_holds D Sc m cutoff ΛP ΛR L hP hR) i.1 i.2 hP0 hh
    (by rw [hhe] at hh; omega) _ _
    (by rw [hhe]; omega) _ (fun c B z hm => ?_)
  rw [(hm 0 z).2 _ rfl, AdjunctionBubbleSeries.coeff_zero_momentSeries, map_one, one_mul,
    ELVOld.rightwardOddScalar_eq, hN']

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
