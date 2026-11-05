/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumEntryLift
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumDecodeFaithful
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumCoefficientDecode
import OddMath.QuiverHecke.SwappedAssembly.SupportedPointwiseLeftwardInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumRightwardEvenMoments
import OddMath.QuiverHecke.SwappedVacuumAdjunctionBubbles

/-! # Vacuum entries of the even right bubbles at negative height

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8
(the bubble relations of Definition 8.1 at the vacuum sector).

For an even colour `i` with `0 < M < N` (`M = m i`, `N = cutoff i`), so that the vacuum
height `h = M - N` is negative, the vacuum entry of the closed diagram
`η x^(s - h - 1) ≫ dcap (-h - 1)` of the tensor target family is the coefficient action of
the `s`-th coefficient of `(1 - w)^M / E(-w)` (`vacuumEntry_neg_even`). This is the field
`neg_even` of `VacuumRightNegativeEntries`.

The proof reads the entry on the tensor vacuum value through the cup inverse of
`tensorVacuum_rightward_even_bubbleEntries`, whose extreme column has the decoded moments of
`tensorVacuum_rightward_even_extreme_moments`, and lifts the decoded equality with
`vacuumEntry_of_decode`; faithfulness of the decoded reading is
`vacuumDecodeFaithful_tensorTarget`, and the decoded value of the coefficient action is
`vacuumDecode_tensorTargetCoefficient`.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld ELVOld.PowerVacuumCoefficient ELVOld.WeightTensorVacuum
universe u
local instance supportedVacuumRightEvenHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (sy : Symmetrizer D) (hc : Sc.Homogeneous)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)
local notation "Ys" => tensorTargetFamily D Sc m cutoff ΛP ΛR L
local notation "cc" => elvProbeCrossCoeff D Sc m cutoff N ΛP ΛR hP hR sy hc
local notation "lw" => pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR sy hc

omit [Fintype I] in
private theorem even_probeCutoff_eq (i : I) (hi : D.parity i = 0) :
    probeCutoff D m i = m i := by
  simp [probeCutoff, probeDotExponent, hi]

include sy hc in
/-- **Even right bubbles at negative height.** For an even colour `i` with
`0 < probeCutoff` and negative vacuum height `h`, the vacuum entry of
`η x^(s - h - 1) ≫ dcap (-h - 1)` of the tensor target family is the coefficient action of
the `s`-th coefficient of `(1 - w)^M / E(-w)`. -/
theorem vacuumEntry_neg_even (i : I) (hi : D.parity i = 0) (hP0 : 0 < probeCutoff D m i)
    (hh : D.h i ν₀ < 0) (s : ℕ) :
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀
      (etaL i ((s : ℤ) - D.h i ν₀ - 1).toNat ++ dcapL i (-D.h i ν₀ - 1).toNat)
      ((sChain_etaL i _).append (sChain_dcapL i _))
      (SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SYM.probeSeriesInv D k m) i))) := by
  have hhe := vacuum_height_eq D Sc m cutoff N ΛP ΛR hP hR i
  rw [even_probeCutoff_eq D m i hi] at hhe
  have hPN : m i < cutoff i := by rw [hhe] at hh; omega
  have he : ((s : ℤ) - D.h i ν₀ - 1).toNat = cutoff i - m i - 1 + s := by
    rw [hhe]; omega
  have hn : (-D.h i ν₀ - 1).toNat = cutoff i - m i - 1 := by rw [hhe]; omega
  rw [he, hn]
  have hnZ : ((cutoff i - m i - 1 : ℕ) : ℤ) < -D.h i ν₀ := by rw [hhe]; omega
  have hd : ¬StepValid (dn i) true ((0, 0) : Sector I) := by simp [StepValid]
  obtain ⟨c, j, B, hB, hceq, hcup⟩ := tensorVacuum_rightward_even_bubbleEntries D Sc m cutoff L
    ΛP ΛR hP hR sy hc i hi hP0 (Ys (0,0)).obj
    ((congrArg (fun Y => Y.obj) (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L)).trans
      (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hP hR).symm)
    (fun q p => (lw).lcrossSame i ν₀ q p (Ys (0,0)).obj)
    (fun n q r => (lw).dcap i n ν₀ q r (Ys (0,0)).obj)
    (centralPointwiseLeftward_negInverseAt D Sc m cutoff N ΛP ΛR hP hR sy hc i (0,0)
      (Ys (0,0)) hh) cc
  apply vacuumEntry_of_decode D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀ _ _ _ c
    (vacuumDecodeFaithful_tensorTarget D Sc m cutoff ΛP ΛR L hP hR c)
    (vacuumDecode_tensorTargetCoefficient D Sc m cutoff ΛP ΛR L hP hR c hceq _)
  intro z
  rw [ProbeReservoir.compDiag_etaL_dcapL_swappedGens (P) cc lw i _ _ ν₀ hnZ (0,0) _ hd]
  refine (congrArg (fun f => tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
    (f.total ⟨⟨[]⟩, rfl⟩ z)) (hcup ⟨cutoff i - m i - 1, by omega⟩ _).symm).trans ?_
  refine (tensorVacuum_rightward_even_extreme_moments D Sc m cutoff L sy hc i hi hP0
    hPN j B hB s z).trans ?_
  rfl

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
