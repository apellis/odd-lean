/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumRightwardEvenMoments

/-! # Zero-height moments of the vacuum bend on the tensor vacuum

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

At zero height of the vacuum sector (`cutoff i = probeCutoff D m i`), the negative
inverse window is empty. Leftward data satisfying the negative inverse equations
(1.14) at the tensor vacuum then make the evaluated A6 bend an isomorphism `s`
(from `vacuumRightwardCupInverse_native_odd` and `vacuumRightwardCupInverse_native_even`),
and the decoded moments `unit ≫ yˡ ≫ s⁻¹ ≫ cap` are the coefficients of
`momentSeries (probeSeriesInv)` at `i` given by `tensorVacuumZeroHeightCap_even_moments`,
`tensorVacuumZeroHeightCap_odd_moments_even` and `tensorVacuumZeroHeightCap_odd_moments_odd`
(`tensorVacuum_zeroHeight_even_moments`, `tensorVacuum_zeroHeight_odd_moments`).
The invertibility of the bend is derived, not assumed.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

/-- A cup inverse with an empty window is a two-sided inverse. -/
theorem IsCupInverse.inv_of_eq_zero {C : Type*} [Category C] [Preadditive C] {X Y O : C}
    {h : ℕ} (hh : h = 0) {s : X ⟶ Y} {w : Fin h → (O ⟶ Y)} {j : Y ⟶ X}
    {B : Fin h → (Y ⟶ O)} (H : IsCupInverse s w j B) : s ≫ j = 𝟙 X ∧ j ≫ s = 𝟙 Y := by
  subst hh
  exact ⟨H.1, by simpa using H.2.2.2.2⟩

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly ProbeVacuumCap PowerVacuumCoefficient
universe u

local instance zeroHeightVacuumMomentsHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I)
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
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
local notation "K" => contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i]
local notation "q₀" => SPath.centralDnUp i (SKM.wt D ν₀ [SKM.up i]) ν₀ ((0, 0) : Sector I)
  ⟨false, trivial⟩

omit [Fintype I] in
private theorem even_probeCutoff_zero (hi : D.parity i = 0) : probeCutoff D m i = m i := by
  simp [probeCutoff, probeDotExponent, hi]

omit [Fintype I] in
private theorem odd_probeCutoff_zero (hi : D.parity i = 1) : probeCutoff D m i = 2 * m i := by
  simp [probeCutoff, probeDotExponent, hi]

local notation "R₀" => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)

include sy hc in
/-- **Even colour, zero height, on the tensor vacuum.** For an even colour with
`cutoff i = m i`, leftward data satisfying the negative inverse equations at the tensor
vacuum make the evaluated bend an isomorphism `s`, and the decoded moment
`unit ≫ yˡ ≫ s⁻¹ ≫ cap` is the `(l + 1)`-th coefficient of
`momentSeries (probeSeriesInv)` at `i`. -/
theorem tensorVacuum_zeroHeight_even_moments (hi : D.parity i = 0)
    (hP : 0 < probeCutoff D m i) (hcut : cutoff i = m i)
    (Z : (P).H ((0, 0) : Sector I)) (hZ : Z = Zt)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z)
    (HN : (P).NegInverseAt (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc) :
    ∃ s : shiftedPreSourceObject D (parameterTwist D Sc) m R₀ i H ≅
        (restriction K).obj ((induction K).obj V),
      s.hom = evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H ∧
      ∀ (l : ℕ) (z : (V).obj star),
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
            (((adjunction K).unit.app V ≫
              (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ l) ≫
                s.inv ≫ shiftedPreCap D (parameterTwist D Sc) m R₀ i hP H).total star z) =
          polynomialToPower D cutoff L (PowerSeries.coeff (l + 1)
              (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
            tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z := by
  classical
  have hlen : (-D.h i ν₀).toNat = 0 := by
    rw [SupportedSectors.vacuum_negative_window_length D Sc m cutoff bound ΛP ΛR hcP hcR i,
      even_probeCutoff_zero D m i hi]
    omega
  have hex := (vacuumRightwardCupInverse_native_even D Sc m cutoff bound ΛP ΛR hcP hcR
    (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) sy hc i Z
    (hZ.trans (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hcP hcR).symm) lc dc HN
    hP hi).imp fun _ hB => ProbeWindow.IsCupInverse.inv_of_eq_zero hlen hB
  rw [show vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) = H from
    tensorOutputAt_empty D (parameterTwist D Sc) m cutoff L ΛR] at hex
  obtain ⟨j, h₁, h₂⟩ := hex
  obtain ⟨s, hs⟩ : ∃ s : shiftedPreSourceObject D (parameterTwist D Sc) m R₀ i H ≅
      (restriction K).obj ((induction K).obj V),
      s.hom = evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H :=
    ⟨⟨_, j, h₁, h₂⟩, rfl⟩
  have hN : 0 < cutoff i := by
    rw [even_probeCutoff_zero D m i hi] at hP
    omega
  exact ⟨s, hs, fun l z => tensorVacuumZeroHeightCap_even_moments D (parameterTwist D Sc) m
    cutoff L sy (parameterTwist_homogeneous D Sc hc) i hi hP hN hcut s hs l z⟩

include sy hc in
/-- **Odd colour, zero height, on the tensor vacuum.** For an odd colour with
`cutoff i = 2 m i`, leftward data satisfying the negative inverse equations at the
tensor vacuum make the evaluated A6 bend an isomorphism `s`; the decoded moment
`unit ≫ y^(2r) ≫ s⁻¹ ≫ cap` is the `r`-th coefficient of `momentSeries (probeSeriesInv)`
at `i` times the normalized odd coefficient, and `unit ≫ y^(2r+1) ≫ s⁻¹ ≫ cap` is the
`(r + 1)`-th coefficient. -/
theorem tensorVacuum_zeroHeight_odd_moments (hi : D.parity i = 1)
    (hP : 0 < probeCutoff D m i) (hcut : cutoff i = 2 * m i)
    (Z : (P).H ((0, 0) : Sector I)) (hZ : Z = Zt)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z)
    (HN : (P).NegInverseAt (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc) :
    ∃ s : shiftedPreSourceObject D (parameterTwist D Sc) m R₀ i H ≅
        (restriction K).obj ((induction K).obj V),
      s.hom = evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H ∧
      ∀ (r : ℕ) (z : (V).obj star),
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
            (((adjunction K).unit.app V ≫
              (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ (2 * r)) ≫
                s.inv ≫ shiftedPreCap D (parameterTwist D Sc) m R₀ i hP H).total star z) =
          ((-1 : k) ^ (cutoff i + 1) •
              coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
            (polynomialToPower D cutoff L (PowerSeries.coeff r
              (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
              tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z) ∧
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
            (((adjunction K).unit.app V ≫
              (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ (2 * r + 1)) ≫
                s.inv ≫ shiftedPreCap D (parameterTwist D Sc) m R₀ i hP H).total star z) =
          polynomialToPower D cutoff L (PowerSeries.coeff (r + 1)
              (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
            tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z := by
  classical
  have hlen : (-D.h i ν₀).toNat = 0 := by
    rw [SupportedSectors.vacuum_negative_window_length D Sc m cutoff bound ΛP ΛR hcP hcR i,
      odd_probeCutoff_zero D m i hi]
    omega
  have hex := (vacuumRightwardCupInverse_native_odd D Sc m cutoff bound ΛP ΛR hcP hcR
    (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) sy hc i Z
    (hZ.trans (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hcP hcR).symm) lc dc HN
    hP hi).imp fun _ hB => ProbeWindow.IsCupInverse.inv_of_eq_zero hlen hB
  rw [show vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) = H from
    tensorOutputAt_empty D (parameterTwist D Sc) m cutoff L ΛR] at hex
  obtain ⟨j, h₁, h₂⟩ := hex
  obtain ⟨s, hs⟩ : ∃ s : shiftedPreSourceObject D (parameterTwist D Sc) m R₀ i H ≅
      (restriction K).obj ((induction K).obj V),
      s.hom = evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H :=
    ⟨⟨_, j, h₁, h₂⟩, rfl⟩
  have hN : 0 < cutoff i := by
    rw [odd_probeCutoff_zero D m i hi] at hP
    omega
  exact ⟨s, hs, fun r z =>
    ⟨tensorVacuumZeroHeightCap_odd_moments_even D (parameterTwist D Sc) m cutoff L sy
      (parameterTwist_homogeneous D Sc hc) i hi hP hN hcut s hs r z,
     tensorVacuumZeroHeightCap_odd_moments_odd D (parameterTwist D Sc) m cutoff L sy
      (parameterTwist_homogeneous D Sc hc) i hi hP hN hcut s hs r z⟩⟩

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
