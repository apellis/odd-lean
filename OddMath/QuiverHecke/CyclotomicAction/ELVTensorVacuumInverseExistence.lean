/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumZeroHeightMoments

/-! # Existence of the negative inverse data at the tensor vacuum

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

At nonpositive height of the vacuum sector, the actual negative augmented matrix at the
tensor vacuum is invertible (`SupportedSectors.centralAugmentedMatrix_isIso`), so the
selected inverse family satisfies the negative inverse equations (1.14) there
(`tensorVacuum_negInverseAt`). This discharges the leftward-data hypothesis of the
rightward moment theorems: for an even colour with `0 < m i < cutoff i` the native cup
window has an inverse with the decoded moments of `momentSeries (probeSeriesInv)`
(`tensorVacuum_rightward_even_moments_of_inverse`), and at zero height the evaluated bend
is an isomorphism with those moments (`tensorVacuum_zeroHeight_even_moments_of_inverse`,
`tensorVacuum_zeroHeight_odd_moments_of_inverse`). No inverse is assumed.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly ProbeVacuumCap PowerVacuumCoefficient
universe u

local instance inverseExistenceHomPi {k : Type u} [CommRing k]
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
local notation "Zt" => tensorSectorInput D Sc m cutoff L ΛR ΛP hcP hcR
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
private theorem even_probeCutoff_exist (hi : D.parity i = 0) : probeCutoff D m i = m i := by
  simp [probeCutoff, probeDotExponent, hi]

omit [Fintype I] in
private theorem odd_probeCutoff_exist (hi : D.parity i = 1) : probeCutoff D m i = 2 * m i := by
  simp [probeCutoff, probeDotExponent, hi]

local notation "R₀" => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)

include sy hc in
/-- **The negative inverse equations hold at the tensor vacuum.** At nonpositive height
of the vacuum sector, the selected inverse of the actual negative augmented matrix at the
tensor vacuum satisfies the five negative inverse equations. -/
theorem tensorVacuum_negInverseAt (hh : D.h i ν₀ ≤ 0) :
    ∃ (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Zt ⟶ ((P).pathFunctor p).obj Zt)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Zt ⟶ ((P).pathFunctor r).obj Zt),
      (P).NegInverseAt (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i ν₀
        ((0, 0) : Sector I) ((0, 0) : Sector I) Zt lc dc := by
  rw [tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hcP hcR]
  haveI := (SupportedSectors.centralAugmentedMatrix_isIso D Sc m cutoff bound ΛP ΛR hcP hcR
    sy hc i ((0, 0) : Sector I) (SupportedSectors.tensorVacuum D Sc m cutoff L ΛP ΛR)).2 hh
  exact ⟨_, _, (P).negInverseAt_of_isIso _ i _ _ _ _⟩

include sy hc in
/-- **Even moments of the rightward vacuum cap, unconditionally.** For an even colour
with `0 < m i < cutoff i`, the native cup window of the evaluated bend on the tensor
vacuum has an entrywise inverse `(j, B)` whose extreme column has the decoded moments
of `momentSeries (probeSeriesInv)` at `i`. -/
theorem tensorVacuum_rightward_even_moments_of_inverse (hi : D.parity i = 0)
    (hP : 0 < probeCutoff D m i) (hPN : m i < cutoff i) :
    ∃ (j : _ ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m R₀ i H)
      (B : Fin (cutoff i - m i) → (_ ⟶ V)),
      ProbeWindow.IsCupInverse (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H)
        (fun n => (adjunction K).unit.app V ≫
          (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ n.val)) j B ∧
      ∀ (l : ℕ) (z : (V).obj star),
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
            (((adjunction K).unit.app V ≫
              (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^
                (cutoff i - m i - 1 + l)) ≫
                B ⟨cutoff i - m i - 1, by omega⟩).total star z) =
          polynomialToPower D cutoff L (PowerSeries.coeff l
              (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
            tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z := by
  have hh : D.h i ν₀ ≤ 0 := by
    rw [SupportedSectors.vacuum_height_eq D Sc m cutoff bound ΛP ΛR hcP hcR i,
      even_probeCutoff_exist D m i hi]
    omega
  obtain ⟨lc, dc, HN⟩ := tensorVacuum_negInverseAt D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hh
  obtain ⟨-, j, B, hB, -, -, hm⟩ := tensorVacuum_rightward_even_moments D Sc m cutoff L ΛP ΛR
    hcP hcR sy hc i hi hP hPN Zt rfl lc dc HN
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc)
  exact ⟨j, B, hB, hm⟩

include sy hc in
/-- **Even colour, zero height, unconditionally.** For an even colour with
`cutoff i = m i`, the evaluated bend on the tensor vacuum is an isomorphism `s`, and
`unit ≫ yˡ ≫ s⁻¹ ≫ cap` is the `(l + 1)`-th coefficient of
`momentSeries (probeSeriesInv)` at `i`. -/
theorem tensorVacuum_zeroHeight_even_moments_of_inverse (hi : D.parity i = 0)
    (hP : 0 < probeCutoff D m i) (hcut : cutoff i = m i) :
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
  have hh : D.h i ν₀ ≤ 0 := by
    rw [SupportedSectors.vacuum_height_eq D Sc m cutoff bound ΛP ΛR hcP hcR i,
      even_probeCutoff_exist D m i hi]
    omega
  obtain ⟨lc, dc, HN⟩ := tensorVacuum_negInverseAt D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hh
  exact tensorVacuum_zeroHeight_even_moments D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hi hP hcut
    Zt rfl lc dc HN

include sy hc in
/-- **Odd colour, zero height, unconditionally.** For an odd colour with
`cutoff i = 2 m i`, the evaluated bend on the tensor vacuum is an isomorphism `s`; the
moment `unit ≫ y^(2r) ≫ s⁻¹ ≫ cap` is the `r`-th coefficient of
`momentSeries (probeSeriesInv)` at `i` times the normalized odd coefficient, and
`unit ≫ y^(2r+1) ≫ s⁻¹ ≫ cap` is the `(r + 1)`-th coefficient. -/
theorem tensorVacuum_zeroHeight_odd_moments_of_inverse (hi : D.parity i = 1)
    (hP : 0 < probeCutoff D m i) (hcut : cutoff i = 2 * m i) :
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
  have hh : D.h i ν₀ ≤ 0 := by
    rw [SupportedSectors.vacuum_height_eq D Sc m cutoff bound ΛP ΛR hcP hcR i,
      odd_probeCutoff_exist D m i hi]
    omega
  obtain ⟨lc, dc, HN⟩ := tensorVacuum_negInverseAt D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hh
  exact tensorVacuum_zeroHeight_odd_moments D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hi hP hcut
    Zt rfl lc dc HN

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
