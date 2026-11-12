/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRightwardVacuumCupInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumCapMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumWholeInput
import OddMath.QuiverHecke.CyclotomicAction.ParameterTwistPureNilpotent

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

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
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

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
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

include hdot in
/-- **Even moments of the rightward vacuum bubble entries.** For an even colour with
`0 < M < N`, leftward data satisfying the negative inverse equations at the tensor
vacuum give an entrywise inverse `(j, B)` of the native cup window of the tensor
vacuum bend such that every product `unit ≫ xᴺ ≫ B n` is the evaluated right bubble
entry `η xᴺ ≫ dcap n` conjugated by one isomorphism `c` (an `eqToHom`), and the last
column has the decoded moments: the shift `N - M - 1 + l` gives the `l`-th coefficient of
`momentSeries (probeSeriesInv)` at `i`. -/
theorem tensorVacuum_rightward_even_moments [Fact Sc.PureNilpotent] (hi : D.parity i = 0)
    (hP : 0 < probeCutoff D m i) (hPN : m i < cutoff i)
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
          ((P).etaEntry cc i N ν₀ (.nil _) q₀ Z ≫ dc n q₀ (.nil _)) ≫ c.hom) ∧
      ∀ (l : ℕ) (z : (V).obj star),
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
            (((adjunction K).unit.app V ≫
              (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^
                (cutoff i - m i - 1 + l)) ≫
                B ⟨cutoff i - m i - 1, by omega⟩).total star z) =
          polynomialToPower D cutoff L (PowerSeries.coeff l
              (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
            tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z := by
  obtain ⟨c, j, B, hB, hceq, hcup⟩ := tensorVacuum_rightward_even_bubbleEntries D Sc m cutoff L
    ΛP ΛR hcP hcR i hdot hi hP Z hZ lc dc HN cc
  exact ⟨c, j, B, hB, hceq, hcup, fun l z =>
    tensorVacuum_rightward_even_extreme_moments D Sc m cutoff L i hdot hi hP hPN j B hB l z⟩

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
