/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRightwardVacuumCupInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumLeftwardMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumRightwardColumn

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

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
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

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
