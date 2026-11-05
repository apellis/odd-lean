/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRightwardVacuumCupInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumLeftwardMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumRightwardColumn

/-! # Elaboration probe for the rightward column moments (temporary) -/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.RightwardProbe
open BalancedInduction CyclotomicAction SwappedAssembly ProbeVacuumCap PowerVacuumCoefficient
open CyclotomicCrossingTensor WeightTensorVacuum
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I)

section NoInstWB
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)
local notation "K" => contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i]

include sy hc in
theorem probe_NoInstWB (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m
      (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : ProbeWindow.IsCupInverse (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫
        (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ n.val)) j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
        ((rightwardUnitColumn ((adjunction K).unit.app V)
          (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H) B
          (cutoff i - 2 * m i - 1 + 2 * r)
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z :=
  rightwardUnitColumn_odd_moments_even D (parameterTwist D Sc) m cutoff L sy
    (parameterTwist_homogeneous D Sc hc) i hi hP hPN j B hB r z

end NoInstWB

section NoInstPB
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)
local notation "K" => contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i]

include sy hc in
theorem probe_NoInstPB (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m
      (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : ProbeWindow.IsCupInverse (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫
        (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ n.val)) j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
        ((rightwardUnitColumn ((adjunction K).unit.app V)
          (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H) B
          (cutoff i - 2 * m i - 1 + 2 * r)
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z :=
  rightwardUnitColumn_odd_moments_even D (parameterTwist D Sc) m cutoff L sy
    (parameterTwist_homogeneous D Sc hc) i hi hP hPN j B hB r z

end NoInstPB

section InstWB
local instance probeHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)
local notation "K" => contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i]

include sy hc in
theorem probe_InstWB (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m
      (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : ProbeWindow.IsCupInverse (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫
        (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ n.val)) j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
        ((rightwardUnitColumn ((adjunction K).unit.app V)
          (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H) B
          (cutoff i - 2 * m i - 1 + 2 * r)
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z :=
  rightwardUnitColumn_odd_moments_even D (parameterTwist D Sc) m cutoff L sy
    (parameterTwist_homogeneous D Sc hc) i hi hP hPN j B hB r z

end InstWB

section InstPB
local instance probeHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)
local notation "K" => contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i]

include sy hc in
theorem probe_InstPB (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m
      (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : ProbeWindow.IsCupInverse (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫
        (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ n.val)) j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
        ((rightwardUnitColumn ((adjunction K).unit.app V)
          (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H) B
          (cutoff i - 2 * m i - 1 + 2 * r)
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z :=
  rightwardUnitColumn_odd_moments_even D (parameterTwist D Sc) m cutoff L sy
    (parameterTwist_homogeneous D Sc hc) i hi hP hPN j B hB r z

end InstPB

section NoInstPBOdd
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)
local notation "K" => contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i]

include sy hc in
theorem probe_NoInstPBOdd (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m
      (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : ProbeWindow.IsCupInverse (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫
        (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ n.val)) j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
        ((rightwardUnitColumn ((adjunction K).unit.app V)
          (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H) B
          (cutoff i - 2 * m i - 1 + (2 * r + 1))
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        (polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
          tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z) :=
  rightwardUnitColumn_odd_moments_odd D (parameterTwist D Sc) m cutoff L sy
    (parameterTwist_homogeneous D Sc hc) i hi hP hPN j B hB r z

end NoInstPBOdd

section InstPBOdd
local instance probeHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)
local notation "K" => contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i]

include sy hc in
theorem probe_InstPBOdd (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m
      (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : ProbeWindow.IsCupInverse (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫
        (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H ^ n.val)) j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
        ((rightwardUnitColumn ((adjunction K).unit.app V)
          (evaluatedPostDot D (parameterTwist D Sc) m cutoff bound i H) B
          (cutoff i - 2 * m i - 1 + (2 * r + 1))
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        (polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
          tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z) :=
  rightwardUnitColumn_odd_moments_odd D (parameterTwist D Sc) m cutoff L sy
    (parameterTwist_homogeneous D Sc hc) i hi hP hPN j B hB r z

end InstPBOdd

end OddMath.QuiverHecke.ELVOld.RightwardProbe
