/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumCapMoments

/-! # Elaboration probe for the rightward extreme moments (temporary) -/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient ProbeVacuumCap
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I)

local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "W₀" => Functor.obj (restriction (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I)))
  (weightedVacuum D (parameterTwist D Sc) cutoff L)
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound W₀
local notation "R₀" => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D (parameterTwist D Sc) m
local notation "V" => Superfunctor.obj H N₀
local notation "star" => (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)
local notation "K" => contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i]
local notation "Tw" => parameterTwist D Sc

include sy hc in
/-- Probe: only the hypotheses of the cap-moment lemma at the parameter twist. -/
theorem rightwardProbe_hyp (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Tw m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Tw m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Tw m cutoff bound i H ^ n.val))
      j B)
    (r : ℕ) (z : (V).obj star) : True := by
  have _h := tensorVacuumNegativeCap_odd_moments_even D Tw m cutoff L sy
    (parameterTwist_homogeneous D Sc hc) i hi hP (by omega) hPN j B hB r z
  trivial

include sy hc in
/-- Probe: the full even moment at the parameter twist, in the cap-moment context. -/
theorem rightwardProbe_full (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Tw m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Tw m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Tw m cutoff bound i H ^ n.val))
      j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Tw m cutoff L
        (((adjunction K).unit.app V ≫
          (evaluatedPostDot D Tw m cutoff bound i H ^ (cutoff i - 2 * m i - 1 + 2 * r)) ≫
            B ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Tw m cutoff L z :=
  tensorVacuumNegativeCap_odd_moments_even D Tw m cutoff L sy
    (parameterTwist_homogeneous D Sc hc) i hi hP (by omega) hPN j B hB r z

end OddMath.QuiverHecke.ELVOld
