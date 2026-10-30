/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputCompatibleLifts

/-!
# Prescribed P on the compatible output lifts

This is the unprojected comparison in `DeformedMackeyBoundary.md` §3: the
actual P applied to the constructed section intertwines corrected output rho
with the actual append moving dot. It does not identify a polynomial projection
against the chronological crossing image. That additional full-ELV append
splitting is necessary before deriving the degree-zero polynomial defect.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The literal P-image of the specified compatible long section. -/
def outputLiftBoundary (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] AppendTarget D Sc cutoff j.1 v (v ++ [j.1]) :=
  (pMap D Sc cutoff j.1 v (v ++ [j.1])).comp (outputLongSection D Sc cutoff p j.1 v)

/-- Actual first-order intertwining before the crossing/polynomial splitting. -/
theorem outputLiftBoundary_rho (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) :
    outputLiftBoundary D Sc cutoff p j v (outputCoefficientRho D Sc cutoff p j v f) =
      appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
        (outputLiftBoundary D Sc cutoff p j v f) := by
  change pMap D Sc cutoff j.1 v (v ++ [j.1])
    (outputLongSection D Sc cutoff p j.1 v (outputCoefficientRho D Sc cutoff p j v f)) = _
  rw [← boundaryRho_outputLongSection, pMap_boundaryRho]
  rfl

/-- Every corrected basis lift has its prescribed, not assumed, P-image. -/
theorem pMap_outputCorrectedLift (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (d : ℕ) (b : Old D Sc cutoff v v) :
    pMap D Sc cutoff j.1 v (v ++ [j.1]) (outputCorrectedLift D Sc cutoff p j v d b) =
      appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) d
        (pMap D Sc cutoff j.1 v (v ++ [j.1]) (outputLongLift D Sc cutoff p j.1 v 0 b)) :=
  pMap_boundaryRho_iterate D Sc cutoff j v (v ++ [j.1]) d
    (outputLongLift D Sc cutoff p j.1 v 0 b)

/-- The P-image of every source class differs from that of its specified long
lift by an actual chronological crossing class. This is the needed concrete
factorization statement before constructing the polynomial projection. -/
theorem pMap_sub_outputLiftBoundary_mem (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    pMap D Sc cutoff j.1 v (v ++ [j.1]) z -
      outputLiftBoundary D Sc cutoff p j v (outputLongExtraction D Sc cutoff p j.1 v z) ∈
        chronologicalCrossingSpan D Sc cutoff j.1 v v := by
  have hs : z - outputLongSection D Sc cutoff p j.1 v
      (outputLongExtraction D Sc cutoff p j.1 v z) ∈
        chronologicalShortSpan D Sc cutoff j.1 v v := by
    rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p j.1 v]
    change outputLongExtraction D Sc cutoff p j.1 v _ = 0
    rw [map_sub, outputLongExtraction_section, sub_self]
  have h := pMap_chronologicalShortSpan_le D Sc cutoff j.1 v v
    (Submodule.mem_map.mpr ⟨_, hs, rfl⟩)
  simpa only [map_sub, outputLiftBoundary, LinearMap.comp_apply] using h

end OddMath.QuiverHecke.ELVOld
