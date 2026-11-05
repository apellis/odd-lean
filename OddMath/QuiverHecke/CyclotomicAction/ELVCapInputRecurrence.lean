import OddMath.QuiverHecke.CyclotomicAction.ELVCrossingInputDot
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRowLeading

/-! # Input contraction pivots on the actual boundary lifts

The input shift has zero constant coefficient. Hence the actual contraction
of a decoded lift is the constant coefficient of the next boundary value.
This gives anti-diagonal vanishing and the prescribed leading equivalence.
These statements concern the concrete input operators; categorical cap
comparison and the full factor action remain separate.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem appendInputShift_zero (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) : appendInputShift D Sc cutoff i v t f 0 = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, add_zero]
  | single m b => simp [appendInputShift, appendOutputShift]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
