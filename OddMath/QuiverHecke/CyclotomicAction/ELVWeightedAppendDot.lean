import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot

/-! # Dot transport by weighted append comparison

The generator compatibility in DeformedActionAssembly §§5–6 and STATUS
critical-chain item 2 uses
the selected five-isomorphism comparison. It intertwines the old signed
coend dot with the literal truncated appended dot, retaining the parity
twist of arbitrary old arrows.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "R" => weightedRestriction D Sc cutoff N M

/-- The old dot maps to the same appended affine diagram in the literal
weighted quotient. -/
theorem oldTruncateFunctor_map_appendDot (s : OldCategory D Sc cutoff) :
    (Q).map (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i s) =
      truncatedAppendComponent D Sc cutoff N (dotE D Sc [i] 0) ((Q).obj s) := rfl

/-- The chosen weighted append comparison intertwines the actual signed
old coend dot and the prescribed truncated dot on every output word.
No homogeneous-arrow or homogeneous-vector restriction is needed. -/
theorem appendWeightedModuleIso_hom_dot (w : OldCategory D Sc cutoff) :
    (appendWeightedModuleIso D Sc cutoff N i M).hom.total ((Q).obj w) ∘ₗ
        CyclotomicCrossingTensor.actualInductionDot D Sc cutoff i R w =
      ((moduleInductionDot D Sc cutoff N i).app (D.parity i) M).app
        (D.parity i) ((Q).obj w) ∘ₗ
        (appendWeightedModuleIso D Sc cutoff N i M).hom.total ((Q).obj w) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply,
    CyclotomicCrossingTensor.actualInductionDot_tensor,
    appendWeightedModuleIso_hom_tensor, moduleInductionDot_tensor]
  rw [(Q).map_comp, map_twist, oldTruncateFunctor_map_appendDot]

end OddMath.QuiverHecke.ELVOld
