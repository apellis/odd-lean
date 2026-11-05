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
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The old dot maps to the same appended affine diagram in the literal
weighted quotient. -/
theorem oldTruncateFunctor_map_appendDot (s : OldCategory D Sc cutoff) :
    (Q).map (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i s) =
      truncatedAppendComponent D Sc cutoff N (dotE D Sc [i] 0) ((Q).obj s) := rfl

/-- The chosen weighted append comparison intertwines the actual signed
old coend dot and the prescribed truncated dot on every output word.
No homogeneous-arrow or homogeneous-vector restriction is needed. -/
theorem appendWeightedModuleIso_hom_dot (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M w ∘ₗ
        CyclotomicCrossingTensor.inductionDot D Sc cutoff i RM w =
      BalancedInduction.transformLinear
        (truncatedAppendComponent_supernatural D Sc cutoff N (by
          simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M ((Q).obj w) ∘ₗ
        weightedAppendComparisonLinear D Sc cutoff N i M w := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply,
    CyclotomicCrossingTensor.inductionDot_tensor,
    appendWeightedModuleIso_hom_tensor, BalancedInduction.transformLinear_tensor]
  rw [(Q).map_comp, map_twist, oldTruncateFunctor_map_appendDot]
  rfl

end OddMath.QuiverHecke.ELVOld
