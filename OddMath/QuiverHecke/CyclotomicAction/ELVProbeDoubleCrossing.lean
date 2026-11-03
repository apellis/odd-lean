import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDoubleAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionDoubleTransform

/-! # The selected scalar comparison on double-induction crossings

DeformedActionAssembly §§5–6 and DeformedMatrixComparison (2), (4) compare
the given equal-colour crossing using the selected one-letter scalar
comparisons and the two canonical induction flattenings. The prescribed
extra minus is retained after conjugating the literal two-letter transform.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N) (i : I)
local notation "cut" => probeCutoff D m
local notation "J" => ELVOld.oldContentAppend D Sc cut ν i
local notation "K" => ELVOld.oldContentAppend D Sc cut (i :: ν) i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "S" => probeOrdinaryAppend D Sc m (i :: ν) i
local notation "Q₀" => probeOldOrdinaryFunctor D Sc m ν
local notation "Q₁" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "Q₂" => probeOldOrdinaryFunctor D Sc m (i :: i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m ν N hN

/-- The selected iterated scalar comparison intertwines the literal
crossings conjugated by their prescribed induction flattenings. -/
theorem probeDoubleAppendComparisonLinear_crossing
    (w : ELVOld.OldContentCategory D Sc cut (i :: i :: ν)) :
    probeDoubleAppendComparisonLinear D Sc m ν N hN i i w ∘ₗ
      doubleTransformLinear J K (probeOldContentEqualCross_supernatural D Sc m ν i) N w =
    doubleTransformLinear T S (probeOrdinaryEqualCross_supernatural D Sc m ν i) O ((Q₂).obj w) ∘ₗ
      probeDoubleAppendComparisonLinear D Sc m ν N hN i i w := by
  apply doubleHom_ext J K N
  intro s v a g b
  simp only [LinearMap.comp_apply, doubleTransformLinear_tensor,
    probeDoubleAppendComparisonLinear, probeDoubleAppendOrdinaryModuleIso_hom_tensor]
  have hmap := (eqToHom (probeOldOrdinaryFunctor_append D Sc m (i :: ν) i)).naturality a
  simp only [eqToHom_app, eqToHom_refl, Category.id_comp, Category.comp_id,
    Functor.comp_map] at hmap
  rw [(Q₁).map_id, (Q₂).map_comp, map_twist,
    probeOrdinaryEqualCross_old D Sc m ν i s, (Q₂).map_comp, hmap]
  rfl

/-- Scalar transport preserves the extra minus in the prescribed action crossing. -/
theorem probeDoubleAppendComparisonLinear_signedCrossing
    (w : ELVOld.OldContentCategory D Sc cut (i :: i :: ν)) :
    probeDoubleAppendComparisonLinear D Sc m ν N hN i i w ∘ₗ
      (-doubleTransformLinear J K (probeOldContentEqualCross_supernatural D Sc m ν i) N w) =
    (-doubleTransformLinear T S (probeOrdinaryEqualCross_supernatural D Sc m ν i) O ((Q₂).obj w)) ∘ₗ
      probeDoubleAppendComparisonLinear D Sc m ν N hN i i w := by
  rw [LinearMap.comp_neg, LinearMap.neg_comp,
    probeDoubleAppendComparisonLinear_crossing D Sc m ν N hN i w]

end OddMath.QuiverHecke
