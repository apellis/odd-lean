/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteModuleLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedContentMatrixInverse

/-! # Local inverse entries of the given weighted matrix on an output content

BE (1.14): restrict the constructed weighted unit matrix inverse to its
specified output content and retain the prescribed homogeneous fields.
This also supplies the absent-predecessor boundary without a lower append.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
namespace BalancedInduction
universe u
variable {k C A : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  {ι : Type}

/-- Restriction retains the literal finite module product. -/
theorem restriction_finiteProduct (V : ι → Superfunctor k A (SVec k)) :
    (restriction Q).obj (OddMath.FiniteSupermodule.product V) =
      OddMath.FiniteSupermodule.product (fun a => (restriction Q).obj (V a)) := rfl

variable [Fintype ι]

/-- Restriction retains all columns in their literal finite product coordinate. -/
theorem restriction_finiteColumns
    {V : ι → Superfunctor k A (SVec k)} {T : Superfunctor k A (SVec k)}
    (f : ∀ a, V a ⟶ T) (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) :
    eqToHom (restriction_finiteProduct Q V).symm ≫
        (restriction Q).map (OddMath.FiniteSupermodule.columnsHom f hf) =
      OddMath.FiniteSupermodule.columnsHom (fun a => (restriction Q).map (f a))
        (fun a => map_mem (restriction Q) (hf a)) := by
  change (𝟙 _ ≫ (restriction Q).map (OddMath.FiniteSupermodule.columnsHom f hf)) = _
  rw [Category.id_comp]
  apply Superfunctor.hom_ext_parity
  · intro t
    rfl
  · intro t
    rfl

end BalancedInduction
open BalancedInduction OddMath.FiniteSupermodule CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
  (β : Multiset I)
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "R" => restriction (contentInclusion D Sc cutoff N β)
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "m" => contentUnitCount D cutoff i β
local notation "p" => D.parity i
local instance weightedLocalGlobalPi : PiSupercategory k
    (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) := supermodulePiSupercategory

/-- The given weighted unit matrix supplies all local inverse entries on its
output content. No inverse assumption is added. -/
def weightedContentLocalInverseFrom
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) :
    SKM.SuperSumInvFrom (k := k) ((R).map (weightedMatrixMate D Sc cutoff N i M))
      (fun n => (R).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) M n))
      p (fun n => n • p) m :=
  localInverseFromColumns p (fun n => n • p)
    ((R).mapIso ((SKM.homParityShiftDatum (k := k) p).iso
      (induced T ((restriction T).obj M))))
    (fun r => (R).mapIso ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M))
    (map_mem R ((SKM.homParityShiftDatum (k := k) p).hom_mem _))
    (fun r => map_mem R ((SKM.homParityShiftDatum (k := k) (r.val • p)).hom_mem M))
    ((R).map (weightedMatrixMate D Sc cutoff N i M))
    (fun n => (R).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) M n))
    (map_mem R (weightedMatrixMate_mem D Sc cutoff N i M))
    (fun n => map_mem R (unitDotColumn_mem T (truncatedDot_supernatural D Sc cutoff N i) M n))
    (eqToIso (restriction_finiteProduct Q (weightedUnitMatrixFamily D Sc cutoff N i M m)).symm ≪≫
      weightedContentUnitMatrixIso D Sc cutoff N i M β hh) (by
        rw [Iso.trans_hom, weightedContentUnitMatrixIso_hom]
        change eqToHom (restriction_finiteProduct Q _).symm ≫
          (R).map (columnsHom _ _) = _
        rw [restriction_finiteColumns]
        unfold restoredColumns
        congr 1
        funext a
        cases a with
        | none =>
          simp only [restoredColumn, optionRestoringIso, optionForwardColumns,
            Functor.mapIso_hom, ← CategoryTheory.Functor.map_comp, weightedUnitMatrixEntry_none]
        | some r =>
          simp only [restoredColumn, optionRestoringIso, optionForwardColumns,
            Functor.mapIso_hom, ← CategoryTheory.Functor.map_comp, weightedUnitMatrixEntry_some])

end OddMath.QuiverHecke.ELVOld
