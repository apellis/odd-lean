/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWeightedLocalInverse

/-! # Local inverse columns of the given weighted cap matrix

BE (1.13): the constructed weighted cap matrix inverse restricts to the
specified output content with the given mate and ordinary dot/cap fields.
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

/-- Restriction retains all rows in the literal finite product coordinate. -/
theorem restriction_finiteRows
    {V : ι → Superfunctor k A (SVec k)} {S : Superfunctor k A (SVec k)}
    (f : ∀ a, S ⟶ V a) (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) :
    (restriction Q).map (OddMath.FiniteSupermodule.rowsHom f hf) ≫
        eqToHom (restriction_finiteProduct Q V) =
      OddMath.FiniteSupermodule.rowsHom (fun a => (restriction Q).map (f a))
        (fun a => map_mem (restriction Q) (hf a)) := by
  change ((restriction Q).map (OddMath.FiniteSupermodule.rowsHom f hf) ≫ 𝟙 _) = _
  rw [Category.comp_id]
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
local notation "m" => contentCapCount D cutoff i β
local notation "p" => D.parity i
local instance weightedCapLocalPi : PiSupercategory k
    (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) := supermodulePiSupercategory

/-- The given weighted cap matrix supplies every local inverse column on its
output content. The prescribed forward fields are retained without an inverse premise. -/
def weightedContentLocalInverseTo
    (hh : contentCrossingHeight D cutoff i β ≤ 0) :
    SKM.SuperSumInvTo (k := k) ((R).map (weightedMatrixMate D Sc cutoff N i M))
      (fun n => (R).map (capDotRow T (truncatedDot_supernatural D Sc cutoff N i) M n))
      p (fun n => n • p) m :=
  localInverseToRows p (fun n => n • p)
    ((R).mapIso ((SKM.homParityShiftDatum (k := k) p).iso ((restriction T).obj (induced T M))))
    (fun r => (R).mapIso ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M))
    (map_mem R ((SKM.homParityShiftDatum (k := k) p).hom_mem _))
    (fun r => map_mem R ((SKM.homParityShiftDatum (k := k) (r.val • p)).hom_mem M))
    ((R).map (weightedMatrixMate D Sc cutoff N i M))
    (fun n => (R).map (capDotRow T (truncatedDot_supernatural D Sc cutoff N i) M n))
    (map_mem R (weightedMatrixMate_mem D Sc cutoff N i M))
    (fun n => map_mem R (capDotRow_mem T (truncatedDot_supernatural D Sc cutoff N i) M n))
    (weightedContentCapMatrixIso D Sc cutoff N i M β hh ≪≫
      eqToIso (restriction_finiteProduct Q (weightedCapMatrixFamily D Sc cutoff N i M m))) (by
        rw [Iso.trans_hom, weightedContentCapMatrixIso_hom]
        change (R).map (rowsHom _ _) ≫ eqToHom (restriction_finiteProduct Q _) = _
        rw [restriction_finiteRows]
        unfold restoredRows
        congr 1
        funext a
        cases a with
        | none =>
          simp only [restoredRow, optionRestoringIso, optionForwardRows,
            Functor.mapIso_inv, ← CategoryTheory.Functor.map_comp, weightedCapMatrixEntry_none]
        | some r =>
          simp only [restoredRow, optionRestoringIso, optionForwardRows,
            Functor.mapIso_inv, ← CategoryTheory.Functor.map_comp, weightedCapMatrixEntry_some])

end OddMath.QuiverHecke.ELVOld
