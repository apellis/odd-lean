import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWeightedCapInverse
import OddMath.Algebra.FiniteSupermoduleCoordinates

/-! # Principal entries of the specified weighted local inverses

BE (1.13)–(1.14): evaluation retains the principal projection or insertion
of the same finite content matrix inverse, with its named parity isomorphism.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction OddMath.FiniteSupermodule CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) (β : Multiset I)
local instance weightedPrincipalPi : PiSupercategory k
    (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) := supermodulePiSupercategory
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "R" => restriction (contentInclusion D Sc cutoff N β)

/-- The unit local principal is the actual inverse's literal `none` row. -/
theorem weightedContentLocalInverseFrom_principal_total
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (z : ((restriction (T)).obj (induced (T) M)).obj w.obj) :
    (weightedContentLocalInverseFrom D Sc cutoff N i M β hh).f'.total w z =
      (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso (induced (T) ((restriction (T)).obj M))).hom.total w.obj)
        (((weightedContentUnitMatrixIso D Sc cutoff N i M β hh).inv.total w z) none) := by
  dsimp only [weightedContentLocalInverseFrom, localInverseFromColumns,
    inverseCoordinateRow, optionRestoringIso]
  simp only [Iso.trans_inv, eqToIso.inv]
  dsimp only [restriction_finiteProduct]
  simp only [eqToHom_refl, Category.comp_id, Superfunctor.comp_total]
  change (((R).mapIso ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
    (induced (T) ((restriction (T)).obj M)))).hom.total w)
      ((projectionHom (fun a => (R).obj (weightedUnitMatrixFamily D Sc cutoff N i M
        (contentUnitCount D cutoff i β) a)) none).total w
        ((weightedContentUnitMatrixIso D Sc cutoff N i M β hh).inv.total w z)) = _
  rw [projectionHom_total_apply]
  rfl

/-- The cap local principal is the actual inverse's literal `none` column. -/
theorem weightedContentLocalInverseTo_principal_total
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (z : ((restriction (T)).obj (induced (T) M)).obj w.obj) :
    (weightedContentLocalInverseTo D Sc cutoff N i M β hh).f'.total w z =
      (weightedContentCapMatrixIso D Sc cutoff N i M β hh).inv.total w
        (Pi.single none
          ((((SKM.homParityShiftDatum (k := k) (D.parity i)).iso ((restriction (T)).obj (induced (T) M))).inv.total w.obj) z)) := by
  dsimp only [weightedContentLocalInverseTo, localInverseToRows,
    inverseCoordinateColumn, optionRestoringIso]
  simp only [Iso.trans_inv, eqToIso.inv]
  dsimp only [restriction_finiteProduct]
  simp only [eqToHom_refl, Category.id_comp, Superfunctor.comp_total]
  change (weightedContentCapMatrixIso D Sc cutoff N i M β hh).inv.total w
    ((inclusionHom (fun a => (R).obj (weightedCapMatrixFamily D Sc cutoff N i M
        (contentCapCount D cutoff i β) a)) none).total w
      ((((R).mapIso ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
        ((restriction (T)).obj (induced (T) M)))).inv.total w) z)) = _
  congr 1
  apply funext
  intro a
  cases a with
  | none =>
      simp only [inclusionHom_total_self, Pi.single_eq_same]
      rfl
  | some a =>
      rw [inclusionHom_total_ne _ none (some a) (Ne.symm (Option.some_ne_none a))]
      symm
      apply Pi.single_eq_of_ne
      exact Option.some_ne_none a

end OddMath.QuiverHecke.ELVOld
