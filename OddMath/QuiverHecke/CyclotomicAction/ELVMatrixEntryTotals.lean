import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedMatrixFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations

/-! # Component formulas for the actual shifted matrix entries
The finite families of Brundan--Ellis (1.13)--(1.14) use the prescribed
module unit/cap maps and the canonical parity isomorphisms. These formulas
identify their total component maps without assuming any matrix inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.MatrixEntryTotals
universe u
variable {k : Type u} [CommRing k]
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
private theorem restriction_total (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k B (SVec k)} (f : M ⟶ N) (t : C) :
    ((BalancedInduction.restriction J).map f).total t = f.total (J.obj t) := rfl
end OddMath.QuiverHecke.ELVOld.MatrixEntryTotals

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance matrixEntryTotalsPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- The actual unit column on components is the ordinary unit followed by the dot power. -/
theorem moduleUnitColumn_total (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (n : ℕ) :
    SVec.toLinearMap ((moduleUnitColumn D Sc cutoff i M n).total t) =
      ((inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t)) ^ n).comp
        (SVec.toLinearMap (((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app M).total t)) := by
  rw [moduleUnitColumn, Superfunctor.comp_total, SVec.toLinearMap_comp,
    MatrixEntryTotals.restriction_total, inductionDotModule_power_total]

/-- The actual cap row on components is the ordinary dot power followed by the counit. -/
theorem moduleCapRow_total (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (n : ℕ) :
    SVec.toLinearMap ((moduleCapRow D Sc cutoff i M n).total t) =
      (SVec.toLinearMap (((BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M).total t)).comp
        ((inductionDot D Sc cutoff i
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t) ^ n) := by
  rw [moduleCapRow, Superfunctor.comp_total, SVec.toLinearMap_comp,
    inductionDotModule_power_total]

/-- The unit entry uses precisely the canonical source parity coordinate. -/
theorem unitMatrixEntry_some_total (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (m : ℕ) (r : Fin m)
    (b : (unitMatrixFamily D Sc cutoff i M m (some r)).obj t) :
    (unitMatrixEntry D Sc cutoff i M m (some r)).total t b =
      (moduleUnitColumn D Sc cutoff i M r.val).total t
        (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t b) := by
  change ((((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom ≫
    moduleUnitColumn D Sc cutoff i M r.val).total t) b = _
  rw [Superfunctor.comp_total]
  rfl

/-- Removing the canonical target parity coordinate gives the ordinary cap row. -/
theorem capMatrixEntry_some_total (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (m : ℕ) (r : Fin m)
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t) :
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t
      ((capMatrixEntry D Sc cutoff i M m (some r)).total t z) =
      (moduleCapRow D Sc cutoff i M r.val).total t z := by
  change (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom.total t)
    (((moduleCapRow D Sc cutoff i M r.val ≫
      ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).inv).total t) z) = _
  rw [Superfunctor.comp_total]
  exact (moduleIsoLinearEquiv
    ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t).apply_symm_apply _

/-- The first source-shifted module entry before evaluating components. -/
theorem unitMatrixEntry_none (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    unitMatrixEntry D Sc cutoff i M m none =
      ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
        ((BalancedInduction.induction (append D Sc cutoff i)).obj
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj M))).hom ≫
            matrixMateComponent D Sc cutoff i M := rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

