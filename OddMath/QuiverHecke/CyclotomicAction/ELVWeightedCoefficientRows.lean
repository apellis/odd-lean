import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixComponentInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows

/-! # Prescribed inverse coefficient rows under weighted descent

The coefficient functional in `SwappedVacuumCoordinates.md`, §6 and
`SwappedVacuumNonpositiveBubbles.md`, §2 must be the prescribed inverse
row in the selected weighted charts. The proved given forward matrix
square determines this inverse comparison, with its original parity unshift.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u

private theorem inverse_chart_square
    {k : Type u} [CommRing k] {V W X Y : SVec k}
    (e : V ≅ W) (f : X ≅ Y) (c : W ≃ₗ[k] Y) (d : V ≃ₗ[k] X)
    (h : c.toLinearMap ∘ₗ SVec.toLinearMap e.hom =
      SVec.toLinearMap f.hom ∘ₗ d.toLinearMap) :
    d.toLinearMap ∘ₗ SVec.toLinearMap e.inv =
      SVec.toLinearMap f.inv ∘ₗ c.toLinearMap := by
  have he (z : W) : e.hom (e.inv z) = z := by
    have hi := congrArg (fun g : W ⟶ W => g z) e.inv_hom_id
    simpa only [SVec.comp_apply, SVec.id_apply] using hi
  have hf (z : X) : f.inv (f.hom z) = z := by
    have hi := congrArg (fun g : X ⟶ X => g z) f.hom_inv_id
    simpa only [SVec.comp_apply, SVec.id_apply] using hi
  apply LinearMap.ext
  intro z
  calc
    d (e.inv z) = f.inv (f.hom (d (e.inv z))) := (hf _).symm
    _ = f.inv (c (e.hom (e.inv z))) := congrArg f.inv (LinearMap.congr_fun h (e.inv z)).symm
    _ = f.inv (c z) := congrArg (fun b => f.inv (c b)) (he z)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
local instance weightedCoefficientRowsPi :
    PiSupercategory k (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :=
  supermodulePiSupercategory
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The inverse of the given weighted unit matrix is the inverse of the
given old matrix under the same selected whole finite-family charts. -/
theorem weightedUnitMatrix_inverse_compare (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I)) :
    (weightedUnitMatrixValueEquiv D Sc cutoff N i M
      (contentUnitCount D cutoff i (w.word : Multiset I)) w).toLinearMap ∘ₗ
      SVec.toLinearMap (moduleUnitMatrixIso D Sc cutoff RM i w hh).inv =
    SVec.toLinearMap (weightedUnitMatrixComponentIso D Sc cutoff N i M w hh).inv ∘ₗ
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  apply inverse_chart_square
  rw [moduleUnitMatrixIso_hom, weightedUnitMatrixComponentIso_hom]
  exact weightedMatrixCharts_unitMatrix D Sc cutoff N i M _ w

/-- The original inverse-row parity coordinate, removed after the actual
prescribed weighted inverse. This is not an independently chosen extractor. -/
def weightedUnitCoefficient (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (w.word : Multiset I))) :
    (((restriction T).obj ((induction T).obj M)).obj ((Q).obj w)) →ₗ[k] M.obj ((Q).obj w) :=
  (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
    (r.val • D.parity i)).iso M) ((Q).obj w)).toLinearMap ∘ₗ
      LinearMap.proj (some r) ∘ₗ
        SVec.toLinearMap (weightedUnitMatrixComponentIso D Sc cutoff N i M w hh).inv

/-- The chosen weighted inverse coefficient is exactly the old inverse
coefficient under the selected append chart, with no added scalar. -/
theorem weightedUnitCoefficient_compare (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (w.word : Multiset I))) :
    weightedUnitCoefficient D Sc cutoff N i M w hh r ∘ₗ
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap =
    moduleUnitCoefficient D Sc cutoff RM i w hh r := by
  have hi := weightedUnitMatrix_inverse_compare D Sc cutoff N i M w hh
  apply LinearMap.ext
  intro z
  have hz := congrFun (LinearMap.congr_fun hi z) (some r)
  have hc := congrArg
    (fun b => ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom.total ((Q).obj w) b) hz
  have hu := shiftedModuleValueLinearEquiv_hom_coordinate RM M w ((Q).obj w)
    (LinearEquiv.refl k _) (r.val • D.parity i)
    (((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) (some r))
  exact hc.symm.trans hu

/-- The actual weighted inverse coefficient extracts the given weighted
unit/dot columns on every input module vector throughout the finite window. -/
theorem weightedUnitCoefficient_unitDotColumn (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (w.word : Multiset I)))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i (w.word : Multiset I))
    (b : M.obj ((Q).obj w)) :
    weightedUnitCoefficient D Sc cutoff N i M w hh r
      ((unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) M a).total ((Q).obj w) b) =
      if a = r.val then b else 0 := by
  have hc := LinearMap.congr_fun (weightedUnitCoefficient_compare D Sc cutoff N i M w hh r)
    ((moduleUnitColumn D Sc cutoff i RM a).total w b)
  have hu := weightedUnitColumnValue_compare D Sc cutoff N i M w a b
  change weightedUnitCoefficient D Sc cutoff N i M w hh r
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w
        ((moduleUnitColumn D Sc cutoff i RM a).total w b)) =
      moduleUnitCoefficient D Sc cutoff RM i w hh r
        ((moduleUnitColumn D Sc cutoff i RM a).total w b) at hc
  rw [hu] at hc
  by_cases har : a = r.val
  · rw [ite_eq_left har, har]
    rw [har] at hc
    exact hc.trans (moduleUnitCoefficient_column D Sc cutoff RM i w hh r b)
  · rw [ite_eq_right har]
    exact hc.trans (moduleUnitCoefficient_column_ne D Sc cutoff RM i w hh r ⟨a, ha⟩
      (fun he => har (congrArg Fin.val he).symm) b)

end OddMath.QuiverHecke.ELVOld
