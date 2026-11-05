import OddMath.QuiverHecke.CyclotomicAction.ELVInductionMateTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVOldModuleAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCrossTensor

/-! # The actual signed crossing mate on balanced generators

This evaluates the fixed old-module adjunction and the prescribed signed
crossing. No mate formula or component inverse is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem actualCross_eq (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    equalCrossOnDoubleInduction D Sc cutoff i N =
      BalancedInduction.doubleCrossComponent (append D Sc cutoff i)
        (equalCross_supernatural D Sc cutoff i) N := rfl

private theorem signedCross_component_eq (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (signedEqualInductionCross D Sc cutoff i).app (D.parity i * D.parity i) N =
      -BalancedInduction.doubleCrossComponent (append D Sc cutoff i)
        (equalCross_supernatural D Sc cutoff i) N := by
  rw [signedEqualInductionCross_app, ite_eq_left rfl]
  exact congrArg Neg.neg (actualCross_eq D Sc cutoff i N)

private theorem oldModuleMate_eq_ordered (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (oldModuleMate D Sc cutoff i).app (D.parity i * D.parity i) N =
      BalancedInduction.orderedMateComponent (append D Sc cutoff i)
        (equalCross_supernatural D Sc cutoff i) N := by
  rw [oldModuleMate_app, signedCross_component_eq]
  rfl

theorem oldModuleMate_total_tensor (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : N.obj ((append D Sc cutoff i).obj s)) :
    ((oldModuleMate D Sc cutoff i).app (D.parity i * D.parity i) N).total t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj N).toFunctor s g b) =
    -BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor
      ((append D Sc cutoff i).obj s)
      (equalCrossComponent D Sc cutoff i s ≫
        twist k (D.parity i * D.parity i) ((append D Sc cutoff i).map g)) b := by
  rw [oldModuleMate_eq_ordered]
  exact BalancedInduction.orderedMateComponent_total_tensor
    (append D Sc cutoff i) (equalCross_supernatural D Sc cutoff i) N s t g b

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
