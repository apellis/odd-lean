import OddMath.QuiverHecke.CyclotomicAction.ELVOldModuleAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCrossTensor

/-! # Ordered crossing-mate tensors on old representables

Component evaluation for the same-colour entry of DeformedMatrixComparison.
All products keep their order in the full homogeneous-coefficient quotient.
No coefficient truncation or content transport is asserted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem neg_total_apply
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {P Q : Superfunctor k C (SVec k)} (f : P ⟶ Q) (t : C) (x : P.obj t) :
    (-f).total t x = -(f.total t x) := by
  change -(f.app 0 t x) + -(f.app 1 t x) = -(f.app 0 t x + f.app 1 t x)
  exact (neg_add _ _).symm

private theorem equalCrossOnDoubleInduction_eq (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    equalCrossOnDoubleInduction D Sc cutoff i M =
      BalancedInduction.doubleCrossComponent (append D Sc cutoff i)
        (equalCross_supernatural D Sc cutoff i) M := rfl

theorem equalCrossOnDoubleInduction_total_tensor (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s w t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj w ⟶ t)
    (h : (append D Sc cutoff i).obj s ⟶ w) (b : M.obj s) :
    (equalCrossOnDoubleInduction D Sc cutoff i M).total t
      (BalancedInduction.tensor (append D Sc cutoff i)
        (BalancedInduction.induced (append D Sc cutoff i) M).toFunctor w g
          (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s h b)) =
    BalancedInduction.tensor (append D Sc cutoff i)
      (BalancedInduction.induced (append D Sc cutoff i) M).toFunctor
      ((append D Sc cutoff i).obj s)
      (equalCrossComponent D Sc cutoff i s ≫
        twist k (D.parity i * D.parity i) ((append D Sc cutoff i).map h ≫ g))
      (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s (𝟙 _) b) := by
  rw [equalCrossOnDoubleInduction_eq]
  exact BalancedInduction.doubleCrossComponent_total_tensor
    (append D Sc cutoff i) (equalCross_supernatural D Sc cutoff i) M s w t g h b

theorem signedEqualInductionCross_total_tensor (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s w t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj w ⟶ t)
    (h : (append D Sc cutoff i).obj s ⟶ w) (b : M.obj s) :
    ((signedEqualInductionCross D Sc cutoff i).app (D.parity i * D.parity i) M).total t
      (BalancedInduction.tensor (append D Sc cutoff i)
        (BalancedInduction.induced (append D Sc cutoff i) M).toFunctor w g
          (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s h b)) =
    -BalancedInduction.tensor (append D Sc cutoff i)
      (BalancedInduction.induced (append D Sc cutoff i) M).toFunctor
      ((append D Sc cutoff i).obj s)
      (equalCrossComponent D Sc cutoff i s ≫
        twist k (D.parity i * D.parity i) ((append D Sc cutoff i).map h ≫ g))
      (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s (𝟙 _) b) := by
  rw [signedEqualInductionCross_app, ite_eq_left rfl, neg_total_apply,
    equalCrossOnDoubleInduction_total_tensor]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
