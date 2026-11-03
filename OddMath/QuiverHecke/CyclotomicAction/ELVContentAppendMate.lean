import OddMath.QuiverHecke.CyclotomicAction.ELVContentEFChartTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMateEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedMatrixFamilies

/-! # The prescribed same-colour mate under chosen content extension

DeformedMatrixComparison (2), (4), first matrix entry. The independently
prescribed content cup-crossing-cap operator is compared with the old
module mate through the chosen E/F charts, on literal balanced tensors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open CategoryTheory.Functor
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
namespace BalancedInduction
private theorem tensor_neg_left
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A]
    (J : C ⥤ A) (M : Superfunctor k C (SVec k))
    (s : C) (t : A) (g : J.obj s ⟶ t) (b : M.obj s) :
    tensor J M.toFunctor s (-g) b = -tensor J M.toFunctor s g b := by
  unfold tensor
  rw [TensorProduct.neg_tmul, _root_.map_neg]
private def mateCoendLinear
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (M : Superfunctor k C (SVec k))
    (f : induced A ((restriction A).obj M) ⟶ (restriction A).obj (induced A M))
    (t : C) : Obj A ((restriction A).obj M).toFunctor t →ₗ[k] Obj A M.toFunctor (A.obj t) :=
  f.total t

private theorem mateCoendLinear_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (M : Superfunctor k C (SVec k))
    (f : induced A ((restriction A).obj M) ⟶ (restriction A).obj (induced A M))
    (t : C) (x : Obj A ((restriction A).obj M).toFunctor t) :
    mateCoendLinear A M f t x = f.total t x := rfl
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₀" => oldContentInclusion D Sc cutoff ν
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i
local notation "Fc" => BalancedInduction.restriction (k := k) J₀
local notation "E" => BalancedInduction.induction (k := k) J
local notation "R₁" => BalancedInduction.restriction (k := k) Q₁

private theorem matrixMateComponent_total_tensor
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s t : OldCategory D Sc cutoff) (g : (J).obj s ⟶ t) (b : M.obj ((J).obj s)) :
    (matrixMateComponent D Sc cutoff i M).total t
      (BalancedInduction.tensor J ((BalancedInduction.restriction J).obj M).toFunctor s g b) =
      -BalancedInduction.tensor J M.toFunctor ((J).obj s)
        (equalCrossComponent D Sc cutoff i s ≫ twist k (D.parity i) ((J).map g)) b := by
  have h := oldModuleMate_total_tensor D Sc cutoff i M s t g b
  simp only [SKM.zmod2_mul_self] at h
  exact h

private def oldMatrixMateCoendLinear
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J ((BalancedInduction.restriction J).obj M).toFunctor t →ₗ[k]
      BalancedInduction.Obj J M.toFunctor ((J).obj t) :=
  BalancedInduction.mateCoendLinear J M (matrixMateComponent D Sc cutoff i M) t

private theorem oldMatrixMateCoendLinear_apply
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff)
    (x : BalancedInduction.Obj J ((BalancedInduction.restriction J).obj M).toFunctor t) :
    oldMatrixMateCoendLinear D Sc cutoff i M t x =
      (matrixMateComponent D Sc cutoff i M).total t x :=
  BalancedInduction.mateCoendLinear_apply J M (matrixMateComponent D Sc cutoff i M) t x

private theorem oldMatrixMateCoendLinear_tensor
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s t : OldCategory D Sc cutoff) (g : (J).obj s ⟶ t) (b : M.obj ((J).obj s)) :
    oldMatrixMateCoendLinear D Sc cutoff i M t
      (BalancedInduction.tensor J ((BalancedInduction.restriction J).obj M).toFunctor s g b) =
      -BalancedInduction.tensor J M.toFunctor ((J).obj s)
        (equalCrossComponent D Sc cutoff i s ≫ twist k (D.parity i) ((J).map g)) b := by
  have h := matrixMateComponent_total_tensor D Sc cutoff i M s t g b
  have ha := oldMatrixMateCoendLinear_apply D Sc cutoff i M t
    (BalancedInduction.tensor J ((BalancedInduction.restriction J).obj M).toFunctor s g b)
  exact ha.trans h

/-- The literal last equal crossing in the two-letter content block. -/
def oldContentEqualCross (s : OldContentCategory D Sc cutoff ν) :
    (J₀ ⋙ J₁).obj s ⟶ (J₀ ⋙ J₁).obj s :=
  equalCrossComponent D Sc cutoff i s.obj

theorem oldContentEqualCross_supernatural :
    IsSupernatural k (D.parity i * D.parity i) (oldContentEqualCross D Sc cutoff ν i) where
  mem s := (equalCross_supernatural D Sc cutoff i).mem s.obj
  naturality := by
    intro s t p f hf
    exact (equalCross_supernatural D Sc cutoff i).naturality hf

/-- On every source tensor, the selected content E/F charts intertwine the
independently prescribed content cup-crossing-cap and the old module mate. -/
private theorem oldContentAppendRestrictionLinear_mate_coend_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (J).obj s.obj ⟶ t.obj) (b : N.obj ((J₀).obj s)) :
    oldContentAppendRestrictionLinear D Sc cutoff (i :: ν) i N ((J₁).obj t)
      (BalancedInduction.orderedGridMateLinear J₀ J₁
        (oldContentEqualCross_supernatural D Sc cutoff ν i) N t
        (BalancedInduction.tensor J₀ ((Fc).obj N).toFunctor s g b)) =
    oldMatrixMateCoendLinear D Sc cutoff i (BalancedInduction.induced Q₁ N) t.obj
      (oldContentEFRestrictionLinear D Sc cutoff ν i N t
        (BalancedInduction.tensor J₀ ((Fc).obj N).toFunctor s g b)) := by
  have hGrid := BalancedInduction.orderedGridMateLinear_tensor J₀ J₁
    (oldContentEqualCross_supernatural D Sc cutoff ν i) N s t g b
  have hRestr := oldContentAppendRestrictionLinear_tensor D Sc cutoff (i :: ν) i
    N ((J₀).obj s) ((J₁).obj t)
    (-(oldContentEqualCross D Sc cutoff ν i s ≫
      twist k (D.parity i * D.parity i) ((J₁).map g))) b
  have hLeft := (congrArg (oldContentAppendRestrictionLinear D Sc cutoff (i :: ν) i N
    ((J₁).obj t)) hGrid).trans hRestr
  have hChart := oldContentEFRestrictionLinear_tensor D Sc cutoff ν i N s t g b
  have hOld := oldMatrixMateCoendLinear_tensor D Sc cutoff i (BalancedInduction.induced Q₁ N)
    s.obj t.obj g (BalancedInduction.tensor Q₁ N.toFunctor ((J₀).obj s)
      (𝟙 ((J).obj s.obj)) b)
  have hRightStep := congrArg (oldMatrixMateCoendLinear D Sc cutoff i
    (BalancedInduction.induced Q₁ N) t.obj) hChart
  set_option backward.dsimp.instances true in
    dsimp only [BalancedInduction.restriction, Superfunctor.comp] at hRightStep hOld
  have hRight := hRightStep.trans hOld
  have hNeg : BalancedInduction.inductionInsertedTensor Q₁ J N ((J₀).obj s) ((J₁).obj t).obj
      (-(oldContentEqualCross D Sc cutoff ν i s ≫
        twist k (D.parity i * D.parity i) ((J₁).map g))) b =
      -BalancedInduction.tensor J (BalancedInduction.induced Q₁ N).toFunctor
        ((J).obj s.obj)
        (equalCrossComponent D Sc cutoff i s.obj ≫
          twist k (D.parity i) ((J).map g))
        (BalancedInduction.tensor Q₁ N.toFunctor ((J₀).obj s) (𝟙 ((J).obj s.obj)) b) := by
    change BalancedInduction.tensor J (BalancedInduction.induced Q₁ N).toFunctor
      ((J).obj s.obj)
      (-(equalCrossComponent D Sc cutoff i s.obj ≫
        twist k (D.parity i * D.parity i) ((J).map g)))
      (BalancedInduction.tensor Q₁ N.toFunctor ((J₀).obj s) (𝟙 ((J).obj s.obj)) b) = _
    rw [SKM.zmod2_mul_self]
    have hn := BalancedInduction.tensor_neg_left J (BalancedInduction.induced Q₁ N)
      ((J).obj s.obj) ((J).obj t.obj)
      (equalCrossComponent D Sc cutoff i s.obj ≫
        twist k (D.parity i) ((J).map g))
      (BalancedInduction.tensor Q₁ N.toFunctor ((J₀).obj s) (𝟙 ((J).obj s.obj)) b)
    exact hn
  unfold BalancedInduction.inductionInsertedTensor at hLeft
  change BalancedInduction.tensor J (BalancedInduction.induced Q₁ N).toFunctor
    ((J).obj s.obj)
    (-(equalCrossComponent D Sc cutoff i s.obj ≫
      twist k (D.parity i * D.parity i) ((J).map g)))
    (BalancedInduction.tensor Q₁ N.toFunctor ((J₀).obj s) (𝟙 ((J).obj s.obj)) b) =
    -BalancedInduction.tensor J (BalancedInduction.induced Q₁ N).toFunctor
      ((J).obj s.obj)
      (equalCrossComponent D Sc cutoff i s.obj ≫ twist k (D.parity i) ((J).map g))
      (BalancedInduction.tensor Q₁ N.toFunctor ((J₀).obj s) (𝟙 ((J).obj s.obj)) b) at hNeg
  have hResult := hLeft.trans (hNeg.trans hRight.symm)
  set_option backward.dsimp.instances true in
    dsimp only [BalancedInduction.restriction, Superfunctor.comp] at hResult ⊢
  exact hResult

/-- The selected content E/F charts carry the given signed cup-crossing-cap
to the literal first entry of the old unit and cap matrices. -/
theorem oldContentAppendRestrictionLinear_mate_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (J).obj s.obj ⟶ t.obj) (b : N.obj ((J₀).obj s)) :
    oldContentAppendRestrictionLinear D Sc cutoff (i :: ν) i N ((J₁).obj t)
      (BalancedInduction.orderedGridMateLinear J₀ J₁
        (oldContentEqualCross_supernatural D Sc cutoff ν i) N t
        (BalancedInduction.tensor J₀ ((Fc).obj N).toFunctor s g b)) =
    (matrixMateComponent D Sc cutoff i (BalancedInduction.induced Q₁ N)).total t.obj
      (oldContentEFRestrictionLinear D Sc cutoff ν i N t
        (BalancedInduction.tensor J₀ ((Fc).obj N).toFunctor s g b)) := by
  have hCore := oldContentAppendRestrictionLinear_mate_coend_tensor D Sc cutoff ν i N s t g b
  have hActual := oldMatrixMateCoendLinear_apply D Sc cutoff i
    (BalancedInduction.induced Q₁ N) t.obj
    (oldContentEFRestrictionLinear D Sc cutoff ν i N t
      (BalancedInduction.tensor J₀ ((Fc).obj N).toFunctor s g b))
  exact hCore.trans hActual

end OddMath.QuiverHecke.ELVOld
