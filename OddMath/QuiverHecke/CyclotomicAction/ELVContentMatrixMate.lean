import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixCharts

/-! # The prescribed mate on entire chosen content coends

DeformedMatrixComparison (4), (5), principal matrix field. Genuine selected
E/F charts carry the independently given content cup-crossing-cap to the
literal old matrix mate on every coend vector, before finite parity shifts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
namespace BalancedInduction
private def mateLinear
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (M : Superfunctor k C (SVec k))
    (f : induced A ((restriction A).obj M) ⟶ (restriction A).obj (induced A M)) (t : C) :
    Obj A ((restriction A).obj M).toFunctor t →ₗ[k] Obj A M.toFunctor (A.obj t) := f.total t

private theorem mateLinear_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (M : Superfunctor k C (SVec k))
    (f : induced A ((restriction A).obj M) ⟶ (restriction A).obj (induced A M)) (t : C)
    (x : Obj A ((restriction A).obj M).toFunctor t) :
    mateLinear A M f t x = f.total t x := rfl

private theorem coendComp_ext
    {k C A V W Z : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    (f : Obj J M w →ₗ[k] V) (g : V →ₗ[k] Z)
    (h : Obj J M w →ₗ[k] W) (l : W →ₗ[k] Z)
    (hh : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      g (f (tensor J M s a b)) = l (h (tensor J M s a b))) : g ∘ₗ f = l ∘ₗ h := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact hh s a b
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i

private def matrixMateLinear
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    Obj J ((restriction J).obj M).toFunctor t →ₗ[k] Obj J M.toFunctor ((J).obj t) :=
  BalancedInduction.mateLinear J M (matrixMateComponent D Sc cutoff i M) t

private theorem matrixMateLinear_apply
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (x : Obj J ((restriction J).obj M).toFunctor t) :
    matrixMateLinear D Sc cutoff i M t x = (matrixMateComponent D Sc cutoff i M).total t x :=
  BalancedInduction.mateLinear_apply J M (matrixMateComponent D Sc cutoff i M) t x

private theorem mateCharts_comp
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      orderedGridMateLinear J₀ J₁ (oldContentEqualCross_supernatural D Sc cutoff ν i) N t =
    matrixMateLinear D Sc cutoff i (induced Q₁ N) t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  apply BalancedInduction.coendComp_ext J₀ ((restriction J₀).obj N).toFunctor
  intro s a b
  have h := oldContentMatrixCharts_mate_tensor D Sc cutoff ν i N s t a b
  have hm := matrixMateLinear_apply D Sc cutoff i (induced Q₁ N) t.obj
    ((oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap
      (tensor J₀ ((restriction J₀).obj N).toFunctor s a b))
  exact h.trans hm.symm

/-- The given principal mate field through the genuine chosen charts,
on every vector of the entire balanced source. -/
theorem oldContentMatrixCharts_mate
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (x : Obj J₀ ((restriction J₀).obj N).toFunctor t) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap
      (orderedGridMateLinear J₀ J₁ (oldContentEqualCross_supernatural D Sc cutoff ν i) N t x) =
    (matrixMateComponent D Sc cutoff i (induced Q₁ N)).total t.obj
      ((oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap x) := by
  have h := LinearMap.congr_fun (mateCharts_comp D Sc cutoff ν i N t) x
  have hm := matrixMateLinear_apply D Sc cutoff i (induced Q₁ N) t.obj
    ((oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap x)
  dsimp only [LinearMap.comp_apply] at h
  exact h.trans hm

end OddMath.QuiverHecke.ELVOld
