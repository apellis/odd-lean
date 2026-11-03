import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendMate
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations

/-! # Invertible component charts for the chosen content matrices

DeformedMatrixComparison (2), (4) transports the prescribed finite matrices
through the selected preceding and following E/F comparisons. These are
linear equivalences obtained from the given module isomorphisms, without
an invertibility hypothesis on any comparison map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
namespace BalancedInduction
private theorem restriction_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (t : C)
    (z : ((restriction Q).obj M).obj t) :
    ((restriction Q).map f).total t z = f.total (Q.obj t) z := rfl
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i

/-- The actual preceding E/F chart is a linear equivalence on its full coend. -/
def oldContentEFLinearEquiv
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor t ≃ₗ[k]
      BalancedInduction.Obj J ((BalancedInduction.restriction J).obj
        (BalancedInduction.induced Q₁ N)).toFunctor t.obj :=
  moduleIsoLinearEquiv ((oldContentEFRestrictionNaturalIso D Sc cutoff ν i).app N) t

/-- Its forward map is exactly the selected chart used in the mate comparison. -/
theorem oldContentEFLinearEquiv_hom
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap =
      oldContentEFRestrictionLinear D Sc cutoff ν i N t := rfl

/-- The actual following F/E chart is a linear equivalence on the full coend. -/
def oldContentFELinearEquiv
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj J₁ N.toFunctor ((J₁).obj t) ≃ₗ[k]
      BalancedInduction.Obj J (BalancedInduction.induced Q₁ N).toFunctor ((J).obj t.obj) :=
  moduleIsoLinearEquiv ((oldContentFERestrictionNaturalIso D Sc cutoff (i :: ν) i).app N) t

/-- The value summand uses precisely the fully faithful inclusion unit. -/
def oldContentValueLinearEquiv
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    N.obj t ≃ₗ[k] BalancedInduction.Obj Q₁ N.toFunctor t.obj :=
  moduleIsoLinearEquiv (oldContentExtensionUnitIso D Sc cutoff (i :: ν) N) t

/-- The following-composite equivalence is the very same selected map
appearing on the output side of the prescribed mate tensor square. -/
theorem oldContentFELinearEquiv_apply
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (z : BalancedInduction.Obj J₁ N.toFunctor ((J₁).obj t)) :
    oldContentFELinearEquiv D Sc cutoff ν i N t z =
      oldContentAppendRestrictionLinear D Sc cutoff (i :: ν) i N ((J₁).obj t) z := by
  change ((oldContentFERestrictionNaturalIso D Sc cutoff (i :: ν) i).hom.app N).total t z = _
  rw [oldContentFERestrictionNaturalIso_hom_app]
  exact BalancedInduction.restriction_total_apply J₁
    (oldContentAppendRestrictionIso D Sc cutoff (i :: ν) i N).hom t z

/-- The value equivalence inserts the literal identity tensor. -/
theorem oldContentValueLinearEquiv_apply
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) (b : N.obj t) :
    oldContentValueLinearEquiv D Sc cutoff ν i N t b =
      BalancedInduction.tensor Q₁ N.toFunctor t (𝟙 t.obj) b := by
  change (BalancedInduction.fullyFaithfulUnitIso Q₁ N).hom.total t b = _
  rw [BalancedInduction.fullyFaithfulUnitIso_hom]
  exact BalancedInduction.unit_total_apply Q₁ N t b

/-- The genuine source and target charts carry the prescribed content mate
to the literal first old matrix entry on every balanced generator. -/
theorem oldContentMatrixCharts_mate_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (J).obj s.obj ⟶ t.obj) (b : N.obj ((J₀).obj s)) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap
      (BalancedInduction.orderedGridMateLinear J₀ J₁
        (oldContentEqualCross_supernatural D Sc cutoff ν i) N t
        (BalancedInduction.tensor J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor s g b)) =
    (matrixMateComponent D Sc cutoff i (BalancedInduction.induced Q₁ N)).total t.obj
      ((oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap
        (BalancedInduction.tensor J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor s g b)) := by
  rw [oldContentEFLinearEquiv_hom]
  have he := oldContentFELinearEquiv_apply D Sc cutoff ν i N t
    (BalancedInduction.orderedGridMateLinear J₀ J₁
      (oldContentEqualCross_supernatural D Sc cutoff ν i) N t
      (BalancedInduction.tensor J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor s g b))
  have hm := oldContentAppendRestrictionLinear_mate_tensor D Sc cutoff ν i N s t g b
  exact he.trans hm

end OddMath.QuiverHecke.ELVOld
