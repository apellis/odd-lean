import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendRestrictionDot
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendAdjunction

/-! # The ordinary adjunction under old-content extension

The chosen full-content append comparisons in SwappedVacuumCoordinates §6
must preserve the prescribed cup and cap before the same-colour matrix
inverse can be attached to the content E/F functors. These are comparisons
of the existing units and counits, on every input module and every vector.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
namespace BalancedInduction
private theorem even_comp_app_one
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M L N : Superfunctor k C (SVec k)} (f : M ⟶ L) (g : L ⟶ N)
    (hf : f ∈ parity (R := k) _ _ 0) (hg : g ∈ parity (R := k) _ _ 0) (v : C) :
    (f ≫ g).app 1 v = 0 :=
  Superfunctor.app_eq_zero_of_mem (comp_mem hf hg) (by decide) v

end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)

/-- The selected append-restriction comparison sends the actual content
unit to the old append unit on the actual inclusion unit. -/
theorem oldContentAppendRestrictionIso_unit
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (b : M.obj s) :
    oldContentAppendRestrictionLinear D Sc cutoff ν i M
      ((oldContentAppend D Sc cutoff ν i).obj s)
      (BalancedInduction.unit (oldContentAppend D Sc cutoff ν i) M.toFunctor s b) =
    BalancedInduction.unit (append D Sc cutoff i)
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M).toFunctor s.obj
      (BalancedInduction.unit (oldContentInclusion D Sc cutoff ν) M.toFunctor s b) := by
  rw [oldContentAppendRestrictionLinear_eq, LinearMap.comp_apply]
  have hu : oldContentAppendInclusionUnitLinear D Sc cutoff ν i M
      ((oldContentAppend D Sc cutoff ν i).obj s)
      (BalancedInduction.unit (oldContentAppend D Sc cutoff ν i) M.toFunctor s b) =
      BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor
        ((oldContentAppend D Sc cutoff ν i).obj s) (𝟙 ((append D Sc cutoff i).obj s.obj))
        (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i) M.toFunctor s
          (𝟙 ((append D Sc cutoff i).obj s.obj)) b) := rfl
  rw [hu, oldContentAppendExtensionLinear_tensor]
  exact congrArg (fun a : (append D Sc cutoff i).obj s.obj ⟶
      (append D Sc cutoff i).obj s.obj =>
      BalancedInduction.inductionInsertedTensor (oldContentInclusion D Sc cutoff ν)
        (append D Sc cutoff i) M s ((append D Sc cutoff i).obj s.obj) a b)
    (Category.id_comp (𝟙 ((append D Sc cutoff i).obj s.obj)))

/-- The chosen comparison for content restriction, on its literal coend carriers. -/
def oldContentRestrictionExtensionLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor w →ₗ[k]
      BalancedInduction.Obj (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((append D Sc cutoff i).obj w) :=
  (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom.total w

/-- Restriction extension uses the original arrow with the same append functor. -/
theorem oldContentRestrictionExtensionLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) (s : OldContentCategory D Sc cutoff ν)
    (g : s.obj ⟶ w) (b : N.obj ((oldContentAppend D Sc cutoff ν i).obj s)) :
    oldContentRestrictionExtensionLinear D Sc cutoff ν i N w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor
        s g b) =
      BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((oldContentAppend D Sc cutoff ν i).obj s) ((append D Sc cutoff i).map g) b := by
  exact oldContentRestrictionExtensionIso_tensor D Sc cutoff ν i N w s g b

/-- Homogeneous components of the selected restriction extension on its raw coends. -/
def oldContentRestrictionExtensionComponent (p : ZMod 2)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor w →ₗ[k]
      BalancedInduction.Obj (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((append D Sc cutoff i).obj w) :=
  (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom.app p w

/-- The chosen restriction comparison has zero odd component. -/
theorem oldContentRestrictionExtensionComponent_one
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) :
    oldContentRestrictionExtensionComponent D Sc cutoff ν i 1 N w = 0 := by
  have hu := BalancedInduction.adjunctionUnit_mem
    (oldContentInclusion D Sc cutoff (i :: ν)) N
  have hr := map_mem (BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)) hu
  have hi := map_mem (BalancedInduction.induction (oldContentInclusion D Sc cutoff ν)) hr
  have hc := BalancedInduction.adjunctionCounit_mem (oldContentInclusion D Sc cutoff ν)
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N))
  have hz := BalancedInduction.even_comp_app_one _ _ hi hc w
  have he := congrArg (fun f => f.app 1 w)
    (oldContentRestrictionExtensionIso_hom D Sc cutoff ν i N)
  exact he.trans hz

/-- Its degree-zero component is its whole selected map. -/
theorem oldContentRestrictionExtensionComponent_zero
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) :
    oldContentRestrictionExtensionComponent D Sc cutoff ν i 0 N w =
      oldContentRestrictionExtensionLinear D Sc cutoff ν i N w := by
  have hz := oldContentRestrictionExtensionComponent_one D Sc cutoff ν i N w
  change oldContentRestrictionExtensionComponent D Sc cutoff ν i 0 N w =
    oldContentRestrictionExtensionComponent D Sc cutoff ν i 0 N w +
      oldContentRestrictionExtensionComponent D Sc cutoff ν i 1 N w
  rw [hz, add_zero]

end OddMath.QuiverHecke.ELVOld
