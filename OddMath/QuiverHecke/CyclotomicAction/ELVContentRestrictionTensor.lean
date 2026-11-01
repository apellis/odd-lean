import OddMath.QuiverHecke.CyclotomicAction.ELVContentRestrictionExtension

/-! # Generator formula for the content restriction comparison

The canonical inclusion unit/counit comparison sends [g ⊗ b] to
[append(g) ⊗ b]. This is the restriction-side map needed to compare the
fixed-content action generators in SwappedVacuumCoordinates §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C E : Type u} [Category.{u} C] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ E) [J.Additive] [J.Linear k] [IsSuperfunctor k J]

theorem unit_total_apply (M : Superfunctor k C (SVec k)) (v : C) (b : M.obj v) :
    ((adjunctionUnit J).app M).total v b = unit J M.toFunctor v b := by
  simp only [adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

theorem counit_total_apply (N : Superfunctor k E (SVec k)) (w : E)
    (z : Obj J (J ⋙ N.toFunctor) w) :
    ((adjunctionCounit J).app N).total w z = counit J N.toFunctor w z := by
  simp only [adjunctionCounit, Superfunctor.homMk, SuperNatTrans.total,
    counitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The comparison is the induction of the actual inclusion unit followed by
its actual inclusion counit; the append/inclusion restriction square is strict. -/
theorem oldContentRestrictionExtensionIso_hom (ν : List I) (i : I)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom =
      (BalancedInduction.induction (oldContentInclusion D Sc cutoff ν)).map
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).map
          ((BalancedInduction.adjunctionUnit
            (oldContentInclusion D Sc cutoff (i :: ν))).app N)) ≫
      (BalancedInduction.adjunctionCounit (oldContentInclusion D Sc cutoff ν)).app
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)) := by
  simp only [oldContentRestrictionExtensionIso, Iso.trans_hom, Functor.mapIso_hom,
    oldContentRestrictionSquare, Iso.refl_hom, Category.comp_id,
    oldContentExtensionUnitIso, BalancedInduction.fullyFaithfulUnitIso_hom,
    supportedContentCounitIso_hom]

/-- The prescribed source-arrow generator is unchanged and its old arrow is appended. -/
theorem oldContentRestrictionExtensionIso_tensor (ν : List I) (i : I)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) (s : OldContentCategory D Sc cutoff ν)
    (g : (oldContentInclusion D Sc cutoff ν).obj s ⟶ w)
    (b : N.obj ((oldContentAppend D Sc cutoff ν i).obj s)) :
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom.total w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor s g b) =
      BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((oldContentAppend D Sc cutoff ν i).obj s) ((append D Sc cutoff i).map g) b := by
  rw [oldContentRestrictionExtensionIso_hom, Superfunctor.comp_total]
  change ((BalancedInduction.adjunctionCounit (oldContentInclusion D Sc cutoff ν)).app
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N))).total w
      ((BalancedInduction.moduleMap (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).map
          ((BalancedInduction.adjunctionUnit
            (oldContentInclusion D Sc cutoff (i :: ν))).app N))).total w
        (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν)
          ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor
            s g b)) = _
  rw [BalancedInduction.counit_total_apply]
  have hm := BalancedInduction.moduleMap_total_tensor
    (oldContentInclusion D Sc cutoff ν)
    ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).map
      ((BalancedInduction.adjunctionUnit (oldContentInclusion D Sc cutoff (i :: ν))).app N))
    w s g b
  refine (congrArg (BalancedInduction.counit (oldContentInclusion D Sc cutoff ν)
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)).toFunctor w) hm).trans ?_
  change BalancedInduction.counit (oldContentInclusion D Sc cutoff ν)
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)).toFunctor w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν) _ s g
        (BalancedInduction.unit (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
          ((oldContentAppend D Sc cutoff ν i).obj s) b) +
        BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν) _ s (twist k 1 g) 0) = _
  rw [BalancedInduction.tensor_zero_right, add_zero, BalancedInduction.counit_tensor]
  change BalancedInduction.postcompose (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
      ((append D Sc cutoff i).map g)
      (BalancedInduction.unit (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((oldContentAppend D Sc cutoff ν i).obj s) b) = _
  rw [BalancedInduction.unit_apply, BalancedInduction.postcompose_tensor, Category.id_comp]

end OddMath.QuiverHecke.ELVOld
