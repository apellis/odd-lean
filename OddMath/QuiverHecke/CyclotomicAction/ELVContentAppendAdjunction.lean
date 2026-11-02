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

private theorem counit_zeroComponent
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (N : Superfunctor k A (SVec k)) (w : A)
    (z : Obj J ((restriction J).obj N).toFunctor w) :
    ((adjunctionCounit J).app N).app 0 w z = restrictionCounitLinear J N w z := rfl
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

/-- The chosen content comparison followed by the prescribed old counit,
with both nested coend carriers fixed. -/
def oldContentCounitComparisonLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (oldContentInclusion D Sc cutoff (i :: ν))
      (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N)).toFunctor w →ₗ[k]
      BalancedInduction.Obj (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor w :=
    restrictionCounitLinear (append D Sc cutoff i)
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N) w ∘ₗ
      BalancedInduction.mapComponent (append D Sc cutoff i)
        (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom 0 w ∘ₗ
      oldContentAppendExtensionLinear D Sc cutoff ν i
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N) w

/-- The prescribed content counit extended by the actual inclusion. -/
def oldContentInducedCounitLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (oldContentInclusion D Sc cutoff (i :: ν))
      (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N)).toFunctor w →ₗ[k]
      BalancedInduction.Obj (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor w :=
    BalancedInduction.mapComponent (oldContentInclusion D Sc cutoff (i :: ν))
      ((BalancedInduction.adjunctionCounit (oldContentAppend D Sc cutoff ν i)).app N) 0 w

/-- On every nested generator, the selected append extension and restriction
extension carry the ordinary content cap to the ordinary old cap. -/
theorem oldContentAppendExtensionIso_counit_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν)) (w : OldCategory D Sc cutoff)
    (h : t.obj ⟶ w) (g : (append D Sc cutoff i).obj s.obj ⟶ t.obj)
    (b : N.obj ((oldContentAppend D Sc cutoff ν i).obj s)) :
    oldContentCounitComparisonLinear D Sc cutoff ν i N w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i)
          ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N)).toFunctor
        t h (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i)
          ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor s g b)) =
    oldContentInducedCounitLinear D Sc cutoff ν i N w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i)
          ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N)).toFunctor
        t h (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i)
          ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor s g b)) := by
  simp only [oldContentCounitComparisonLinear, oldContentInducedCounitLinear,
    LinearMap.comp_apply]
  rw [oldContentAppendExtensionLinear_tensor]
  unfold BalancedInduction.inductionInsertedTensor
  rw [BalancedInduction.mapComponent_tensor, twist_zero]
  have hf := oldContentRestrictionExtensionComponent_zero D Sc cutoff ν i N s.obj
  have hs := oldContentRestrictionExtensionLinear_tensor D Sc cutoff ν i N s.obj s (𝟙 _) b
  have hx : (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom.app 0 s.obj
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor
        s (𝟙 _) b) =
      BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((oldContentAppend D Sc cutoff ν i).obj s) (𝟙 _) b := by
    change oldContentRestrictionExtensionComponent D Sc cutoff ν i 0 N s.obj _ = _
    rw [hf]
    exact hs.trans (congrArg (fun a => BalancedInduction.tensor
      (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
      ((oldContentAppend D Sc cutoff ν i).obj s) a b) ((append D Sc cutoff i).map_id s.obj))
  refine (congrArg (fun z => restrictionCounitLinear (append D Sc cutoff i)
    (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N) w
    (BalancedInduction.tensor (append D Sc cutoff i)
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)).toFunctor
      s.obj (g ≫ h) z)) hx).trans ?_
  rw [restrictionCounitLinear_tensor]
  have hp := BalancedInduction.postcompose_tensor
    (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor (g ≫ h)
    ((oldContentAppend D Sc cutoff ν i).obj s) (𝟙 ((append D Sc cutoff i).obj s.obj)) b
  have hid := congrArg (fun a : (append D Sc cutoff i).obj s.obj ⟶ w =>
    BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
      ((oldContentAppend D Sc cutoff ν i).obj s) a b) (Category.id_comp (g ≫ h))
  refine (hp.trans hid).trans ?_
  have hr := BalancedInduction.mapComponent_tensor
    (oldContentInclusion D Sc cutoff (i :: ν))
    ((BalancedInduction.adjunctionCounit (oldContentAppend D Sc cutoff ν i)).app N)
    0 w t h (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i)
      ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor s g b)
  have he := BalancedInduction.counit_zeroComponent (oldContentAppend D Sc cutoff ν i)
    N t (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i)
      ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor s g b)
  have hc := restrictionCounitLinear_tensor (oldContentAppend D Sc cutoff ν i) N s t g b
  have hright := hr.trans (congrArg₂
    (fun a z => BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
      N.toFunctor t a z) (twist_zero h) (he.trans hc))
  have hb := BalancedInduction.balance (oldContentInclusion D Sc cutoff (i :: ν))
    N.toFunctor (show (oldContentAppend D Sc cutoff ν i).obj s ⟶ t from g) h b
  have hmap : (oldContentInclusion D Sc cutoff (i :: ν)).map
      (show (oldContentAppend D Sc cutoff ν i).obj s ⟶ t from g) = g := rfl
  have ha := congrArg (fun a : (append D Sc cutoff i).obj s.obj ⟶ t.obj => a ≫ h) hmap
  have ht := congrArg (fun a : (append D Sc cutoff i).obj s.obj ⟶ w =>
    BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
      ((oldContentAppend D Sc cutoff ν i).obj s) a b) ha
  have hresult := (ht.symm.trans hb).trans hright.symm
  exact hresult

/-- The whole chosen content-extension square preserves the ordinary counit. -/
theorem oldContentAppendExtensionIso_counit
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) :
    oldContentCounitComparisonLinear D Sc cutoff ν i N w =
      oldContentInducedCounitLinear D Sc cutoff ν i N w := by
  apply BalancedInduction.nested_hom_ext (oldContentAppend D Sc cutoff ν i)
    (oldContentInclusion D Sc cutoff (i :: ν))
    ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N) w
  intro s t h g b
  exact oldContentAppendExtensionIso_counit_tensor D Sc cutoff ν i N s t w h g b

end OddMath.QuiverHecke.ELVOld
