import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionWhiskering

/-! # The chosen dot under full-content extension

The content E/F comparison in DeformedActionAssembly §5 must preserve the
chosen generators before the old-category inverse matrices are transported.
Here the existing old append dot restricts to the old content category, and
the canonical append-extension comparison intertwines its induced operator
with the prescribed old induction dot. All coefficient twists are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)

/-- The literal old append dot, restricted to its full content category. -/
def oldContentAppendDot (s : OldContentCategory D Sc cutoff ν) :
    (oldContentAppend D Sc cutoff ν i).obj s ⟶
      (oldContentAppend D Sc cutoff ν i).obj s :=
  oldAppendDotComponent D Sc cutoff i s.obj

theorem oldContentAppendDot_supernatural :
    IsSupernatural k (D.parity i) (oldContentAppendDot D Sc cutoff ν i) where
  mem s := (oldAppendDot_supernatural D Sc cutoff i).mem s.obj
  naturality := by
    intro s t p f hf
    exact (oldAppendDot_supernatural D Sc cutoff i).naturality hf

/-- The induced chosen dot on the old content module category. -/
def oldContentInductionDotComponent
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M ⟶
      BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M :=
  BalancedInduction.transformComponent (oldContentAppendDot_supernatural D Sc cutoff ν i) M

/-- The literal linear component of the chosen comparison, with both raw
coend carriers fixed before inserting its operator maps. -/
def oldContentAppendExtensionLinear
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor w →ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i)
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M).toFunctor w :=
  ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M).total w

/-- The chosen comparison's tensor formula in the fixed raw coend carriers. -/
theorem oldContentAppendExtensionLinear_tensor
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν)) (w : OldCategory D Sc cutoff)
    (h : t.obj ⟶ w)
    (g : (append D Sc cutoff i).obj s.obj ⟶ t.obj) (b : M.obj s) :
    oldContentAppendExtensionLinear D Sc cutoff ν i M w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor
        t h (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i)
          M.toFunctor s g b)) =
      BalancedInduction.inductionInsertedTensor (oldContentInclusion D Sc cutoff ν)
        (append D Sc cutoff i) M s w (g ≫ h) b := by
  exact oldContentAppendExtensionIso_tensor D Sc cutoff ν i M s t w h g b

/-- On every nested generator, the chosen comparison keeps the full twist
from the inner dot and the outer induction map. -/
theorem oldContentAppendExtensionIso_dot_tensor
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν)) (w : OldCategory D Sc cutoff)
    (h : t.obj ⟶ w)
    (g : (oldContentAppend D Sc cutoff ν i).obj s ⟶ t) (b : M.obj s) :
    oldContentAppendExtensionLinear D Sc cutoff ν i M w
      (BalancedInduction.mapComponent (oldContentInclusion D Sc cutoff (i :: ν))
        (oldContentInductionDotComponent D Sc cutoff ν i M) (D.parity i) w
        (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
          (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor
          t h (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i)
            M.toFunctor s g b))) =
    actualInductionDot D Sc cutoff i
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M) w
      (oldContentAppendExtensionLinear D Sc cutoff ν i M w
        (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
          (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor
          t h (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i)
            M.toFunctor s g b))) := by
  rw [BalancedInduction.mapComponent_tensor]
  simp only [oldContentInductionDotComponent, BalancedInduction.transformComponent_apply,
    ↓reduceIte, BalancedInduction.transformLinear_tensor]
  rw [oldContentAppendExtensionLinear_tensor, oldContentAppendExtensionLinear_tensor]
  unfold BalancedInduction.inductionInsertedTensor
  rw [actualInductionDot_tensor]
  apply congrArg (fun a : (append D Sc cutoff i).obj s.obj ⟶ w =>
    BalancedInduction.tensor (append D Sc cutoff i)
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M).toFunctor
      s.obj a (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν)
        M.toFunctor s (𝟙 s.obj) b))
  change (oldAppendDotComponent D Sc cutoff i s.obj ≫
      twist k (D.parity i) (show (append D Sc cutoff i).obj s.obj ⟶ t.obj from g)) ≫
      twist k (D.parity i) h =
    oldAppendDotComponent D Sc cutoff i s.obj ≫
      twist k (D.parity i)
        ((show (append D Sc cutoff i).obj s.obj ⟶ t.obj from g) ≫ h)
  rw [twist_comp, Category.assoc]

/-- The entire canonical append-extension comparison intertwines the dot
on all balanced coends, with no homogeneity hypothesis on their generators. -/
theorem oldContentAppendExtensionIso_dot
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldCategory D Sc cutoff) :
    oldContentAppendExtensionLinear D Sc cutoff ν i M w ∘ₗ
      BalancedInduction.mapComponent (oldContentInclusion D Sc cutoff (i :: ν))
        (oldContentInductionDotComponent D Sc cutoff ν i M) (D.parity i) w =
    actualInductionDot D Sc cutoff i
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M) w ∘ₗ
        oldContentAppendExtensionLinear D Sc cutoff ν i M w := by
  apply BalancedInduction.nested_hom_ext
    (oldContentAppend D Sc cutoff ν i) (oldContentInclusion D Sc cutoff (i :: ν)) M w
  intro s t h g b
  simpa only [LinearMap.comp_apply] using
    oldContentAppendExtensionIso_dot_tensor D Sc cutoff ν i M s t w h g b

end OddMath.QuiverHecke.ELVOld
