import OddMath.QuiverHecke.CyclotomicAction.ELVContentExtensionAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVContentRestrictionTensor

/-! # Canonical content induction comparison on quotient generators

The induction and restriction extension comparisons use the same literal
append/inclusion square. Their tensor formulas support the adjunction-map
comparison in SwappedVacuumCoordinates §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : B ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

private def compInsertion (M : Superfunctor k C (SVec k)) :
    induced (J ⋙ K) M ⟶ induced K (induced J M) := (inductionComp J K).inv.app M

/-- A nested generator with its actual induced superspace endpoint fixed. -/
def inductionInsertedTensor (M : Superfunctor k C (SVec k))
    (s : C) (w : E) (a : K.obj (J.obj s) ⟶ w) (b : M.obj s) :
    (induced K (induced J M)).obj w :=
  tensor K (induced J M).toFunctor (J.obj s) a
    (tensor J M.toFunctor s (𝟙 _) b)

private theorem compInsertion_tensor (M : Superfunctor k C (SVec k))
    (s : C) (w : E) (a : K.obj (J.obj s) ⟶ w) (b : M.obj s) :
    (compInsertion J K M).total w (tensor (J ⋙ K) M.toFunctor s a b) =
      inductionInsertedTensor J K M s w a b := inductionComp_inv_total_tensor J K M s w a b

private def compInsertionLinear (M : Superfunctor k C (SVec k)) (w : E) :
    Obj (J ⋙ K) M.toFunctor w →ₗ[k] Obj K (induced J M).toFunctor w :=
  SVec.toLinearMap ((compInsertion J K M).total w)

private theorem compInsertionLinear_tensor (M : Superfunctor k C (SVec k))
    (s : C) (w : E) (a : K.obj (J.obj s) ⟶ w) (b : M.obj s) :
    compInsertionLinear J K M w (tensor (J ⋙ K) M.toFunctor s a b) =
      inductionInsertedTensor J K M s w a b := compInsertion_tensor J K M s w a b

end OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem oldContentAppendExtensionIso_hom (ν : List I) (i : I)
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M =
      (BalancedInduction.inductionComp (oldContentAppend D Sc cutoff ν i)
        (oldContentInclusion D Sc cutoff (i :: ν))).hom.app M ≫
      (BalancedInduction.inductionComp (oldContentInclusion D Sc cutoff ν)
        (append D Sc cutoff i)).inv.app M := by
  have hm : (BalancedInduction.inductionFunctorIsoOfEq
      (oldContentAppend D Sc cutoff ν i ⋙ oldContentInclusion D Sc cutoff (i :: ν))
      (oldContentInclusion D Sc cutoff ν ⋙ append D Sc cutoff i)
      (oldContentAppend_inclusion D Sc cutoff ν i)).hom.app M = 𝟙 _ := rfl
  simp only [oldContentAppendExtensionIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, hm, Category.id_comp]

private theorem oldContentAppendExtensionIso_flatten (ν : List I) (i : I)
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν)) (w : OldCategory D Sc cutoff)
    (h : t.obj ⟶ w)
    (g : (append D Sc cutoff i).obj s.obj ⟶ t.obj) (b : M.obj s) :
    ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M).total w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor t h
        (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i) M.toFunctor s g b)) =
      BalancedInduction.compInsertionLinear (oldContentInclusion D Sc cutoff ν)
        (append D Sc cutoff i) M w
        (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν ⋙ append D Sc cutoff i)
          M.toFunctor s (g ≫ h) b) := by
  rw [oldContentAppendExtensionIso_hom, Superfunctor.comp_total]
  change BalancedInduction.compInsertionLinear (oldContentInclusion D Sc cutoff ν)
      (append D Sc cutoff i) M w
      (((BalancedInduction.inductionComp (oldContentAppend D Sc cutoff ν i)
        (oldContentInclusion D Sc cutoff (i :: ν))).hom.app M).total w
        (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
          (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor t h
          (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i) M.toFunctor s g b))) = _
  have hf := BalancedInduction.inductionComp_hom_total_tensor
    (oldContentAppend D Sc cutoff ν i) (oldContentInclusion D Sc cutoff (i :: ν)) M s t w h g b
  change ((BalancedInduction.inductionComp (oldContentAppend D Sc cutoff ν i)
    (oldContentInclusion D Sc cutoff (i :: ν))).hom.app M).total w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor t h
        (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i) M.toFunctor s g b)) =
    BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν ⋙ append D Sc cutoff i)
      M.toFunctor s (g ≫ h) b at hf
  exact congrArg (BalancedInduction.compInsertionLinear
    (oldContentInclusion D Sc cutoff ν) (append D Sc cutoff i) M w) hf

private theorem oldContentAppendInsertion_tensor (ν : List I) (i : I)
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (w : OldCategory D Sc cutoff)
    (a : (append D Sc cutoff i).obj s.obj ⟶ w) (b : M.obj s) :
    BalancedInduction.compInsertionLinear (oldContentInclusion D Sc cutoff ν)
      (append D Sc cutoff i) M w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν ⋙ append D Sc cutoff i)
        M.toFunctor s a b) =
    BalancedInduction.inductionInsertedTensor (oldContentInclusion D Sc cutoff ν)
      (append D Sc cutoff i) M s w a b := by
  exact BalancedInduction.compInsertionLinear_tensor
    (oldContentInclusion D Sc cutoff ν) (append D Sc cutoff i) M s w a b

theorem oldContentAppendExtensionIso_tensor (ν : List I) (i : I)
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν)) (w : OldCategory D Sc cutoff)
    (h : t.obj ⟶ w)
    (g : (append D Sc cutoff i).obj s.obj ⟶ t.obj) (b : M.obj s) :
    ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M).total w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor t h
        (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i) M.toFunctor s g b)) =
      BalancedInduction.inductionInsertedTensor (oldContentInclusion D Sc cutoff ν)
        (append D Sc cutoff i) M s w
        (g ≫ h) b := by
  have hf := oldContentAppendExtensionIso_flatten D Sc cutoff ν i M s t w h g b
  have hi := oldContentAppendInsertion_tensor D Sc cutoff ν i M s w (g ≫ h) b
  exact hf.trans hi

end OddMath.QuiverHecke.ELVOld
