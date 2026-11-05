import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVContentEFComparison

/-! # Parity of the selected content extension and F/E charts

SwappedVacuumCoordinates §6 and DeformedMatrixComparison (4), (5) use the
chosen content extension/restriction comparisons in the normalized cap.
Their actual module components are even, with the same selected maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u v
private theorem even_comp {k : Type u} {C : Type v} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {V W Z : C} {f : V ⟶ W} {g : W ⟶ Z}
    (hf : f ∈ parity (R := k) _ _ 0) (hg : g ∈ parity (R := k) _ _ 0) :
    f ≫ g ∈ parity (R := k) _ _ 0 := by
  simpa only [zero_add] using comp_mem hf hg

private theorem even_total {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (f : F ⟶ G)
    (hf : f ∈ parity (R := k) _ _ 0) (t : C) :
    f.total t ∈ parity (R := k) (F.obj t) (G.obj t) 0 := by
  rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) t,
    add_zero]
  exact f.app_mem 0 t
private theorem even_of_total {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (f : F ⟶ G)
    (hf : ∀ t, f.total t ∈ parity (R := k) (F.obj t) (G.obj t) 0) :
    f ∈ parity (R := k) _ _ 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext t
  have hp : proj k q (f.total t) = f.app q t := by
    rcases parity_eq_zero_or_one q with rfl | rfl
    · exact proj_eq_of_add rfl (f.app_mem 0 t) (f.app_mem 1 t)
    · exact proj_eq_of_add (add_comm _ _) (f.app_mem 1 t) (by simpa using f.app_mem 0 t)
  rw [← hp]
  exact proj_of_mem_ne (hf t) (Ne.symm hq)

namespace BalancedInduction
private theorem fullyFaithfulUnit_hom_even
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q] [Q.Full] [Q.Faithful]
    (M : Superfunctor k C (SVec k)) :
    (fullyFaithfulUnitIso Q M).hom ∈ parity (R := k) _ _ 0 := by
  rw [fullyFaithfulUnitIso_hom]
  exact adjunctionUnit_mem Q M
end BalancedInduction

private theorem restrictionComparison_hom_even
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q] [Q.Full] [Q.Faithful]
    (P : Superfunctor k C (SVec k)) (O : Superfunctor k A (SVec k))
    (f : induced Q P ≅ O) (hf : f.hom ∈ parity (R := k) _ _ 0) :
    (fullyFaithfulUnitIso Q P ≪≫ (restriction Q).mapIso f).hom ∈ parity (R := k) _ _ 0 :=
  even_comp (BalancedInduction.fullyFaithfulUnit_hom_even Q P)
    (IsSuperfunctor.map_mem (F := restriction Q) hf)

private theorem restrictionComparison_total_even
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q] [Q.Full] [Q.Faithful]
    (P : Superfunctor k C (SVec k)) (O : Superfunctor k A (SVec k))
    (f : induced Q P ≅ O) (hf : f.hom ∈ parity (R := k) _ _ 0) (t : C) :
    (fullyFaithfulUnitIso Q P ≪≫ (restriction Q).mapIso f).hom.total t ∈
      parity (R := k) (P.obj t) (O.obj (Q.obj t)) 0 :=
  even_total _ (restrictionComparison_hom_even Q P O f hf) t

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)

/-- The selected full-content extension unit is the even ordinary unit. -/
theorem oldContentExtensionUnitIso_hom_mem
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentExtensionUnitIso D Sc cutoff ν M).hom ∈ parity (R := k) _ _ 0 :=
  BalancedInduction.fullyFaithfulUnit_hom_even (oldContentInclusion D Sc cutoff ν) M

/-- The selected append/extension comparison is even on every input module. -/
theorem oldContentAppendExtensionIso_hom_mem
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M ∈ parity (R := k) _ _ 0 := by
  rw [oldContentAppendExtensionIso_hom]
  exact even_comp (inductionComp_hom_mem (oldContentAppend D Sc cutoff ν i)
    (oldContentInclusion D Sc cutoff (i :: ν)) M)
    (inductionComp_inv_mem (oldContentInclusion D Sc cutoff ν) (append D Sc cutoff i) M)

/-- The given append/restriction chart includes its actual even inclusion unit. -/
theorem oldContentAppendRestrictionIso_hom_mem
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentAppendRestrictionIso D Sc cutoff ν i M).hom ∈ parity (R := k) _ _ 0 := by
  apply even_of_total
  intro t
  exact restrictionComparison_total_even (oldContentInclusion D Sc cutoff (i :: ν))
    (induced (oldContentAppend D Sc cutoff ν i) M)
    (induced (append D Sc cutoff i) (induced (oldContentInclusion D Sc cutoff ν) M))
    ((oldContentAppendExtensionIso D Sc cutoff ν i).app M)
    (oldContentAppendExtensionIso_hom_mem D Sc cutoff ν i M) t

/-- The whole chosen F/E chart is even on arbitrary full-coefficient modules. -/
theorem oldContentFERestrictionNaturalIso_hom_mem
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentFERestrictionNaturalIso D Sc cutoff ν i).hom.app M ∈ parity (R := k) _ _ 0 := by
  rw [oldContentFERestrictionNaturalIso_hom_app]
  exact IsSuperfunctor.map_mem (F := restriction (oldContentAppend D Sc cutoff ν i))
    (oldContentAppendRestrictionIso_hom_mem D Sc cutoff ν i M)

end OddMath.QuiverHecke.ELVOld
