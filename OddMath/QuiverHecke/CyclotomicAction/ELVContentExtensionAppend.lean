import OddMath.QuiverHecke.CyclotomicAction.ELVFullyFaithfulInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedInductionNaturality

/-! # Append and full-content extension

The literal append/inclusion square gives the induction comparison required
for the content-module realization in SwappedVacuumCoordinates §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (ν : List I) (i : I)

/-- Induce append inside the content block then extend, or extend then use
the established old append. The comparison is natural on all module maps. -/
def oldContentAppendExtensionIso :
    BalancedInduction.induction (k := k) (oldContentAppend D Sc cutoff ν i) ⋙
        BalancedInduction.induction (oldContentInclusion D Sc cutoff (i :: ν)) ≅
      BalancedInduction.induction (oldContentInclusion D Sc cutoff ν) ⋙
        BalancedInduction.induction (CyclotomicCrossingTensor.append D Sc cutoff i) :=
  BalancedInduction.inductionComp (oldContentAppend D Sc cutoff ν i)
      (oldContentInclusion D Sc cutoff (i :: ν)) ≪≫
    BalancedInduction.inductionFunctorIsoOfEq _ _
      (oldContentAppend_inclusion D Sc cutoff ν i) ≪≫
    (BalancedInduction.inductionComp (oldContentInclusion D Sc cutoff ν)
      (CyclotomicCrossingTensor.append D Sc cutoff i)).symm

/-- Restricting old append of the canonical extension recovers content append. -/
def oldContentAppendRestrictionIso
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M ≅
      (BalancedInduction.restriction (oldContentInclusion D Sc cutoff (i :: ν))).obj
        (BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc cutoff i)
          (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M)) :=
  oldContentExtensionUnitIso D Sc cutoff (i :: ν)
      (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M) ≪≫
    (BalancedInduction.restriction (oldContentInclusion D Sc cutoff (i :: ν))).mapIso
      ((oldContentAppendExtensionIso D Sc cutoff ν i).app M)

end OddMath.QuiverHecke.ELVOld
