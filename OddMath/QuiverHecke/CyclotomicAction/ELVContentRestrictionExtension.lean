import OddMath.QuiverHecke.CyclotomicAction.ELVContentSupportedExtension

/-! # Restriction and canonical old-content extension

The literal append/inclusion square and the supported inclusion counit give
an actual supermodule comparison for restriction, alongside the induction
comparison. The support argument uses full coefficients and no flatness.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem oldAppendRestriction_supported (ν : List I) (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff (i :: ν) N) :
    OldContentSupported D Sc cutoff ν
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj N) := by
  intro w hw
  apply hN ((append D Sc cutoff i).obj w)
  intro he
  apply hw
  change (w.word : Multiset I) + ([i] : Multiset I) =
    ([i] : Multiset I) + (ν : Multiset I) at he
  rw [add_comm ([i] : Multiset I)] at he
  exact add_right_cancel he

/-- The two restrictions in the append/inclusion square agree literally. -/
def oldContentRestrictionSquare (ν : List I) (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj
      ((BalancedInduction.restriction (oldContentInclusion D Sc cutoff (i :: ν))).obj N) ≅
    (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj N) := Iso.refl _

/-- Extending fixed-content restriction is canonically old restriction of the
canonical extension. The map is built from the actual inclusion unit/counit. -/
def oldContentRestrictionExtensionIso (ν : List I) (i : I)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    BalancedInduction.induced (oldContentInclusion D Sc cutoff ν)
      ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N) ≅
    (BalancedInduction.restriction (append D Sc cutoff i)).obj
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N) :=
  (BalancedInduction.induction (oldContentInclusion D Sc cutoff ν)).mapIso
    ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).mapIso
      (oldContentExtensionUnitIso D Sc cutoff (i :: ν) N) ≪≫
      oldContentRestrictionSquare D Sc cutoff ν i
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)) ≪≫
    supportedContentCounitIso D Sc cutoff ν _
      (oldAppendRestriction_supported D Sc cutoff ν i _
        (oldContentExtension_supported D Sc cutoff (i :: ν) N))

end OddMath.QuiverHecke.ELVOld
