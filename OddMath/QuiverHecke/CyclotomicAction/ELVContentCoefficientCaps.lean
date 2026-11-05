import OddMath.QuiverHecke.CyclotomicAction.ELVContentCoefficientMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVContentEFComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentComparisonParity

/-! # Inverse-defined coefficient caps on native content modules

The probe left-cap normalization in `SwappedVacuumNonpositiveBubbles.md`,
§2, uses the chosen F/E chart, a prescribed inverse unit-matrix coefficient,
and the inverse fully faithful inclusion unit. These compose to module
maps from native F/E back to the original module. Input-module family
naturality and the final swapped mixed slide remain separate obligations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
  (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
local notation "K" => oldContentAppend D Sc cutoff ν i
local notation "Q" => oldContentInclusion D Sc cutoff ν

/-- The inverse coefficient cap on the native F/E module. All three maps
are the previously selected comparison, inverse row and inclusion inverse. -/
def contentCoefficientCap
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (ν : Multiset I))) :
    (restriction K).obj ((induction K).obj N) ⟶ N :=
  ((oldContentFERestrictionNaturalIso D Sc cutoff ν i).app N).hom ≫
    contentUnitCoefficientMap D Sc cutoff (induced Q N) i ν hh r ≫
      (oldContentExtensionUnitIso D Sc cutoff ν N).inv

/-- The selected charts and inclusion inverse are even, so the native
coefficient cap retains exactly the inverse row's degree r*p. -/
theorem contentCoefficientCap_mem
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (ν : Multiset I))) :
    contentCoefficientCap D Sc cutoff ν i N hh r ∈ parity (R := k) _ _ (r.val • D.parity i) := by
  have he := oldContentFERestrictionNaturalIso_hom_mem D Sc cutoff ν i N
  change ((oldContentFERestrictionNaturalIso D Sc cutoff ν i).app N).hom ∈
    parity (R := k) ((restriction K).obj ((induction K).obj N)) _ 0 at he
  have hc := contentUnitCoefficientMap_mem D Sc cutoff (induced Q N) i ν hh r
  have hf := inv_mem (oldContentExtensionUnitIso D Sc cutoff ν N)
    (oldContentExtensionUnitIso_hom_mem D Sc cutoff ν N)
  simpa only [contentCoefficientCap, zero_add, add_zero] using comp_mem he (comp_mem hc hf)

/-- Exact total linear map of the native cap, in the selected value and
F/E coordinates. This is the operator chain used in scalar comparison. -/
theorem contentCoefficientCap_total
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (ν : Multiset I)))
    (t : OldContentCategory D Sc cutoff ν) :
    (contentCoefficientCap D Sc cutoff ν i N hh r).total t =
      (moduleIsoLinearEquiv (oldContentExtensionUnitIso D Sc cutoff ν N) t).symm.toLinearMap.comp
        (((contentUnitCoefficientMap D Sc cutoff (induced Q N) i ν hh r).total t).comp
          (moduleIsoLinearEquiv ((oldContentFERestrictionNaturalIso D Sc cutoff ν i).app N) t).toLinearMap) := by
  simp only [contentCoefficientCap, Superfunctor.comp_total]
  rfl

end OddMath.QuiverHecke.ELVOld
