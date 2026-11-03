import OddMath.QuiverHecke.CyclotomicAction.ELVContentCoefficientMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVContentEFComparison

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

private theorem iso_total_surjective
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (t : C) :
    Function.Surjective (e.hom.total t) := (moduleIsoLinearEquiv e t).surjective

private theorem comp_total_surjective
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G H : Superfunctor k C (SVec k)} (f : F ⟶ G) (g : G ⟶ H) (t : C)
    (hf : Function.Surjective (f.total t)) (hg : Function.Surjective (g.total t)) :
    Function.Surjective ((f ≫ g).total t) := by
  intro v
  obtain ⟨b, hb⟩ := hg v
  obtain ⟨a, ha⟩ := hf b
  refine ⟨a, ?_⟩
  rw [Superfunctor.comp_total, SVec.comp_apply, ha, hb]

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

/-- This cap is surjective on every module value, including on the actual
regular probe; no scalar-valued coefficient extractor is assumed. -/
theorem contentCoefficientCap_total_surjective
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (ν : Multiset I)))
    (t : OldContentCategory D Sc cutoff ν) :
    Function.Surjective ((contentCoefficientCap D Sc cutoff ν i N hh r).total t) := by
  unfold contentCoefficientCap
  apply comp_total_surjective
  · exact iso_total_surjective _ _
  · apply comp_total_surjective
    · exact contentUnitCoefficientMap_total_surjective D Sc cutoff (induced Q N) i ν hh r t
    · exact iso_total_surjective (oldContentExtensionUnitIso D Sc cutoff ν N).symm t

end OddMath.QuiverHecke.ELVOld
