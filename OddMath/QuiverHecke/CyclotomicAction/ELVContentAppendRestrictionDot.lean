import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot

/-! # The chosen dot after restricting append extension

The fixed-content inverse comparison in DeformedActionAssembly §5 uses
`oldContentAppendRestrictionIso`, including its selected fully-faithful
inclusion unit. Its literal raw coend component intertwines the prescribed
content dot and the restricted old induction dot, with either moving parity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u

namespace BalancedInduction
private theorem fullyFaithfulComparison_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Full] [J.Faithful] [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (N : Superfunctor k C (SVec k)) (P : Superfunctor k A (SVec k))
    (e : induced J N ≅ P) (v : C) (b : N.obj v) :
    ((fullyFaithfulUnitIso J N ≪≫ (restriction J).mapIso e).hom).total v b =
      e.hom.total (J.obj v) (unit J N.toFunctor v b) := by
  have hu : (fullyFaithfulUnitIso J N).hom.total v b = unit J N.toFunctor v b := by
    rw [fullyFaithfulUnitIso_hom]
    exact unit_total_apply J N v b
  rw [Iso.trans_hom, Functor.mapIso_hom, Superfunctor.comp_total]
  change ((restriction J).map e.hom).total v
    ((fullyFaithfulUnitIso J N).hom.total v b) = _
  exact congrArg (fun a => ((restriction J).map e.hom).total v a) hu

private theorem fullyFaithfulComparison_linear
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Full] [J.Faithful] [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (N : Superfunctor k C (SVec k)) (P : Superfunctor k A (SVec k))
    (e : induced J N ≅ P) (v : C) :
    ((fullyFaithfulUnitIso J N ≪≫ (restriction J).mapIso e).hom).total v =
      e.hom.total (J.obj v) ∘ₗ unit J N.toFunctor v := by
  apply LinearMap.ext
  intro b
  exact fullyFaithfulComparison_total J N P e v b

private theorem mapComponent_unit
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (p : ZMod 2) (v : C) (b : M.obj v) :
    mapComponent J f p (J.obj v) (unit J M.toFunctor v b) =
      unit J N.toFunctor v (f.app p v b) := by
  rw [unit_apply, mapComponent_tensor, twist_id, unit_apply]

private theorem mapComponent_unit_linear
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (p : ZMod 2) (v : C) :
    mapComponent J f p (J.obj v) ∘ₗ unit J M.toFunctor v =
      unit J N.toFunctor v ∘ₗ f.app p v := by
  apply LinearMap.ext
  intro b
  exact mapComponent_unit J f p v b
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)

/-- The selected append-restriction comparison on its literal coend carriers. -/
def oldContentAppendRestrictionLinear
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj (oldContentAppend D Sc cutoff ν i) M.toFunctor t →ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i)
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M).toFunctor t.obj :=
  (oldContentAppendRestrictionIso D Sc cutoff ν i M).hom.total t

/-- The actual inclusion unit, with its source fixed as the raw append coend. -/
def oldContentAppendInclusionUnitLinear
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj (oldContentAppend D Sc cutoff ν i) M.toFunctor t →ₗ[k]
      BalancedInduction.Obj (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor t.obj :=
  BalancedInduction.unit (oldContentInclusion D Sc cutoff (i :: ν))
    (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor t

/-- The selected map first inserts the actual inclusion unit and then uses
the already selected full-content append extension comparison. -/
theorem oldContentAppendRestrictionLinear_eq
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    oldContentAppendRestrictionLinear D Sc cutoff ν i M t =
      oldContentAppendExtensionLinear D Sc cutoff ν i M t.obj ∘ₗ
        oldContentAppendInclusionUnitLinear D Sc cutoff ν i M t := by
  exact BalancedInduction.fullyFaithfulComparison_linear
    (oldContentInclusion D Sc cutoff (i :: ν))
    (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M)
    (BalancedInduction.induced (append D Sc cutoff i)
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M))
    ((oldContentAppendExtensionIso D Sc cutoff ν i).app M) t

/-- Restricting the chosen comparison preserves the literal dot operator
for both moving parities, on every module and every content object. -/
theorem oldContentAppendRestrictionIso_dot
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    oldContentAppendRestrictionLinear D Sc cutoff ν i M t ∘ₗ
      BalancedInduction.transformLinear
        (oldContentAppendDot_supernatural D Sc cutoff ν i) M t =
      inductionDot D Sc cutoff i
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M) t.obj ∘ₗ
          oldContentAppendRestrictionLinear D Sc cutoff ν i M t := by
  simp only [oldContentAppendRestrictionLinear_eq]
  have hu := BalancedInduction.mapComponent_unit_linear
    (oldContentInclusion D Sc cutoff (i :: ν))
    (oldContentInductionDotComponent D Sc cutoff ν i M) (D.parity i) t
  simp only [oldContentInductionDotComponent, BalancedInduction.transformComponent_app,
    ↓reduceIte] at hu
  change BalancedInduction.mapComponent (oldContentInclusion D Sc cutoff (i :: ν))
      (oldContentInductionDotComponent D Sc cutoff ν i M) (D.parity i) t.obj ∘ₗ
      oldContentAppendInclusionUnitLinear D Sc cutoff ν i M t =
    oldContentAppendInclusionUnitLinear D Sc cutoff ν i M t ∘ₗ
      BalancedInduction.transformLinear
        (oldContentAppendDot_supernatural D Sc cutoff ν i) M t at hu
  rw [LinearMap.comp_assoc, ← hu, ← LinearMap.comp_assoc,
    oldContentAppendExtensionIso_dot, LinearMap.comp_assoc]

end OddMath.QuiverHecke.ELVOld
