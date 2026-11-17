import OddMath.QuiverHecke.CyclotomicAction.ContentBlockExtension.ContentComparisonParity
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts.UnitCoefficientRows

/-!
# Content block extension

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Inverse coefficient rows as fixed-content module maps

The normalized left cap in `SwappedVacuumNonpositiveBubbles.md`, §2,
comes from the prescribed inverse unit matrix. On fixed output content,
its coefficient rows are actual homogeneous module morphisms: project to
a shifted coordinate of the inverse and remove that prescribed shift.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open BalancedInduction TensorMatrixCoordinates
universe u

private def coordinateProjectionNat
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) :
    (OddMath.FiniteSupermodule.product V).toFunctor ⟶ (V a).toFunctor where
  app t := LinearMap.proj a
  naturality _ _ _ := by apply LinearMap.ext; intro x; rfl

private theorem coordinateProjectionNat_mem
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) (t : C) :
    (coordinateProjectionNat V a).app t ∈ parity (R := k) _ _ 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q x hx
  rw [add_zero]
  change x a ∈ ((V a).obj t).part q
  change x ∈ (OddMath.FiniteSuperspace.product fun b => (V b).obj t).part q at hx
  exact (OddMath.FiniteSuperspace.mem_product_part _ q x).mp hx a

private def coordinateProjection
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) :
    OddMath.FiniteSupermodule.product V ⟶ V a :=
  SuperNatTrans.ofNatTrans (coordinateProjectionNat V a) (coordinateProjectionNat_mem V a)

private theorem coordinateProjection_mem
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) :
    coordinateProjection V a ∈ parity (R := k) _ _ 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  exact SuperNatTrans.ofNatTrans_isHomogeneous _ _

private theorem coordinateProjection_total
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) (t : C) :
    (coordinateProjection V a).total t = LinearMap.proj a := by
  change (LinearMap.proj a : (OddMath.FiniteSupermodule.product V).obj t →ₗ[k] (V a).obj t) + 0 = _
  exact add_zero _

private theorem restriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {F G : Superfunctor k A (SVec k)} (f : F ⟶ G) (t : C) :
    ((restriction Q).map f).total t = f.total (Q.obj t) := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

local instance coefficientMapsPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- The prescribed inverse row on a fixed output-content category, with
the original r-th source shift removed by its selected comparison. -/
def contentUnitCoefficientMap (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (ν : Multiset I))) :
    (restriction (oldContentInclusion D Sc cutoff ν)).obj
      ((restriction (append D Sc cutoff i)).obj ((induction (append D Sc cutoff i)).obj M)) ⟶
    (restriction (oldContentInclusion D Sc cutoff ν)).obj M :=
  (contentUnitMatrixIso D Sc cutoff M i ν hh).inv ≫
    (restriction (oldContentInclusion D Sc cutoff ν)).map
      (coordinateProjection (unitMatrixFamily D Sc cutoff i M _) (some r) ≫
        ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom)

/-- This is a homogeneous module map of degree r*p, including along odd
and inhomogeneous old arrows through its supernatural components. -/
theorem contentUnitCoefficientMap_mem (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (ν : Multiset I))) :
    contentUnitCoefficientMap D Sc cutoff M i ν hh r ∈ parity (R := k) _ _ (r.val • D.parity i) := by
  have hp := coordinateProjection_mem (unitMatrixFamily D Sc cutoff i M _) (some r)
  have hs := (SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).hom_mem M
  have hc := comp_mem hp hs
  have hr := map_mem (restriction (oldContentInclusion D Sc cutoff ν)) hc
  have hi := (contentUnitMatrixIso_even D Sc cutoff M i ν hh).2
  simpa only [contentUnitCoefficientMap, zero_add] using comp_mem hi hr

/-- The inverse content matrix has precisely its selected component inverse. -/
theorem contentUnitMatrixIso_inv_total (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (t : OldContentCategory D Sc cutoff ν) :
    (contentUnitMatrixIso D Sc cutoff M i ν hh).inv.total t =
      (contentUnitMatrixComponentIso D Sc cutoff M i ν hh t).inv := by
  change (contentUnitMatrixComponentIso D Sc cutoff M i ν hh t).inv + 0 = _
  exact add_zero _

/-- Literal evaluation of the coefficient module map: the prescribed
component inverse, its r-th coordinate, and the original source unshift. -/
theorem contentUnitCoefficientMap_total (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (ν : Multiset I)))
    (t : OldContentCategory D Sc cutoff ν)
    (z : mateTargetSpace D Sc cutoff i M t.obj) :
    (contentUnitCoefficientMap D Sc cutoff M i ν hh r).total t z =
      ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom.total t.obj
        (((contentUnitMatrixComponentIso D Sc cutoff M i ν hh t).inv z) (some r)) := by
  simp only [contentUnitCoefficientMap, Superfunctor.comp_total, restriction_total,
    coordinateProjection_total, contentUnitMatrixIso_inv_total, SVec.comp_apply]
  rfl

/-- At the empty word this module map is precisely the previously
specified coefficient of the original all-old inverse matrix. -/
theorem contentUnitCoefficientMap_vacuum_total (i : I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)))
    (z : mateTargetSpace D Sc cutoff i M (⟨[]⟩ : OldCategory D Sc cutoff)) :
    (contentUnitCoefficientMap D Sc cutoff M i [] hh r).total
      (⟨⟨[]⟩, List.Perm.refl _⟩ : OldContentCategory D Sc cutoff []) z =
      moduleUnitCoefficient D Sc cutoff M i (⟨[]⟩ : OldCategory D Sc cutoff) hh r z := by
  rw [contentUnitCoefficientMap_total]
  have he : contentUnitMatrixComponentIso D Sc cutoff M i [] hh
      (⟨⟨[]⟩, List.Perm.refl _⟩ : OldContentCategory D Sc cutoff []) =
      moduleUnitMatrixIso D Sc cutoff M i (⟨[]⟩ : OldCategory D Sc cutoff) hh := by
    apply Iso.ext
    rw [contentUnitMatrixComponentIso_hom, moduleUnitMatrixIso_hom]
  rw [he]
  rfl

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Inverse-defined coefficient caps on native content modules

The probe left-cap normalization in `SwappedVacuumNonpositiveBubbles.md`,
§2, uses the chosen F/E chart, a prescribed inverse unit-matrix coefficient,
and the inverse fully faithful inclusion unit. These compose to module
maps from native F/E back to the original module. Input-module family
naturality and the final swapped mixed slide remain separate obligations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Fixed-output-content matrix inverses natural in input modules

DeformedMatrixComparison section 4. Whole finite-family input-module
naturality combines with the verified content-module component inverses.
The resulting natural isomorphisms retain every prescribed unit/cap entry,
both height signs, both moving parities and the zero-count principal mate.
Compatibility with the chosen content E/F composites remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Literal forward matrix entries, without any rescaling. -/
theorem unitMatrixModuleMap_total (i : I) (m : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    (unitMatrixModuleMap D Sc cutoff i m M).total t =
      unitMatrixComponent D Sc cutoff i M m t := by
  ext x
  exact FiniteSupermodule.columnsHom_total_apply _ _ _ _

/-- The restricted forward unit map is the existing literal content isomorphism. -/
theorem contentUnitMatrixIso_hom_eq (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (contentUnitMatrixIso D Sc cutoff M i ν hh).hom =
      (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).map
        (unitMatrixModuleMap D Sc cutoff i
          (contentUnitCount D cutoff i (ν : Multiset I)) M) := by
  apply FiniteSupermodule.hom_ext_total
  intro t
  change (contentUnitMatrixIso D Sc cutoff M i ν hh).hom.total t =
    (unitMatrixModuleMap D Sc cutoff i
      (contentUnitCount D cutoff i (ν : Multiset I)) M).total t.obj
  rw [contentUnitMatrixIso_hom_total, unitMatrixModuleMap_total]

/-- The output-content restricted unit matrix, natural in the input module. -/
def contentUnitMatrixFunctorNatIso (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I)) :
    (unitMatrixSourceFunctor D Sc cutoff i (contentUnitCount D cutoff i (ν : Multiset I)) ⋙
      BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)) ≅
    ((BalancedInduction.induction (append D Sc cutoff i) ⋙
      BalancedInduction.restriction (append D Sc cutoff i)) ⋙
        BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)) :=
  NatIso.ofComponents (fun M => contentUnitMatrixIso D Sc cutoff M i ν hh) (by
    intro M N f
    simp only [contentUnitMatrixIso_hom_eq]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun g =>
      (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).map g)
      ((unitMatrixModuleNatTrans D Sc cutoff i
        (contentUnitCount D cutoff i (ν : Multiset I))).naturality f))

/-- Both directions have even module components, before any factor-action transport. -/
theorem contentUnitMatrixFunctorNatIso_even (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (contentUnitMatrixFunctorNatIso D Sc cutoff i ν hh).hom.app M ∈ parity (R := k) _ _ 0 ∧
      (contentUnitMatrixFunctorNatIso D Sc cutoff i ν hh).inv.app M ∈ parity (R := k) _ _ 0 :=
  contentUnitMatrixIso_even D Sc cutoff M i ν hh

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end
