import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import OddMath.QuiverHecke.CyclotomicAction.ContentModule
import OddMath.QuiverHecke.CyclotomicAction.CapInputMatrices
import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.FullInduction
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend
import OddMath.QuiverHecke.CyclotomicAction.DistinctCrossing
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed

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

/-! # Parity of the selected content extension and F/E charts

SwappedVacuumCoordinates §6 and DeformedMatrixComparison (4), (5) use the
chosen content extension/restriction comparisons in the normalized cap.
Their actual module components are even, with the same selected maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
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

section

/-! # Input-module naturality of inverse-defined coefficient caps

The normalized left cap of `SwappedVacuumNonpositiveBubbles.md`, §2,
uses a prescribed inverse coefficient and its original parity unshift.
The unshift is supernatural on odd input maps. We retain that sign when
assembling the cap family, including the empty output content.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u

private def coefficientProjectionNat
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) :
    (OddMath.FiniteSupermodule.product V).toFunctor ⟶ (V a).toFunctor where
  app t := LinearMap.proj a
  naturality _ _ _ := by apply LinearMap.ext; intro x; rfl

private theorem coefficientProjectionNat_mem
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) (t : C) :
    (coefficientProjectionNat V a).app t ∈ parity (R := k) _ _ 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q x hx
  rw [add_zero]
  change x a ∈ ((V a).obj t).part q
  change x ∈ (OddMath.FiniteSuperspace.product fun b => (V b).obj t).part q at hx
  exact (OddMath.FiniteSuperspace.mem_product_part _ q x).mp hx a

private def coefficientProjection
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) :
    OddMath.FiniteSupermodule.product V ⟶ V a :=
  SuperNatTrans.ofNatTrans (coefficientProjectionNat V a) (coefficientProjectionNat_mem V a)

private theorem coefficientProjection_mem
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) :
    coefficientProjection V a ∈ parity (R := k) _ _ 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  exact SuperNatTrans.ofNatTrans_isHomogeneous _ _

private theorem coefficientProjection_total
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) (t : C) :
    (coefficientProjection V a).total t = LinearMap.proj a := by
  change (LinearMap.proj a : (OddMath.FiniteSupermodule.product V).obj t →ₗ[k] (V a).obj t) + 0 = _
  exact add_zero _

private theorem productMap_projection
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V W : ι → Superfunctor k C (SVec k)) (a : ι)
    (f : ∀ a, V a ⟶ W a) :
    OddMath.FiniteSupermodule.productMap f ≫ coefficientProjection W a =
      coefficientProjection V a ≫ f a := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro t
  rw [Superfunctor.comp_total, Superfunctor.comp_total,
    coefficientProjection_total, coefficientProjection_total]
  apply LinearMap.ext
  intro x
  exact OddMath.FiniteSupermodule.productMap_total_apply f t x a

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance coefficientCapNaturalityPi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

private def unitCoefficientProjectionNatTrans (i : I) (m : ℕ) (r : Fin m) :
    unitMatrixSourceFunctor D Sc cutoff i m ⟶ SKM.homParityShift (k := k) (r.val • D.parity i) where
  app M := coefficientProjection (unitMatrixFamily D Sc cutoff i M m) (some r)
  naturality M N f := by
    change OddMath.FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m f) ≫
      coefficientProjection (unitMatrixFamily D Sc cutoff i N m) (some r) = _
    rw [productMap_projection]
    simp [unitMatrixCoordinateMap, unitMatrixSummandFunctor]

private theorem unitCoefficientUnshift_supernatural (i : I) (m : ℕ) (r : Fin m) :
    IsSupernatural k (r.val • D.parity i)
      (F := unitMatrixSourceFunctor D Sc cutoff i m)
      (G := 𝟭 (Superfunctor k (OldCategory D Sc cutoff) (SVec k)))
      (fun M => coefficientProjection (unitMatrixFamily D Sc cutoff i M m) (some r) ≫
        ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom) := by
  have hp := isSupernatural_of_natTrans (R := k)
    (unitCoefficientProjectionNatTrans D Sc cutoff i m r)
    (fun M => coefficientProjection_mem (unitMatrixFamily D Sc cutoff i M m) (some r))
  simpa only [zero_add, unitCoefficientProjectionNatTrans] using
    hp.comp (SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).supernatural

/-- The actual prescribed inverse coefficient row is supernatural in
arbitrary homogeneous input-module maps. This includes the empty output
block and retains the Koszul sign of the original source unshift. -/
theorem contentUnitCoefficientMap_supernatural (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (ν : Multiset I))) :
    IsSupernatural k (r.val • D.parity i)
      (F := (induction (append D Sc cutoff i) ⋙ restriction (append D Sc cutoff i)) ⋙
        restriction (oldContentInclusion D Sc cutoff ν))
      (G := restriction (oldContentInclusion D Sc cutoff ν))
      (fun M => contentUnitCoefficientMap D Sc cutoff M i ν hh r) := by
  have hi := isSupernatural_of_natTrans (R := k)
    (contentUnitMatrixFunctorNatIso D Sc cutoff i ν hh).inv
    (fun M => (contentUnitMatrixFunctorNatIso_even D Sc cutoff i ν hh M).2)
  have hp := (unitCoefficientUnshift_supernatural D Sc cutoff i
    (contentUnitCount D cutoff i (ν : Multiset I)) r).whiskerRight
    (restriction (oldContentInclusion D Sc cutoff ν))
  have hrow (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
      (contentUnitMatrixFunctorNatIso D Sc cutoff i ν hh).inv.app M ≫
        (restriction (oldContentInclusion D Sc cutoff ν)).map
          (coefficientProjection (unitMatrixFamily D Sc cutoff i M
            (contentUnitCount D cutoff i (ν : Multiset I))) (some r) ≫
            ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom) =
        contentUnitCoefficientMap D Sc cutoff M i ν hh r := by
    rfl
  simpa only [zero_add, Functor.id_comp, hrow] using hi.comp hp

/-- The inverse-defined native coefficient caps form a homogeneous
supernatural family on every input module, including at empty content.
Odd input maps retain the prescribed row-degree Koszul sign. -/
theorem contentCoefficientCap_supernatural (ν : List I) (i : I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (ν : Multiset I))) :
    IsSupernatural k (r.val • D.parity i)
      (F := induction (oldContentAppend D Sc cutoff ν i) ⋙
        restriction (oldContentAppend D Sc cutoff ν i))
      (G := 𝟭 (Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)))
      (fun N => contentCoefficientCap D Sc cutoff ν i N hh r) := by
  have he := isSupernatural_of_natTrans (R := k)
    (oldContentFERestrictionNaturalIso D Sc cutoff ν i).hom
    (fun N => oldContentFERestrictionNaturalIso_hom_mem D Sc cutoff ν i N)
  have hr := (contentUnitCoefficientMap_supernatural D Sc cutoff i ν hh r).whiskerLeft
    (induction (oldContentInclusion D Sc cutoff ν))
  have hf := isSupernatural_of_natTrans (R := k)
    (fullyFaithfulUnitNaturalIso (oldContentInclusion D Sc cutoff ν)).inv
    (fun N => inv_mem (oldContentExtensionUnitIso D Sc cutoff ν N)
      (oldContentExtensionUnitIso_hom_mem D Sc cutoff ν N))
  have hcap (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
      (oldContentFERestrictionNaturalIso D Sc cutoff ν i).hom.app N ≫
        contentUnitCoefficientMap D Sc cutoff
          ((induction (oldContentInclusion D Sc cutoff ν)).obj N) i ν hh r ≫
          (fullyFaithfulUnitNaturalIso (oldContentInclusion D Sc cutoff ν)).inv.app N =
        contentCoefficientCap D Sc cutoff ν i N hh r := by
    rfl
  simpa only [zero_add, add_zero, hcap] using he.comp (hr.comp hf)

/-- The actual coefficient caps, packaged as an input-module supernatural
transformation with their already prescribed components. -/
def contentCoefficientCapFamily (ν : List I) (i : I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (ν : Multiset I))) :
    SuperNatTrans k
      (induction (oldContentAppend D Sc cutoff ν i) ⋙
        restriction (oldContentAppend D Sc cutoff ν i))
      (𝟭 (Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))) :=
  (contentCoefficientCap_supernatural D Sc cutoff ν i hh r).toSuperNatTrans

/-- The family is homogeneous of precisely the selected inverse-row degree. -/
theorem contentCoefficientCapFamily_isHomogeneous (ν : List I) (i : I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (ν : Multiset I))) :
    (contentCoefficientCapFamily D Sc cutoff ν i hh r).IsHomogeneous (r.val • D.parity i) :=
  (contentCoefficientCap_supernatural D Sc cutoff ν i hh r).toSuperNatTrans_isHomogeneous

/-- Total input-module evaluation is exactly the previous native coefficient
cap. Thus its checked scalar fields and regular-probe window apply verbatim. -/
theorem contentCoefficientCapFamily_total (ν : List I) (i : I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (ν : Multiset I)))
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (contentCoefficientCapFamily D Sc cutoff ν i hh r).total N =
      contentCoefficientCap D Sc cutoff ν i N hh r := by
  unfold contentCoefficientCapFamily
  rcases parity_eq_zero_or_one (r.val • D.parity i) with hp | hp <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans, hp]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Extension from a full truncated content block

The canonical multiset content module realization of Brundan–Ellis
(1.12) uses extension along the literal full content inclusion. Its unit
is invertible and its counit is invertible on supported modules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

instance contentInclusion_additive (β : Multiset I) :
    (contentInclusion D Sc cutoff N β).Additive where
  map_add := by intros; rfl
instance contentInclusion_linear (β : Multiset I) :
    (contentInclusion D Sc cutoff N β).Linear k where
  map_smul := by intros; rfl
instance contentInclusion_super (β : Multiset I) :
    IsSuperfunctor k (contentInclusion D Sc cutoff N β) where
  map_mem h := h

/-- Content conservation descends through the literal truncated quotient. -/
theorem truncatedCategory_hom_eq_zero_of_content_ne
    {v w : TruncatedCategory D Sc cutoff N}
    (h : (v.word : Multiset I) ≠ (w.word : Multiset I)) (f : v ⟶ w) : f = 0 := by
  obtain ⟨a, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word w.word).mkQ_surjective f
  have hp : ¬ w.word.Perm v.word := fun hp => h (Multiset.coe_eq_coe.mpr hp.symm)
  rw [hom_eq_zero_of_not_perm D Sc cutoff hp a, map_zero]

/-- The chosen full-inclusion unit recovers every exact-content module. -/
def contentExtensionUnitIso (β : Multiset I) (M : ContentModules D Sc cutoff N β) :
    M ≅ (BalancedInduction.restriction (contentInclusion D Sc cutoff N β)).obj
      (BalancedInduction.induced (contentInclusion D Sc cutoff N β) M) :=
  BalancedInduction.fullyFaithfulUnitIso (contentInclusion D Sc cutoff N β) M

/-- Support means literal zero components outside the chosen colour multiset. -/
def ContentSupported (β : Multiset I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) : Prop :=
  ∀ w : TruncatedCategory D Sc cutoff N, (w.word : Multiset I) ≠ β →
    Subsingleton (M.obj w)

theorem contentExtension_supported (β : Multiset I)
    (M : Superfunctor k (ContentCategory D Sc cutoff N β) (SVec k)) :
    ContentSupported D Sc cutoff N β
      (BalancedInduction.induced (contentInclusion D Sc cutoff N β) M) := by
  intro w hw
  have hz : ∀ z : BalancedInduction.Obj (contentInclusion D Sc cutoff N β) M.toFunctor w,
      z = 0 := by
    apply BalancedInduction.obj_eq_zero_of_coeff_eq_zero
    intro s g
    apply truncatedCategory_hom_eq_zero_of_content_ne D Sc cutoff N (f := g)
    intro he
    exact hw (he.symm.trans s.content)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem contentSupportedCounit_bijective (β : Multiset I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hM : ContentSupported D Sc cutoff N β M) (w : TruncatedCategory D Sc cutoff N) :
    Function.Bijective (BalancedInduction.counit (contentInclusion D Sc cutoff N β)
      M.toFunctor w) := by
  classical
  by_cases hw : (w.word : Multiset I) = β
  · exact BalancedInduction.counit_bijective_at_image
      (contentInclusion D Sc cutoff N β) M.toFunctor
      ⟨w, hw⟩
  · have hsource := contentExtension_supported D Sc cutoff N β
      ((BalancedInduction.restriction (contentInclusion D Sc cutoff N β)).obj M) w hw
    have htarget := hM w hw
    exact ⟨fun x y _ => hsource.elim x y, fun y => ⟨0, htarget.elim _ y⟩⟩

/-- The forward map is precisely the established balanced inclusion counit. -/
def contentSupportedCounitEquiv (β : Multiset I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hM : ContentSupported D Sc cutoff N β M) (w : TruncatedCategory D Sc cutoff N) :
    BalancedInduction.Obj (contentInclusion D Sc cutoff N β)
        (contentInclusion D Sc cutoff N β ⋙ M.toFunctor) w ≃ₗ[k] M.obj w :=
  LinearEquiv.ofBijective _ (contentSupportedCounit_bijective D Sc cutoff N β M hM w)

def contentSupportedCounitNatIso (β : Multiset I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hM : ContentSupported D Sc cutoff N β M) :
    (BalancedInduction.induced (contentInclusion D Sc cutoff N β)
      ((BalancedInduction.restriction (contentInclusion D Sc cutoff N β)).obj M)).toFunctor ≅
        M.toFunctor :=
  NatIso.ofComponents (fun w =>
    { hom := BalancedInduction.counit (contentInclusion D Sc cutoff N β) M.toFunctor w
      inv := (contentSupportedCounitEquiv D Sc cutoff N β M hM w).symm.toLinearMap
      hom_inv_id := by
        ext z
        exact (contentSupportedCounitEquiv D Sc cutoff N β M hM w).symm_apply_apply z
      inv_hom_id := by
        ext z
        exact (contentSupportedCounitEquiv D Sc cutoff N β M hM w).apply_symm_apply z })
    (fun a => BalancedInduction.counit_naturality (contentInclusion D Sc cutoff N β)
      M.toFunctor a)

/-- Supported modules are recovered by the actual even inclusion counit. -/
def contentSupportedCounitIso (β : Multiset I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hM : ContentSupported D Sc cutoff N β M) :
    BalancedInduction.induced (contentInclusion D Sc cutoff N β)
      ((BalancedInduction.restriction (contentInclusion D Sc cutoff N β)).obj M) ≅ M :=
  moduleIsoOfEvenNatIso _ _ (contentSupportedCounitNatIso D Sc cutoff N β M hM)
    (fun w => BalancedInduction.counit_mem (contentInclusion D Sc cutoff N β) M w)
    (fun w => Supercategory.inv_mem
      ((contentSupportedCounitNatIso D Sc cutoff N β M hM).app w)
      (BalancedInduction.counit_mem (contentInclusion D Sc cutoff N β) M w))

theorem contentSupportedCounitIso_hom (β : Multiset I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hM : ContentSupported D Sc cutoff N β M) :
    (contentSupportedCounitIso D Sc cutoff N β M hM).hom =
      (BalancedInduction.adjunctionCounit (contentInclusion D Sc cutoff N β)).app M := by
  apply Superfunctor.hom_ext
  intro p w
  rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Chosen append comparisons for truncated content blocks

For the canonical multiset-content realization of Brundan–Ellis (1.12),
induction and restriction are compared with global truncated append
using the literal inclusion square, its even unit, and its supported
counit. Arbitrary common upper contents are retained explicitly.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The append/inclusion square is literal on objects and whole quotient arrows. -/
theorem contentAppendTo_inclusion (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ) :
    contentAppendTo D Sc cutoff N β σ γ h ⋙ contentInclusion D Sc cutoff N γ =
      contentInclusion D Sc cutoff N β ⋙ truncatedAppend D Sc cutoff N σ := rfl

/-- The chosen comparison of append induction followed by full-content extension. -/
def contentAppendToExtensionIso (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ) :
    BalancedInduction.induction (k := k) (contentAppendTo D Sc cutoff N β σ γ h) ⋙
        BalancedInduction.induction (contentInclusion D Sc cutoff N γ) ≅
      BalancedInduction.induction (contentInclusion D Sc cutoff N β) ⋙
        BalancedInduction.induction (truncatedAppend D Sc cutoff N σ) :=
  BalancedInduction.inductionComp (contentAppendTo D Sc cutoff N β σ γ h)
      (contentInclusion D Sc cutoff N γ) ≪≫
    BalancedInduction.inductionFunctorIsoOfEq _ _ (contentAppendTo_inclusion D Sc cutoff N β σ γ h) ≪≫
    (BalancedInduction.inductionComp (contentInclusion D Sc cutoff N β)
      (truncatedAppend D Sc cutoff N σ)).symm

/-- Restricting global append of the canonical extension recovers chosen content induction. -/
def contentAppendToRestrictionIso (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ) (M : ContentModules D Sc cutoff N β) :
    BalancedInduction.induced (contentAppendTo D Sc cutoff N β σ γ h) M ≅
      (BalancedInduction.restriction (contentInclusion D Sc cutoff N γ)).obj
        (BalancedInduction.induced (truncatedAppend D Sc cutoff N σ)
          (BalancedInduction.induced (contentInclusion D Sc cutoff N β) M)) :=
  contentExtensionUnitIso D Sc cutoff N γ
      (BalancedInduction.induced (contentAppendTo D Sc cutoff N β σ γ h) M) ≪≫
    (BalancedInduction.restriction (contentInclusion D Sc cutoff N γ)).mapIso
      ((contentAppendToExtensionIso D Sc cutoff N β σ γ h).app M)

/-- Single-colour restriction subtracts its colour from the precise support. -/
theorem contentAppendRestriction_supported (β : Multiset I) (i : I) (γ : Multiset I)
    (h : β + ([i] : Multiset I) = γ)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hM : ContentSupported D Sc cutoff N γ M) :
    ContentSupported D Sc cutoff N β
      ((BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i])).obj M) := by
  intro w hw
  apply hM ((truncatedAppend D Sc cutoff N [i]).obj w)
  intro he
  apply hw
  change (w.word : Multiset I) + ([i] : Multiset I) = γ at he
  exact add_right_cancel (he.trans h.symm)

/-- Both restrictions around the selected inclusion square agree literally. -/
def contentAppendToRestrictionSquare (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (BalancedInduction.restriction (contentAppendTo D Sc cutoff N β σ γ h)).obj
        ((BalancedInduction.restriction (contentInclusion D Sc cutoff N γ)).obj M) ≅
      (BalancedInduction.restriction (contentInclusion D Sc cutoff N β)).obj
        ((BalancedInduction.restriction (truncatedAppend D Sc cutoff N σ)).obj M) := Iso.refl _

/-- Extending content restriction is global restriction of the canonical extension. -/
def contentAppendToRestrictionExtensionIso (β : Multiset I) (i : I) (γ : Multiset I)
    (h : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N γ) :
    BalancedInduction.induced (contentInclusion D Sc cutoff N β)
        ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).obj M) ≅
      (BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i])).obj
        (BalancedInduction.induced (contentInclusion D Sc cutoff N γ) M) :=
  (BalancedInduction.induction (contentInclusion D Sc cutoff N β)).mapIso
    ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).mapIso
      (contentExtensionUnitIso D Sc cutoff N γ M) ≪≫
      contentAppendToRestrictionSquare D Sc cutoff N β [i] γ h
        (BalancedInduction.induced (contentInclusion D Sc cutoff N γ) M)) ≪≫
    contentSupportedCounitIso D Sc cutoff N β _
      (contentAppendRestriction_supported D Sc cutoff N β i γ h _
        (contentExtension_supported D Sc cutoff N γ M))

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The selected append chart on truncated content tensors

For Brundan–Ellis (1.12), specialize the abstract commuting induction
square to the literal truncated content inclusion. Its chosen forward
map retains every entire quotient coefficient and inserts the selected
input inclusion unit, with no homogeneity assumption.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (σ : List I) (γ : Multiset I) (hσ : β + (σ : Multiset I) = γ)
local notation "J" => contentAppendTo D Sc cutoff N β σ γ hσ
local notation "P" => contentInclusion D Sc cutoff N β
local notation "Q" => contentInclusion D Sc cutoff N γ
local notation "A" => truncatedAppend D Sc cutoff N σ

private theorem contentBlockInclusion_obj (δ : Multiset I)
    (s : ContentCategory D Sc cutoff N δ) :
    (contentInclusion D Sc cutoff N δ).obj s = s.obj := rfl
private theorem contentBlockInclusion_map (δ : Multiset I)
    (s t : ContentCategory D Sc cutoff N δ) (f : s ⟶ t) :
    (contentInclusion D Sc cutoff N δ).map f = f := rfl

/-- The selected comparison with both raw balanced-coend endpoints fixed generically. -/
def contentAppendToRestrictionLinear (M : ContentModules D Sc cutoff N β)
    (t : ContentCategory D Sc cutoff N γ) :
    BalancedInduction.Obj J M.toFunctor t →ₗ[k]
      BalancedInduction.Obj A (BalancedInduction.induced P M).toFunctor t.obj :=
  BalancedInduction.fullSquareRestrictionLinear J Q P A
    (contentAppendTo_inclusion D Sc cutoff N β σ γ hσ) M t

/-- Entire coefficient arrows remain unchanged and the actual input inclusion unit is inserted. -/
theorem contentAppendToRestrictionLinear_tensor (M : ContentModules D Sc cutoff N β)
    (s : ContentCategory D Sc cutoff N β) (t : ContentCategory D Sc cutoff N γ)
    (g : (A).obj s.obj ⟶ t.obj) (b : M.obj s) :
    contentAppendToRestrictionLinear D Sc cutoff N β σ γ hσ M t
      (BalancedInduction.tensor J M.toFunctor s g b) =
      BalancedInduction.tensor A (BalancedInduction.induced P M).toFunctor s.obj g
        (BalancedInduction.unit P M.toFunctor s b) := by
  have h := BalancedInduction.fullSquareRestrictionLinear_tensor J Q P A
    (contentAppendTo_inclusion D Sc cutoff N β σ γ hσ) M s t g b
  simpa only [contentAppendToRestrictionLinear, eqToHom_refl, Category.id_comp,
    contentBlockInclusion_obj, contentBlockInclusion_map] using h

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Associativity of the content induction comparisons

`contentETripleComparison_assoc` identifies the named triple comparison with
suffix-first composition, including all endpoint equality transports. This is
whole natural-isomorphism coherence for the content triple action; it supplies
the comparison needed to identify independently defined triple operators.

The proof uses uniqueness of left adjoints, not transport of generator formulas.
There are no finiteness, field, or flatness assumptions.
-/
noncomputable section
open CategoryTheory
universe u
namespace OddMath.QuiverHecke.ELV.ContentComparisonCoherence
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
variable {F : A ⥤ B} {G : B ⥤ A} {H : B ⥤ C} {I : C ⥤ B} {J : C ⥤ D} {K : D ⥤ C}
variable {P : A ⥤ C} {Q : B ⥤ D} {R : A ⥤ D}
variable (a : F ⊣ G) (b : H ⊣ I) (c : J ⊣ K) (p : P ⊣ I ⋙ G) (q : Q ⊣ K ⋙ I) (r : R ⊣ (K ⋙ I) ⋙ G)

private theorem uniq_whisker_right (x : A) :
    J.map (((a.comp b).leftAdjointUniq p).hom.app x) =
    (((a.comp b).comp c).leftAdjointUniq (p.comp c)).hom.app x := by
  apply (((a.comp b).comp c).homEquiv _ _).injective
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc]
  rw [← G.map_comp, ← I.map_comp, c.unit_naturality]
  rw [I.map_comp, G.map_comp]
  rw [← Category.assoc, ← Category.assoc]
  have he := Adjunction.unit_leftAdjointUniq_hom_app (a.comp b) p x
  rw [Adjunction.comp_unit_app] at he
  exact congrArg (fun f => f ≫ G.map (I.map (c.unit.app (P.obj x)))) he

private theorem uniq_whisker_left (x : A) :
    ((b.comp c).leftAdjointUniq q).hom.app (F.obj x) =
    (((a.comp b).comp c).leftAdjointUniq (a.comp q)).hom.app x := by
  apply (((a.comp b).comp c).homEquiv _ _).injective
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc]
  have he := Adjunction.unit_leftAdjointUniq_hom_app (b.comp c) q (F.obj x)
  rw [Adjunction.comp_unit_app] at he
  have hh := congrArg (fun f => a.unit.app x ≫ G.map f) he
  simpa only [Functor.map_comp, Functor.comp_map, Functor.comp_obj, Category.assoc] using hh

private theorem uniq_associativity (x : A) :
    J.map (((a.comp b).leftAdjointUniq p).hom.app x) ≫
      ((p.comp c).leftAdjointUniq r).hom.app x =
    ((b.comp c).leftAdjointUniq q).hom.app (F.obj x) ≫
      ((a.comp q).leftAdjointUniq r).hom.app x := by
  rw [uniq_whisker_right a b c p x, uniq_whisker_left a b c q x]
  rw [Adjunction.leftAdjointUniq_trans_app, Adjunction.leftAdjointUniq_trans_app]

end OddMath.QuiverHecke.ELV.ContentComparisonCoherence

open StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
variable {k : Type u} [CommRing k]
variable {C D E F : Type u} [Category.{u} C] [Category.{u} D]
  [Category.{u} E] [Category.{u} F]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
  [Preadditive F] [Linear k F] [Supercategory k F]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
variable (L : E ⥤ F) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

variable (P : C ⥤ E) [P.Additive] [P.Linear k] [IsSuperfunctor k P]
variable (Q : D ⥤ F) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
variable (R : C ⥤ F) [R.Additive] [R.Linear k] [IsSuperfunctor k R]

/-- Equality-transported composition comparisons commute on every module. -/
theorem inductionCompOfEq_assoc_hom
    (eP : J ⋙ K = P) (eQ : K ⋙ L = Q) (eR : P ⋙ L = R) (eS : J ⋙ Q = R)
    (M : Superfunctor k C (SVec k)) :
    (BalancedInduction.induction L).map ((inductionCompOfEq J K P eP).hom.app M) ≫
      (inductionCompOfEq P L R eR).hom.app M =
    (inductionCompOfEq K L Q eQ).hom.app (BalancedInduction.induced J M) ≫
      (inductionCompOfEq J Q R eS).hom.app M := by
  subst P
  subst Q
  subst R
  simp only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl]
  exact OddMath.QuiverHecke.ELV.ContentComparisonCoherence.uniq_associativity
      (BalancedInduction.adjunction J) (BalancedInduction.adjunction K)
      (BalancedInduction.adjunction L) (BalancedInduction.adjunction (J ⋙ K))
      (BalancedInduction.adjunction (K ⋙ L)) (BalancedInduction.adjunction ((J ⋙ K) ⋙ L)) M

/-- Associativity includes the four independently supplied functor equalities. -/
theorem inductionCompOfEq_assoc
    (eP : J ⋙ K = P) (eQ : K ⋙ L = Q) (eR : P ⋙ L = R) (eS : J ⋙ Q = R) :
    Functor.isoWhiskerRight (inductionCompOfEq (k := k) J K P eP) (BalancedInduction.induction (k := k) L) ≪≫
      inductionCompOfEq (k := k) P L R eR =
    Functor.associator (BalancedInduction.induction (k := k) J) (BalancedInduction.induction (k := k) K)
      (BalancedInduction.induction (k := k) L) ≪≫
      Functor.isoWhiskerLeft (BalancedInduction.induction (k := k) J) (inductionCompOfEq (k := k) K L Q eQ) ≪≫
      inductionCompOfEq (k := k) J Q R eS := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp]
  exact inductionCompOfEq_assoc_hom J K L P Q R eP eQ eR eS M
end OddMath.QuiverHecke.ELV

namespace OddMath.QuiverHecke.ELV
section Content
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
variable (β : Multiset I) (i j : I)
local notation "δ₁" => (β + ([i] : Multiset I))
local notation "δ₂" => ((β + ([i] : Multiset I)) + ([j] : Multiset I))
local notation "J" => contentAppend D Sc cutoff N β [i]
local notation "K" => contentAppend D Sc cutoff N δ₁ [j]
variable (τ : List I) (γ : Multiset I)
  (hγ : ((β + ([i] : Multiset I)) + ([j] : Multiset I)) + (τ : Multiset I) = γ)
  (hs : (β + ([i] : Multiset I)) + (([j] ++ τ : List I) : Multiset I) = γ)
  (h : β + (([i,j] ++ τ : List I) : Multiset I) = γ)
local notation "L" => contentAppendTo D Sc cutoff N δ₂ τ γ hγ

end Content
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Restriction chart tensors on canonical truncated content

The selected full-inclusion unit/counit comparison for Brundan–Ellis
(1.12) sends the entire quotient-arrow generator `[g ⊗ b]` to
`[append(g) ⊗ b]`. No parity restriction on either factor is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The comparison is the induction of the actual inclusion unit followed by
its actual inclusion counit; the append/inclusion restriction square is strict. -/
theorem contentAppendToRestrictionExtensionIso_hom (β : Multiset I) (i : I) (γ : Multiset I)
    (h : β + ([i] : Multiset I) = γ)
    (P : Superfunctor k (ContentCategory D Sc cutoff N γ) (SVec k)) :
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ h P).hom =
      (BalancedInduction.induction (contentInclusion D Sc cutoff N β)).map
        ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).map
          ((BalancedInduction.adjunctionUnit
            (contentInclusion D Sc cutoff N γ)).app P)) ≫
      (BalancedInduction.adjunctionCounit (contentInclusion D Sc cutoff N β)).app
        ((BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i])).obj
          (BalancedInduction.induced (contentInclusion D Sc cutoff N γ) P)) := by
  simp only [contentAppendToRestrictionExtensionIso, Iso.trans_hom, Functor.mapIso_hom,
    contentAppendToRestrictionSquare, Iso.refl_hom, Category.comp_id,
    contentExtensionUnitIso, BalancedInduction.fullyFaithfulUnitIso_hom,
    contentSupportedCounitIso_hom]

/-- The prescribed source-arrow generator is unchanged and its quotient arrow is appended. -/
theorem contentAppendToRestrictionExtensionIso_tensor (β : Multiset I) (i : I) (γ : Multiset I)
    (h : β + ([i] : Multiset I) = γ)
    (P : Superfunctor k (ContentCategory D Sc cutoff N γ) (SVec k))
    (w : TruncatedCategory D Sc cutoff N) (s : ContentCategory D Sc cutoff N β)
    (g : (contentInclusion D Sc cutoff N β).obj s ⟶ w)
    (b : P.obj ((contentAppendTo D Sc cutoff N β [i] γ h).obj s)) :
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ h P).hom.total w
      (BalancedInduction.tensor (contentInclusion D Sc cutoff N β)
        ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).obj P).toFunctor s g b) =
      BalancedInduction.tensor (contentInclusion D Sc cutoff N γ) P.toFunctor
        ((contentAppendTo D Sc cutoff N β [i] γ h).obj s) ((truncatedAppend D Sc cutoff N [i]).map g) b := by
  rw [contentAppendToRestrictionExtensionIso_hom, Superfunctor.comp_total]
  change ((BalancedInduction.adjunctionCounit (contentInclusion D Sc cutoff N β)).app
      ((BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i])).obj
        (BalancedInduction.induced (contentInclusion D Sc cutoff N γ) P))).total w
      ((BalancedInduction.moduleMap (contentInclusion D Sc cutoff N β)
        ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).map
          ((BalancedInduction.adjunctionUnit
            (contentInclusion D Sc cutoff N γ)).app P))).total w
        (BalancedInduction.tensor (contentInclusion D Sc cutoff N β)
          ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).obj P).toFunctor
            s g b)) = _
  rw [BalancedInduction.counit_total_apply]
  have hm := BalancedInduction.moduleMap_total_tensor
    (contentInclusion D Sc cutoff N β)
    ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).map
      ((BalancedInduction.adjunctionUnit (contentInclusion D Sc cutoff N γ)).app P))
    w s g b
  refine (congrArg (BalancedInduction.counit (contentInclusion D Sc cutoff N β)
    ((BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i])).obj
      (BalancedInduction.induced (contentInclusion D Sc cutoff N γ) P)).toFunctor w) hm).trans ?_
  change BalancedInduction.counit (contentInclusion D Sc cutoff N β)
      ((BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i])).obj
        (BalancedInduction.induced (contentInclusion D Sc cutoff N γ) P)).toFunctor w
      (BalancedInduction.tensor (contentInclusion D Sc cutoff N β) _ s g
        (BalancedInduction.unit (contentInclusion D Sc cutoff N γ) P.toFunctor
          ((contentAppendTo D Sc cutoff N β [i] γ h).obj s) b) +
        BalancedInduction.tensor (contentInclusion D Sc cutoff N β) _ s (twist k 1 g) 0) = _
  rw [BalancedInduction.tensor_zero_right, add_zero, BalancedInduction.counit_tensor]
  change BalancedInduction.postcompose (contentInclusion D Sc cutoff N γ) P.toFunctor
      ((truncatedAppend D Sc cutoff N [i]).map g)
      (BalancedInduction.unit (contentInclusion D Sc cutoff N γ) P.toFunctor
        ((contentAppendTo D Sc cutoff N β [i] γ h).obj s) b) = _
  rw [BalancedInduction.unit_apply, BalancedInduction.postcompose_tensor, Category.id_comp]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The positive two-colour crossing under coefficient truncation

Brundan–Ellis (1.12): the quotient crossing on successive singleton
appends retains the prescribed positive old crossing, including the
complete coefficient parity. Its existing two-letter append component
is identified under word associativity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
private theorem mixed_mapFamily_heq {ι : Type*} {U V : ι → Type*}
    (F : ∀ a, U a → V a) {a b : ι} (h : a = b)
    {x : U a} {y : U b} (hxy : HEq x y) : HEq (F a x) (F b y) := by
  cases h
  cases hxy
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i j : I)
local notation "A" => truncatedAppend D Sc cutoff N [i]
local notation "B" => truncatedAppend D Sc cutoff N [j]
local notation "Q" => oldTruncateFunctor D Sc cutoff N

/-- The literal positive crossing j,i→i,j on successive truncated append functors. -/
def truncatedDistinctCrossComponent (s : TruncatedCategory D Sc cutoff N) :
    (B ⋙ A).obj s ⟶ (A ⋙ B).obj s :=
  (truncatedIdeal D Sc cutoff N _ _).mkQ
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word j i))

/-- The selected old crossing projects to this exact two-colour quotient crossing. -/
theorem oldTruncateFunctor_map_distinctCross (s : OldCategory D Sc cutoff) :
    (Q).map (Distinct.crossComponent D Sc cutoff i j s) =
      truncatedDistinctCrossComponent D Sc cutoff N i j ((Q).obj s) := rfl

/-- The ordinary two-letter append crossing changes only its word-associativity endpoints. -/
theorem truncatedDistinctCrossComponent_heq (s : TruncatedCategory D Sc cutoff N) :
    HEq (truncatedDistinctCrossComponent D Sc cutoff N i j s)
      (truncatedAppendComponent D Sc cutoff N (crossTwo D Sc j i) s) := by
  have hw : (s.word ++ [j] ++ [i], s.word ++ [i] ++ [j]) =
      (s.word ++ [j, i], s.word ++ [i, j]) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hc := (conj_eqToHom_iff_heq _ _
    (congrArg (fun w => (pres D Sc).obj (ob D w)) (List.append_assoc s.word [j] [i]))
    (congrArg (fun w => (pres D Sc).obj (ob D w)) (List.append_assoc s.word [i] [j]))).mp
      (crossLast_eq D Sc s.word j i)
  have ha := mixed_mapFamily_heq
    (U := fun z : List I × List I =>
      (pres D Sc).obj (ob D z.1) ⟶ (pres D Sc).obj (ob D z.2))
    (V := fun z : List I × List I => hom D Sc cutoff z.1 z.2)
    (fun z f => affineUnit D Sc cutoff z.1 z.2 f) hw hc
  exact mixed_mapFamily_heq
    (U := fun z : List I × List I => hom D Sc cutoff z.1 z.2)
    (V := fun z : List I × List I => TruncatedOld D Sc cutoff N z.1 z.2)
    (fun z f => (truncatedIdeal D Sc cutoff N z.1 z.2).mkQ f) hw ha

/-- The positive crossing remains supernatural for all coefficient parities. -/
theorem truncatedDistinctCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j)
      (truncatedDistinctCrossComponent D Sc cutoff N i j) := by
  apply IsSupernatural.of_twist
  · intro s
    rw [mul_comm (D.parity i) (D.parity j)]
    exact Submodule.mem_map_of_mem
      (ELVPScalar.affineUnit_mem D Sc cutoff (crossLast_mem D Sc s.word j i))
  · intro s t f
    obtain ⟨a, rfl⟩ := (truncatedIdeal D Sc cutoff N s.word t.word).mkQ_surjective f
    let f' : (⟨s.word⟩ : OldCategory D Sc cutoff) ⟶ ⟨t.word⟩ :=
      (ideal D Sc cutoff s.word t.word).mkQ a
    have h := congrArg (fun g => (Q).map g)
      ((Distinct.cross_supernatural D Sc cutoff i j).naturality_twist f')
    simp only [Functor.map_comp, map_twist] at h
    rw [map_twist]
    exact h

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The prescribed distinct mate through coefficient truncation

Brundan–Ellis (1.12): retain the positive old crossing under the selected
append quotient comparison, with the genuine restriction-square inverse
on its source. Ordinary coefficient coordinates are changed before the
old and truncated coends are composed. No flatness assumption is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i j : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Oi" => append D Sc cutoff i
local notation "Oj" => append D Sc cutoff j
local notation "Ti" => truncatedAppend D Sc cutoff N [i]
local notation "Tj" => truncatedAppend D Sc cutoff N [j]
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "R" => CategoryTheory.Functor.obj (BalancedInduction.restriction Oj) RM
local notation "L" => CategoryTheory.Functor.obj (BalancedInduction.restriction Tj) M
local notation "e" => CategoryTheory.Iso.symm (weightedAppendRestrictionIso D Sc cutoff N j M)

private theorem conjugate_equiv_forward
    {V U W Z : Type u} [AddCommMonoid V] [Module k V]
    [AddCommMonoid U] [Module k U] [AddCommMonoid W] [Module k W]
    [AddCommMonoid Z] [Module k Z]
    (a : V ≃ₗ[k] U) (f : V ≃ₗ[k] W) (b : W ≃ₗ[k] Z) (g : U →ₗ[k] Z)
    (h : b.toLinearMap ∘ₗ f.toLinearMap = g ∘ₗ a.toLinearMap) :
    ((a.symm.trans f).trans b).toLinearMap = g := by
  ext x
  obtain ⟨y, rfl⟩ := a.surjective x
  have hy := LinearMap.congr_fun h y
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using hy

/-- The old and truncated mixed source coends are compared by chosen isomorphisms. -/
def truncatedDistinctSourceEquiv (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj Oi ((Oj) ⋙ (RM).toFunctor) w ≃ₗ[k]
      BalancedInduction.Obj Ti ((Tj) ⋙ M.toFunctor) ((Q).obj w) :=
  ((BalancedInduction.restrictionCoendCoordinates Oi Oj RM w).symm.trans
    (weightedAppendSourceLinearEquiv D Sc cutoff N i R L e w)).trans
      (BalancedInduction.restrictionCoendCoordinates Ti Tj M ((Q).obj w))

/-- Its forward map retains the selected quotient chart and the even restriction square. -/
def truncatedDistinctSourceLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj Oi ((Oj) ⋙ (RM).toFunctor) w →ₗ[k]
      BalancedInduction.Obj Ti ((Tj) ⋙ M.toFunctor) ((Q).obj w) :=
  (BalancedInduction.restrictionCoendCoordinates Ti Tj M ((Q).obj w)).toLinearMap ∘ₗ
    weightedAppendSourceLinear D Sc cutoff N i R L (e).hom w ∘ₗ
      (BalancedInduction.restrictionCoendCoordinates Oi Oj RM w).symm.toLinearMap

/-- The source chart is a genuine linear equivalence of the specified mixed coends. -/
theorem truncatedDistinctSourceEquiv_hom (w : OldCategory D Sc cutoff) :
    (truncatedDistinctSourceEquiv D Sc cutoff N i j M w).toLinearMap =
      truncatedDistinctSourceLinear D Sc cutoff N i j M w := by
  rw [truncatedDistinctSourceEquiv, LinearEquiv.coe_trans, LinearEquiv.coe_trans,
    weightedAppendSourceLinearEquiv_hom D Sc cutoff N i R L e
      (weightedAppendRestrictionIso_inv_mem D Sc cutoff N j M) w]
  rfl

/-- Every whole coefficient arrow is sent to its literal quotient, with its vector unchanged. -/
theorem truncatedDistinctSourceLinear_tensor (s w : OldCategory D Sc cutoff)
    (g : (Oi).obj s ⟶ w) (b : (RM).obj ((Oj).obj s)) :
    truncatedDistinctSourceLinear D Sc cutoff N i j M w
      (BalancedInduction.tensor Oi ((Oj) ⋙ (RM).toFunctor) s g b) =
      BalancedInduction.tensor Ti ((Tj) ⋙ M.toFunctor) ((Q).obj s) ((Q).map g) b := by
  rw [truncatedDistinctSourceLinear, LinearMap.comp_apply, LinearMap.comp_apply,
    BalancedInduction.restrictionCoendCoordinates_inv_tensor,
    weightedAppendSourceLinear_tensor]
  have hb : (e).hom.app 0 s b = b := rfl
  rw [hb]
  exact BalancedInduction.restrictionCoendCoordinates_hom_tensor Ti Tj M
    ((Q).obj s) ((Q).obj w) ((Q).map g) b

/-- The target chart is the same selected i-append comparison at the j-output word. -/
def truncatedDistinctTargetEquiv (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj Oi (RM).toFunctor ((Oj).obj w) ≃ₗ[k]
      BalancedInduction.Obj Ti M.toFunctor ((Tj).obj ((Q).obj w)) :=
  weightedAppendLinearEquiv D Sc cutoff N i M ((Oj).obj w)

/-- The target forward map is the selected quotient comparison at the j-output. -/
def truncatedDistinctTargetLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj Oi (RM).toFunctor ((Oj).obj w) →ₗ[k]
      BalancedInduction.Obj Ti M.toFunctor ((Tj).obj ((Q).obj w)) :=
  weightedAppendComparisonLinear D Sc cutoff N i M ((Oj).obj w)

theorem truncatedDistinctTargetEquiv_hom (w : OldCategory D Sc cutoff) :
    (truncatedDistinctTargetEquiv D Sc cutoff N i j M w).toLinearMap =
      truncatedDistinctTargetLinear D Sc cutoff N i j M w := rfl

/-- Quotienting retains the full target coefficient arrow and input vector. -/
theorem truncatedDistinctTargetLinear_tensor
    (s w : OldCategory D Sc cutoff) (g : (Oi).obj ((Oj).obj s) ⟶ (Oj).obj w)
    (b : (RM).obj ((Oj).obj s)) :
    truncatedDistinctTargetLinear D Sc cutoff N i j M w
      (BalancedInduction.tensor Oi (RM).toFunctor ((Oj).obj s) g b) =
      BalancedInduction.tensor Ti M.toFunctor ((Q).obj ((Oj).obj s)) ((Q).map g) b :=
  appendWeightedModuleIso_hom_tensor D Sc cutoff N i M ((Oj).obj s) ((Oj).obj w) g b

private theorem quotient_map_append (s w : OldCategory D Sc cutoff) (f : s ⟶ w) :
    (Q).map ((Oj).map f) = (Tj).map ((Q).map f) := by
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff s.word w.word).mkQ_surjective f
  rfl

/-- The positive mixed coefficient projects with its entire parity twist. -/
theorem truncatedDistinctMate_coefficient
    (s w : OldCategory D Sc cutoff) (g : (Oi).obj s ⟶ w) :
    (Q).map (Distinct.crossComponent D Sc cutoff i j s ≫
      twist k (D.parity i * D.parity j) ((Oj).map g)) =
      truncatedDistinctCrossComponent D Sc cutoff N i j ((Q).obj s) ≫
        twist k (D.parity i * D.parity j) ((Tj).map ((Q).map g)) := by
  rw [Functor.map_comp, map_twist, oldTruncateFunctor_map_distinctCross, quotient_map_append]
  rfl

private theorem quotient_append_obj (a : I) (s : OldCategory D Sc cutoff) :
    (Q).obj ((append D Sc cutoff a).obj s) =
      (truncatedAppend D Sc cutoff N [a]).obj ((Q).obj s) := rfl

/-- The whole prescribed positive distinct mate commutes with the selected quotient charts. -/
theorem truncatedDistinctMateLinear_square (w : OldCategory D Sc cutoff) :
    truncatedDistinctTargetLinear D Sc cutoff N i j M w ∘ₗ
        Distinct.moduleMateLinear D Sc cutoff i j RM w =
      BalancedInduction.orderedMixedMateCoend Ti Tj
        (truncatedDistinctCross_supernatural D Sc cutoff N i j) M ((Q).obj w) ∘ₗ
          truncatedDistinctSourceLinear D Sc cutoff N i j M w := by
  apply BalancedInduction.hom_ext
  intro s g b
  have hOld := Distinct.moduleMateLinear_tensor D Sc cutoff i j RM s w g b
  generalize hc : (Distinct.crossComponent D Sc cutoff i j s ≫
    twist k (D.parity i * D.parity j) ((Oj).map g)) = c' at hOld
  have hLeft := congrArg (truncatedDistinctTargetLinear D Sc cutoff N i j M w) hOld
  have hTarget := truncatedDistinctTargetLinear_tensor D Sc cutoff N i j M s w c' b
  have hSource := truncatedDistinctSourceLinear_tensor D Sc cutoff N i j M s w g b
  have hRight := congrArg
    (BalancedInduction.orderedMixedMateCoend Ti Tj
      (truncatedDistinctCross_supernatural D Sc cutoff N i j) M ((Q).obj w)) hSource
  have hNew := BalancedInduction.orderedMixedMateCoend_tensor (k := k) Ti Tj
    (truncatedDistinctCross_supernatural D Sc cutoff N i j) M ((Q).obj s) ((Q).obj w) ((Q).map g) b
  have hCoef := (congrArg (fun f => (Q).map f) hc).symm.trans
    (truncatedDistinctMate_coefficient D Sc cutoff N i j s w g)
  have hTensor := congrArg (fun a => BalancedInduction.tensor Ti M.toFunctor
    ((Tj).obj ((Q).obj s)) a b) hCoef
  simp only [quotient_append_obj] at hTarget
  simp only [LinearMap.comp_apply]
  exact (hLeft.trans (hTarget.trans hTensor)).trans (hRight.trans hNew).symm

/-- The explicit decoder is the old PBW inverse between the selected quotient charts. -/
def truncatedDistinctMateEquivAtOld (hij : i ≠ j) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj Ti (Tj ⋙ M.toFunctor) ((Q).obj w) ≃ₗ[k]
      BalancedInduction.Obj Ti M.toFunctor ((Tj).obj ((Q).obj w)) :=
  ((truncatedDistinctSourceEquiv D Sc cutoff N i j M w).symm.trans
    (Distinct.moduleMateUnderlyingEquiv D Sc cutoff i j hij RM w)).trans
      (truncatedDistinctTargetEquiv D Sc cutoff N i j M w)

/-- Its forward map is the prescribed positive cup-crossing-cap on every vector. -/
theorem truncatedDistinctMateEquivAtOld_hom (hij : i ≠ j) (w : OldCategory D Sc cutoff) :
    (truncatedDistinctMateEquivAtOld D Sc cutoff N i j M hij w).toLinearMap =
      BalancedInduction.orderedMixedMateCoend Ti Tj
        (truncatedDistinctCross_supernatural D Sc cutoff N i j) M ((Q).obj w) := by
  apply conjugate_equiv_forward
  rw [truncatedDistinctSourceEquiv_hom, truncatedDistinctTargetEquiv_hom,
    Distinct.moduleMateUnderlyingEquiv_toLinearMap]
  exact truncatedDistinctMateLinear_square D Sc cutoff N i j M w

/-- The prescribed mixed mate is bijective on every quotient object. -/
theorem truncatedDistinctMate_bijective (hij : i ≠ j)
    (w : TruncatedCategory D Sc cutoff N) :
    Function.Bijective (BalancedInduction.orderedMixedMateCoend Ti Tj
      (truncatedDistinctCross_supernatural D Sc cutoff N i j) M w) := by
  have h : Function.Bijective (BalancedInduction.orderedMixedMateCoend Ti Tj
      (truncatedDistinctCross_supernatural D Sc cutoff N i j) M ((Q).obj ⟨w.word⟩)) := by
    rw [← truncatedDistinctMateEquivAtOld_hom D Sc cutoff N i j M hij ⟨w.word⟩]
    exact (truncatedDistinctMateEquivAtOld D Sc cutoff N i j M hij ⟨w.word⟩).bijective
  have hw : (Q).obj (⟨w.word⟩ : OldCategory D Sc cutoff) = w := by cases w; rfl
  rw [hw] at h
  exact h

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The prescribed distinct mate at canonical truncated content

Brundan–Ellis (1.12): compare the positive rectangular cup-crossing-cap
on canonical multiset-content modules with the proved global truncated
mate through the selected full-inclusion charts. Neither coefficient
parity nor the ordinary right action is discarded.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i j : I)

/-- The named canonical target proof is shared by the chosen append charts. -/
theorem contentBlockCanonicalSum (δ : Multiset I) (σ : List I) :
    δ + (σ : Multiset I) = δ + (σ : Multiset I) := rfl

/-- The common upper content keeps the prescribed j,i order as its index. -/
abbrev contentBlockDistinctUpper : Multiset I := (β + ([j] : Multiset I)) + ([i] : Multiset I)

theorem contentBlockDistinctUpper_eq :
    (β + ([i] : Multiset I)) + ([j] : Multiset I) = contentBlockDistinctUpper β i j := by
  unfold contentBlockDistinctUpper
  ac_rfl

local notation "γ" => contentBlockDistinctUpper β i j
local notation "hM" => contentBlockDistinctUpper_eq β i j
local notation "J" => contentAppendTo D Sc cutoff N β [j] (β + ([j] : Multiset I)) (contentBlockCanonicalSum β [j])
local notation "K" => contentAppendTo D Sc cutoff N β [i] (β + ([i] : Multiset I)) (contentBlockCanonicalSum β [i])
local notation "L" => contentAppendTo D Sc cutoff N (β + ([j] : Multiset I)) [i] γ (contentBlockCanonicalSum (β + ([j] : Multiset I)) [i])
local notation "U" => contentAppendTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ hM
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Qi" => contentInclusion D Sc cutoff N (β + ([i] : Multiset I))
local notation "Qj" => contentInclusion D Sc cutoff N (β + ([j] : Multiset I))
local notation "A" => truncatedAppend D Sc cutoff N [i]
local notation "B" => truncatedAppend D Sc cutoff N [j]

/-- The independently prescribed positive distinct crossing in the common upper block. -/
def contentBlockDistinctCross (s : ContentCategory D Sc cutoff N β) :
    (J ⋙ L).obj s ⟶ (K ⋙ U).obj s :=
  truncatedDistinctCrossComponent D Sc cutoff N i j s.obj

theorem contentBlockDistinctCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j) (contentBlockDistinctCross D Sc cutoff N β i j) where
  mem s := (truncatedDistinctCross_supernatural D Sc cutoff N i j).mem s.obj
  naturality := by
    intro s t p f hf
    exact (truncatedDistinctCross_supernatural D Sc cutoff N i j).naturality hf

theorem contentBlockRestrictionExtension_even
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I))) :
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β j _ (contentBlockCanonicalSum β [j]) M).hom ∈
      parity (R := k) _ _ 0 := by
  rw [contentAppendToRestrictionExtensionIso_hom]
  have h := comp_mem
    (map_mem (BalancedInduction.induction Q₀)
      (map_mem (BalancedInduction.restriction J) (BalancedInduction.adjunctionUnit_mem Qj M)))
    (BalancedInduction.adjunctionCounit_mem Q₀
      ((BalancedInduction.restriction B).obj (BalancedInduction.induced Qj M)))
  set_option backward.dsimp.instances true in
    dsimp only [BalancedInduction.induction, contentAppend, BalancedInduction.adjunction] at h ⊢
  simpa only [zero_add] using h

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Inverting the prescribed distinct mate on canonical content

Brundan–Ellis (1.12): the chosen full-content source and target charts
identify the whole positive content mate with the proved global
truncated mate. The direct generic charts retain all output object
transports and ordinary coend balance before specializing content.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
private theorem block_bijective_of_square {V W U Z : Type u}
    (f : V → W) (a : V → U) (b : W → Z) (g : U → Z)
    (ha : Function.Bijective a) (hb : Function.Bijective b) (hg : Function.Bijective g)
    (h : ∀ x, b (f x) = g (a x)) : Function.Bijective f := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply ha.injective
    apply hg.injective
    rw [← h x, ← h y, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hg.surjective (b y)
    obtain ⟨x, hx⟩ := ha.surjective z
    exact ⟨x, hb.injective ((h x).trans ((congrArg g hx).trans hz))⟩

private theorem linearMap_bijective_of_square
    {k V W U Z : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid U] [Module k U] [AddCommMonoid Z] [Module k Z]
    (f : V →ₗ[k] W) (a : V →ₗ[k] U) (b : W →ₗ[k] Z) (g : U →ₗ[k] Z)
    (ha : Function.Bijective a) (hb : Function.Bijective b) (hg : Function.Bijective g)
    (h : b ∘ₗ f = g ∘ₗ a) : Function.Bijective f := by
  apply block_bijective_of_square f a b g ha hb hg
  intro x
  simpa only [LinearMap.comp_apply] using LinearMap.congr_fun h x

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i j : I)
local notation "γ" => contentBlockDistinctUpper β i j
local notation "hUi" => contentBlockDistinctUpper_eq β i j
local notation "hi" => contentBlockCanonicalSum β [i]
local notation "hj" => contentBlockCanonicalSum β [j]
local notation "hijUpper" => contentBlockCanonicalSum (β + ([j] : Multiset I)) [i]
local notation "J" => contentAppendTo D Sc cutoff N β [j] (β + ([j] : Multiset I)) hj
local notation "K" => contentAppendTo D Sc cutoff N β [i] (β + ([i] : Multiset I)) hi
local notation "L" => contentAppendTo D Sc cutoff N (β + ([j] : Multiset I)) [i] γ hijUpper
local notation "U" => contentAppendTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ hUi
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Qi" => contentInclusion D Sc cutoff N (β + ([i] : Multiset I))
local notation "Qj" => contentInclusion D Sc cutoff N (β + ([j] : Multiset I))
local notation "Qw" => contentInclusion D Sc cutoff N γ
local notation "A" => truncatedAppend D Sc cutoff N [i]
local notation "B" => truncatedAppend D Sc cutoff N [j]
local notation "hJ" => contentAppendTo_inclusion D Sc cutoff N β [j] _ hj
local notation "hK" => contentAppendTo_inclusion D Sc cutoff N β [i] _ hi
local notation "hL" => contentAppendTo_inclusion D Sc cutoff N (β + ([j] : Multiset I)) [i] γ hijUpper
local notation "hU" => contentAppendTo_inclusion D Sc cutoff N (β + ([i] : Multiset I)) [j] γ hUi
local notation "hα" => contentBlockDistinctCross_supernatural D Sc cutoff N β i j
local notation "hχ" => truncatedDistinctCross_supernatural D Sc cutoff N i j
local notation "Ext" => BalancedInduction.induced Qj
local notation "Input" => CategoryTheory.Functor.obj (BalancedInduction.restriction J)
local notation "Fiso" => contentAppendToRestrictionExtensionIso D Sc cutoff N β j _ hj
local notation "Source" => BalancedInduction.fullSquareOrdinarySourceLinear (k := k) K Qi Q₀ A hK
local notation "Target" => BalancedInduction.fullSquareTargetLinear (k := k) L Qw Qj A hL

private theorem blockSquare_eqToHom (δ : Multiset I) (σ : List I) (ε : Multiset I)
    (h : δ + (σ : Multiset I) = ε) (s : ContentCategory D Sc cutoff N δ) :
    eqToHom (congrArg (fun F => F.obj s) (contentAppendTo_inclusion D Sc cutoff N δ σ ε h)) =
      𝟙 ((truncatedAppend D Sc cutoff N σ).obj ((contentInclusion D Sc cutoff N δ).obj s)) := rfl

/-- The selected F chart takes its source inclusion unit to the transported target unit. -/
theorem contentBlockDistinctRestriction_unit
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (s : ContentCategory D Sc cutoff N β) (b : M.obj ((J).obj s)) :
    (Fiso M).hom.total ((Q₀).obj s) (BalancedInduction.unit Q₀ (Input M).toFunctor s b) =
      (Ext M).map (eqToHom (congrArg (fun F => F.obj s) hJ))
        (BalancedInduction.unit Qj M.toFunctor ((J).obj s) b) := by
  have hF := contentAppendToRestrictionExtensionIso_tensor D Sc cutoff N β j _ hj M
    ((Q₀).obj s) s (𝟙 ((Q₀).obj s)) b
  have hCoeff : (B).map (𝟙 ((Q₀).obj s)) =
      eqToHom (congrArg (fun F => F.obj s) hJ) := by
    rw [(B).map_id, blockSquare_eqToHom]
  have hC := congrArg (fun a : (Qj).obj ((J).obj s) ⟶ (B).obj ((Q₀).obj s) =>
    BalancedInduction.tensor Qj M.toFunctor ((J).obj s) a b) hCoeff
  have hAction := BalancedInduction.fullSourceInduced_map_unit (k := k) Qj M ((J).obj s)
    ((B).obj ((Q₀).obj s)) (eqToHom (congrArg (fun F => F.obj s) hJ)) b
  exact (hF.trans hC).trans hAction.symm

/-- The entire prescribed canonical mate commutes with both chosen full-content charts. -/
theorem contentBlockDistinctMateLinear_square
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) :
    Target M ((U).obj t) ((B).obj ((Qi).obj t)) (congrArg (fun F => F.obj t) hU) ∘ₗ
      BalancedInduction.orderedRectangularMateLinear J K L U hα M t =
      BalancedInduction.orderedMixedMateCoend A B hχ (Ext M) ((Qi).obj t) ∘ₗ
        Source (Input M) B (Ext M) (Fiso M) t := by
  refine BalancedInduction.fullContentMate_square (k := k) J K L U Q₀ Qj Qi Qw A B
    hJ hK hL hU hα hχ M (Fiso M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β j M)
    (contentBlockDistinctRestriction_unit D Sc cutoff N β j M) ?_ t
  intro s z g
  rw [CategoryTheory.Functor.map_comp, map_twist]
  dsimp only [contentAppendTo, contentInclusion, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.comp_map]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- The prescribed positive canonical content mate is bijective for distinct colours. -/
theorem contentBlockDistinctMateLinear_bijective (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) :
    Function.Bijective (BalancedInduction.orderedRectangularMateLinear J K L U hα M t) := by
  apply linearMap_bijective_of_square (k := k)
    (BalancedInduction.orderedRectangularMateLinear J K L U hα M t)
    (Source (Input M) B (Ext M) (Fiso M) t)
    (Target M ((U).obj t) ((B).obj ((Qi).obj t)) (congrArg (fun F => F.obj t) hU))
    (BalancedInduction.orderedMixedMateCoend A B hχ (Ext M) ((Qi).obj t))
    (BalancedInduction.fullSquareOrdinarySourceLinear_bijective K Qi Q₀ A hK
      (Input M) B (Ext M) (Fiso M) t)
    (BalancedInduction.fullSquareTargetLinear_bijective L Qw Qj A hL M ((U).obj t)
      ((B).obj ((Qi).obj t)) (congrArg (fun F => F.obj t) hU))
    (truncatedDistinctMate_bijective D Sc cutoff N i j (Ext M) hij ((Qi).obj t))
  exact contentBlockDistinctMateLinear_square D Sc cutoff N β i j M t

/-- The given canonical module mate is invertible, with no extra inverse premise. -/
theorem contentBlockDistinctMate_isIso (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I))) :
    IsIso (BalancedInduction.orderedRectangularMateComponent J K L U hα M) := by
  rw [← BalancedInduction.rectangularMateModuleIso_hom J K L U hα M
    (contentBlockDistinctMateLinear_bijective D Sc cutoff N β i j hij M)]
  infer_instance

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Distinct mates with prescribed successor contents

Brundan–Ellis (1.12) on original weight blocks uses their stored lower
and upper successor contents. This transports the proved canonical
content inverse to arbitrary certificates of the same four sums, while
retaining the literal append functors and the positive crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (β : Multiset I) (i j : I) (δj δi γ : Multiset I)
  (hj : β + ([j] : Multiset I) = δj) (hi : β + ([i] : Multiset I) = δi)
  (hL : δj + ([i] : Multiset I) = γ) (hU : δi + ([j] : Multiset I) = γ)
local notation "J" => contentAppendTo D Sc cutoff bound β [j] δj hj
local notation "K" => contentAppendTo D Sc cutoff bound β [i] δi hi
local notation "L" => contentAppendTo D Sc cutoff bound δj [i] γ hL
local notation "U" => contentAppendTo D Sc cutoff bound δi [j] γ hU

/-- The literal positive crossing with all four prescribed content certificates retained. -/
def contentDistinctTargetsCross (s : ContentCategory D Sc cutoff bound β) :
    (J ⋙ L).obj s ⟶ (K ⋙ U).obj s :=
  truncatedDistinctCrossComponent D Sc cutoff bound i j s.obj

theorem contentDistinctTargetsCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j)
      (contentDistinctTargetsCross D Sc cutoff bound β i j δj δi γ hj hi hL hU) where
  mem s := (truncatedDistinctCross_supernatural D Sc cutoff bound i j).mem s.obj
  naturality := by
    intro s t p f hf
    exact (truncatedDistinctCross_supernatural D Sc cutoff bound i j).naturality hf

local notation "hα" => contentDistinctTargetsCross_supernatural D Sc cutoff bound β i j δj δi γ hj hi hL hU

/-- The actual positive module mate remains invertible for every choice of successor certificates. -/
theorem contentDistinctTargetsMate_isIso (hij : i ≠ j) (M : ContentModules D Sc cutoff bound δj) :
    IsIso (BalancedInduction.orderedRectangularMateComponent J K L U hα M) := by
  subst δj
  subst δi
  subst γ
  exact contentBlockDistinctMate_isIso D Sc cutoff bound β i j hij M

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Positive distinct crossings in rectangular content coordinates

The crossing in the Brundan–Ellis (1.12) rectangular mate agrees with
the selected affine word crossing through the chosen induction
composition comparisons, including prescribed successor contents.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (β : Multiset I) (i j : I) (δj δi γ : Multiset I)
  (hj : β + ([j] : Multiset I) = δj) (hi : β + ([i] : Multiset I) = δi)
  (hL : δj + ([i] : Multiset I) = γ) (hU : δi + ([j] : Multiset I) = γ)
  (hji : β + ([j,i] : Multiset I) = γ) (hij : β + ([i,j] : Multiset I) = γ)
private theorem contentCompTo_eq_compOfEq
    (η : Multiset I) (σ : List I) (δ : Multiset I) (hδ : η + (σ : Multiset I) = δ)
    (τ : List I) (ζ : Multiset I) (hζ : δ + (τ : Multiset I) = ζ)
    (h : η + ((σ ++ τ : List I) : Multiset I) = ζ) :
    contentInductionCompTo D Sc cutoff bound η σ δ hδ τ ζ hζ h =
      inductionCompOfEq (contentAppendTo D Sc cutoff bound η σ δ hδ)
        (contentAppendTo D Sc cutoff bound δ τ ζ hζ)
        (contentAppendTo D Sc cutoff bound η (σ ++ τ) ζ h)
        (contentAppend_compTo_eq D Sc cutoff bound η σ δ hδ τ ζ hζ h) := by
  subst δ
  rfl

/-- Reversed induction labels retain the physical crossing degree. -/
theorem contentCrossAffine_reverse_mem : contentCrossAffine D Sc j i ∈
    parity (R := k) _ _ (D.parity i * D.parity j) := by
  simpa only [mul_comm] using contentCrossAffine_mem D Sc j i

local notation "J" => contentAppendTo D Sc cutoff bound β [j] δj hj
local notation "K" => contentAppendTo D Sc cutoff bound β [i] δi hi
local notation "L" => contentAppendTo D Sc cutoff bound δj [i] γ hL
local notation "U" => contentAppendTo D Sc cutoff bound δi [j] γ hU
local notation "F" => contentAppendTo D Sc cutoff bound β ([j] ++ [i]) γ hji
local notation "G" => contentAppendTo D Sc cutoff bound β ([i] ++ [j]) γ hij
local notation "eF" => contentAppend_compTo_eq D Sc cutoff bound β [j] δj hj [i] γ hL hji
local notation "eG" => contentAppend_compTo_eq D Sc cutoff bound β [i] δi hi [j] γ hU hij

/-- The positive crossing is the affine crossing with its two word endpoints transported. -/
theorem contentDistinctTargetsCross_coefficient (hne : i ≠ j)
    (s : ContentCategory D Sc cutoff bound β) :
    contentDistinctTargetsCross D Sc cutoff bound β i j δj δi γ hj hi hL hU s =
      eqToHom (congrArg (fun H => CategoryTheory.Functor.obj H s) eF) ≫
        contentAppendToComponent D Sc cutoff bound (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij (contentCrossAffine D Sc j i) s ≫
          eqToHom (congrArg (fun H => CategoryTheory.Functor.obj H s) eG).symm := by
  apply (conj_eqToHom_iff_heq
    (contentDistinctTargetsCross D Sc cutoff bound β i j δj δi γ hj hi hL hU s)
    (contentAppendToComponent D Sc cutoff bound (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij (contentCrossAffine D Sc j i) s)
    (congrArg (fun H => CategoryTheory.Functor.obj H s) eF)
    (congrArg (fun H => CategoryTheory.Functor.obj H s) eG)).mpr
  rw [contentCrossAffine_distinct D Sc j i hne.symm]
  exact truncatedDistinctCrossComponent_heq D Sc cutoff bound i j s.obj

/-- The word-induction crossing equals the rectangular crossing used by the content mate. -/
theorem contentDistinctTargetsCross_comparison (hne : i ≠ j)
    (P : ContentModules D Sc cutoff bound β) :
    ((contentInductionCompTo D Sc cutoff bound β [i] δi hi [j] γ hU hij).hom.app P ≫
      (contentInductionTransform D Sc cutoff bound (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij
        (contentCrossAffine_reverse_mem D Sc i j)).app (D.parity i * D.parity j) P) ≫
      (contentInductionCompTo D Sc cutoff bound β [j] δj hj [i] γ hL hji).inv.app P =
        BalancedInduction.rectangularCrossComponent J K L U
          (contentDistinctTargetsCross_supernatural D Sc cutoff bound β i j δj δi γ hj hi hL hU) P := by
  have h := inductionCompOfEq_cross J K L U F G eF eG
    (contentDistinctTargetsCross_supernatural D Sc cutoff bound β i j δj δi γ hj hi hL hU)
    (contentAppendTo_supernatural D Sc cutoff bound (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij (contentCrossAffine_reverse_mem D Sc i j))
    (contentDistinctTargetsCross_coefficient D Sc cutoff bound β i j δj δi γ hj hi hL hU hji hij hne) P
  dsimp only [contentInductionTo] at h ⊢
  simpa only [contentCompTo_eq_compOfEq, contentInductionTransform, inductionTransform_app_self] using h

end OddMath.QuiverHecke.ELV
end

end

section

/-! The normalized affine crossing with actual intermediate content targets.
The equal-colour branch retains its prescribed extra minus. -/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i j : I) (δj δi γ : Multiset I)
  (hj : β + ([j] : Multiset I) = δj) (hi : β + ([i] : Multiset I) = δi)
  (hL : δj + ([i] : Multiset I) = γ) (hU : δi + ([j] : Multiset I) = γ)
  (hji : β + ([j,i] : Multiset I) = γ) (hij : β + ([i,j] : Multiset I) = γ)
local notation "J" => contentAppendTo D Sc cutoff N β [j] δj hj
local notation "K" => contentAppendTo D Sc cutoff N β [i] δi hi
local notation "L" => contentAppendTo D Sc cutoff N δj [i] γ hL
local notation "U" => contentAppendTo D Sc cutoff N δi [j] γ hU
local notation "F" => contentAppendTo D Sc cutoff N β ([j] ++ [i]) γ hji
local notation "G" => contentAppendTo D Sc cutoff N β ([i] ++ [j]) γ hij
local notation "eF" => contentAppend_compTo_eq D Sc cutoff N β [j] δj hj [i] γ hL hji
local notation "eG" => contentAppend_compTo_eq D Sc cutoff N β [i] δi hi [j] γ hU hij

/-- The raw crossing coefficient, without a distinct-colour premise. -/
theorem contentTargetsCross_raw_coefficient (s : ContentCategory D Sc cutoff N β) :
    contentDistinctTargetsCross D Sc cutoff N β i j δj δi γ hj hi hL hU s =
      eqToHom (congrArg (fun H => CategoryTheory.Functor.obj H s) eF) ≫
        contentAppendToComponent D Sc cutoff N (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij
          (crossTwo D Sc j i) s ≫
        eqToHom (congrArg (fun H => CategoryTheory.Functor.obj H s) eG).symm := by
  apply (conj_eqToHom_iff_heq
    (contentDistinctTargetsCross D Sc cutoff N β i j δj δi γ hj hi hL hU s)
    (contentAppendToComponent D Sc cutoff N (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij
      (crossTwo D Sc j i) s)
    (congrArg (fun H => CategoryTheory.Functor.obj H s) eF)
    (congrArg (fun H => CategoryTheory.Functor.obj H s) eG)).mpr
  exact truncatedDistinctCrossComponent_heq D Sc cutoff N i j s.obj

/-- The physical rectangular coefficient with the chosen equal-colour normalization. -/
def normalizedContentTargetsCross (s : ContentCategory D Sc cutoff N β) :
    (J ⋙ L).obj s ⟶ (K ⋙ U).obj s :=
  if i = j then -contentDistinctTargetsCross D Sc cutoff N β i j δj δi γ hj hi hL hU s
  else contentDistinctTargetsCross D Sc cutoff N β i j δj δi γ hj hi hL hU s

theorem normalizedContentTargetsCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j)
      (normalizedContentTargetsCross D Sc cutoff N β i j δj δi γ hj hi hL hU) := by
  let hraw := contentDistinctTargetsCross_supernatural D Sc cutoff N β i j δj δi γ hj hi hL hU
  refine { mem := ?_, naturality := ?_ }
  · intro s
    dsimp only [normalizedContentTargetsCross]
    split_ifs
    · exact Submodule.neg_mem _ (hraw.mem s)
    · exact hraw.mem s
  · intro s t p f hf
    by_cases h : i = j
    · simp only [normalizedContentTargetsCross, ite_eq_left h]
      rw [Preadditive.comp_neg, hraw.naturality hf, Preadditive.neg_comp, smul_neg]
    · simpa only [normalizedContentTargetsCross, ite_eq_right h] using hraw.naturality hf

/-- The normalized rectangular coefficient is exactly the independently chosen
normalized affine crossing, including equal colours and all endpoint transports. -/
theorem normalizedContentTargetsCross_coefficient (s : ContentCategory D Sc cutoff N β) :
    normalizedContentTargetsCross D Sc cutoff N β i j δj δi γ hj hi hL hU s =
      eqToHom (congrArg (fun H => CategoryTheory.Functor.obj H s) eF) ≫
        contentAppendToComponent D Sc cutoff N (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij
          (contentCrossAffine D Sc j i) s ≫
        eqToHom (congrArg (fun H => CategoryTheory.Functor.obj H s) eG).symm := by
  by_cases h : i = j
  · subst j
    simp only [normalizedContentTargetsCross, contentCrossAffine_equal,
      contentAppendToComponent_neg, Preadditive.comp_neg, Preadditive.neg_comp]
    exact congrArg Neg.neg (contentTargetsCross_raw_coefficient D Sc cutoff N β i i δj δi γ hj hi hL hU hji hij s)
  · simp only [normalizedContentTargetsCross, ite_eq_right h, contentCrossAffine_distinct D Sc j i (Ne.symm h)]
    exact contentTargetsCross_raw_coefficient D Sc cutoff N β i j δj δi γ hj hi hL hU hji hij s

private theorem normalized_contentCompTo_eq_compOfEq
    (η : Multiset I) (σ : List I) (δ : Multiset I) (hδ : η + (σ : Multiset I) = δ)
    (τ : List I) (ζ : Multiset I) (hζ : δ + (τ : Multiset I) = ζ)
    (h : η + ((σ ++ τ : List I) : Multiset I) = ζ) :
    contentInductionCompTo D Sc cutoff N η σ δ hδ τ ζ hζ h =
      inductionCompOfEq (contentAppendTo D Sc cutoff N η σ δ hδ)
        (contentAppendTo D Sc cutoff N δ τ ζ hζ)
        (contentAppendTo D Sc cutoff N η (σ ++ τ) ζ h)
        (contentAppend_compTo_eq D Sc cutoff N η σ δ hδ τ ζ hζ h) := by
  subst δ
  rfl

/-- The independently chosen normalized word crossing is the normalized
rectangular crossing for every colour pair and every actual successor certificate. -/
theorem normalizedContentTargetsCross_comparison
    (P : ContentModules D Sc cutoff N β) :
    ((contentInductionCompTo D Sc cutoff N β [i] δi hi [j] γ hU hij).hom.app P ≫
      (contentInductionTransform D Sc cutoff N (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij
        (contentCrossAffine_reverse_mem D Sc i j)).app (D.parity i * D.parity j) P) ≫
      (contentInductionCompTo D Sc cutoff N β [j] δj hj [i] γ hL hji).inv.app P =
        BalancedInduction.rectangularCrossComponent J K L U
          (normalizedContentTargetsCross_supernatural D Sc cutoff N β i j δj δi γ hj hi hL hU) P := by
  have h := inductionCompOfEq_cross J K L U F G eF eG
    (normalizedContentTargetsCross_supernatural D Sc cutoff N β i j δj δi γ hj hi hL hU)
    (contentAppendTo_supernatural D Sc cutoff N (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij
      (contentCrossAffine_reverse_mem D Sc i j))
    (normalizedContentTargetsCross_coefficient D Sc cutoff N β i j δj δi γ hj hi hL hU hji hij) P
  dsimp only [contentInductionTo] at h ⊢
  simpa only [normalized_contentCompTo_eq_compOfEq, contentInductionTransform,
    inductionTransform_app_self] using h

end OddMath.QuiverHecke.ELV
end

end
