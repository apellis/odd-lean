import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows

/-! # Inverse coefficient rows as fixed-content module maps

The normalized left cap in `SwappedVacuumNonpositiveBubbles.md`, §2,
comes from the prescribed inverse unit matrix. On fixed output content,
its coefficient rows are actual homogeneous module morphisms: project to
a shifted coordinate of the inverse and remove that prescribed shift.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
