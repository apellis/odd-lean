import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixFunctorInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCoefficientCaps

/-! # Input-module naturality of inverse-defined coefficient caps

The normalized left cap of `SwappedVacuumNonpositiveBubbles.md`, §2,
uses a prescribed inverse coefficient and its original parity unshift.
The unshift is supernatural on odd input maps. We retain that sign when
assembling the cap family, including the empty output content.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
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
local instance : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
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

end OddMath.QuiverHecke.ELVOld
