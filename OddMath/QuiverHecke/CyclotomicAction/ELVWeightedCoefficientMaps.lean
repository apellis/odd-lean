import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedContentMatrixInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedCoefficientRows
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerVacuumCapComparison

/-! # Weighted inverse coefficients as canonical-content module maps

The coefficient cap in `SwappedVacuumCoordinates.md`, §6, must be a
homogeneous module map, retaining its signed naturality on coefficient
arrows. Project the actual prescribed content matrix inverse and remove
its original source parity shift; its empty component is the exact
weighted coefficient row already attached to the literal A/T vacuum.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u

private def weightedCoefficientProjectionNat
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) :
    (OddMath.FiniteSupermodule.product V).toFunctor ⟶ (V a).toFunctor where
  app t := LinearMap.proj a
  naturality _ _ _ := by apply LinearMap.ext; intro x; rfl

private theorem weightedCoefficientProjectionNat_mem
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) (t : C) :
    (weightedCoefficientProjectionNat V a).app t ∈ parity (R := k) _ _ 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q x hx
  rw [add_zero]
  change x a ∈ ((V a).obj t).part q
  change x ∈ (OddMath.FiniteSuperspace.product fun b => (V b).obj t).part q at hx
  exact (OddMath.FiniteSuperspace.mem_product_part _ q x).mp hx a

private def weightedCoefficientProjection
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) :
    OddMath.FiniteSupermodule.product V ⟶ V a :=
  SuperNatTrans.ofNatTrans (weightedCoefficientProjectionNat V a) (weightedCoefficientProjectionNat_mem V a)

private theorem weightedCoefficientProjection_total
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) (t : C) :
    (weightedCoefficientProjection V a).total t = LinearMap.proj a := by
  change (LinearMap.proj a : (OddMath.FiniteSupermodule.product V).obj t →ₗ[k] (V a).obj t) + 0 = _
  exact add_zero _

private theorem weightedCoefficientRestriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {F G : Superfunctor k A (SVec k)} (f : F ⟶ G) (t : C) :
    ((restriction Q).map f).total t = f.total (Q.obj t) := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "T" => truncatedAppend D Sc cutoff N [i]
local instance weightedContentCoefficientPi :
    PiSupercategory k (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :=
  supermodulePiSupercategory

/-- Project the given weighted content matrix inverse and remove exactly
the original r-th source shift. This is an actual module morphism. -/
def weightedContentCoefficientMap (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (r : Fin (contentUnitCount D cutoff i β)) :
    (restriction (contentInclusion D Sc cutoff N β)).obj
      ((restriction T).obj ((induction T).obj M)) ⟶
    (restriction (contentInclusion D Sc cutoff N β)).obj M :=
  (weightedContentUnitMatrixIso D Sc cutoff N i M β hh).inv ≫
    (restriction (contentInclusion D Sc cutoff N β)).map
      (weightedCoefficientProjection (weightedUnitMatrixFamily D Sc cutoff N i M _) (some r) ≫
        ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom)

/-- At genuine empty output, the canonical-content inverse has exactly
the given weighted component inverse; equality follows from its forward
field, rather than from an inverse compatibility premise. -/
theorem weightedContentUnitMatrixIso_vacuum_inv_total
    (hh : 0 ≤ contentCrossingHeight D cutoff i (0 : Multiset I)) :
    (weightedContentUnitMatrixIso D Sc cutoff N i M 0 hh).inv.total
      (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff N 0) =
    (weightedUnitMatrixComponentIso D Sc cutoff N i M (⟨[]⟩ : OldCategory D Sc cutoff) hh).inv := by
  have he : SVec.isoOfLinearEquiv
      (moduleIsoLinearEquiv (weightedContentUnitMatrixIso D Sc cutoff N i M 0 hh)
        (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff N 0)) =
      weightedUnitMatrixComponentIso D Sc cutoff N i M (⟨[]⟩ : OldCategory D Sc cutoff) hh := by
    apply Iso.ext
    change (weightedContentUnitMatrixIso D Sc cutoff N i M 0 hh).hom.total
        (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff N 0) = _
    rw [weightedContentUnitMatrixIso_hom_total, weightedUnitMatrixComponentIso_hom]
    rfl
  have hi := congrArg Iso.inv he
  exact hi

/-- The module row's genuine empty component is the literal normalized
weighted inverse coefficient, with its prescribed source unshift. -/
theorem weightedContentCoefficientMap_vacuum_total
    (hh : 0 ≤ contentCrossingHeight D cutoff i (0 : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (0 : Multiset I)))
    (z : (((restriction T).obj ((induction T).obj M)).obj
      ((oldTruncateFunctor D Sc cutoff N).obj (⟨[]⟩ : OldCategory D Sc cutoff)))) :
    (weightedContentCoefficientMap D Sc cutoff N i M 0 hh r).total
      (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff N 0) z =
      weightedUnitCoefficient D Sc cutoff N i M (⟨[]⟩ : OldCategory D Sc cutoff) hh r z := by
  simp only [weightedContentCoefficientMap, Superfunctor.comp_total,
    weightedCoefficientRestriction_total, weightedCoefficientProjection_total, SVec.comp_apply]
  rw [weightedContentUnitMatrixIso_vacuum_inv_total]
  rfl

namespace PowerVacuumCoefficient
variable [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "W" => weightedVacuum D Sc cutoff L
local notation "Q₀" => contentInclusion D Sc cutoff bound (0 : Multiset I)
local notation "T₀" => truncatedAppend D Sc cutoff bound [i]

omit [Fintype I] in
private theorem coefficientCap_height :
    0 ≤ contentCrossingHeight D cutoff i (0 : Multiset I) := by
  simp [contentCrossingHeight]
private def coefficientCap_top (hN : 0 < cutoff i) : Fin (contentUnitCount D cutoff i (0 : Multiset I)) :=
  ⟨cutoff i - 1, by
    change cutoff i - 1 < contentUnitCount D cutoff i (([] : List I) : Multiset I)
    rw [VacuumCoefficient.count]
    omega⟩

/-- The actual weighted last inverse row as a canonical-content module
map on the literal descended A/T vacuum. -/
def weightedCoefficientCap (hN : 0 < cutoff i) :
    (restriction Q₀).obj ((restriction T₀).obj ((induction T₀).obj W)) ⟶
      (restriction Q₀).obj W :=
  weightedContentCoefficientMap D Sc cutoff bound i W 0
    (coefficientCap_height D cutoff i) (coefficientCap_top D cutoff i hN)

/-- The literal-T scalar-valued row is the actual canonical-content
module cap at empty output, with its original even empty coordinate. -/
theorem weightedFunctional_coefficientCap (hN : 0 < cutoff i)
    (z : (((restriction T₀).obj ((induction T₀).obj W)).obj
      ((oldTruncateFunctor D Sc cutoff bound).obj (⟨[]⟩ : OldCategory D Sc cutoff)))) :
    weightedFunctional D Sc cutoff L i hN z =
      (weightedEmptyEquiv D Sc cutoff L).symm
        ((weightedCoefficientCap D Sc cutoff i L hN).total
          (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff bound 0) z) := by
  have h := weightedContentCoefficientMap_vacuum_total D Sc cutoff bound i W
    (coefficientCap_height D cutoff i) (coefficientCap_top D cutoff i hN) z
  exact (congrArg (weightedEmptyEquiv D Sc cutoff L).symm h).symm

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELVOld
