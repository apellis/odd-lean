import OddMath.QuiverHecke.CyclotomicAction.ELVMatrixFunctorNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixInverse

/-! # Fixed-output-content matrix inverses natural in input modules

DeformedMatrixComparison section 4. Whole finite-family input-module
naturality combines with the verified content-module component inverses.
The resulting natural isomorphisms retain every prescribed unit/cap entry,
both height signs, both moving parities and the zero-count principal mate.
Compatibility with the chosen content E/F composites remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
