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

theorem capMatrixModuleMap_total (i : I) (m : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    (capMatrixModuleMap D Sc cutoff i m M).total t =
      capMatrixComponent D Sc cutoff i M m t := by
  apply LinearMap.ext
  intro x
  funext a
  exact FiniteSupermodule.rowsHom_total_apply _ _ _ _ _

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

/-- The restricted forward cap map is the existing literal content isomorphism. -/
theorem contentCapMatrixIso_hom_eq (i : I) (ν : List I)
    (hh : contentCrossingHeight D cutoff i (ν : Multiset I) ≤ 0)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (contentCapMatrixIso D Sc cutoff M i ν hh).hom =
      (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).map
        (capMatrixModuleMap D Sc cutoff i
          (contentCapCount D cutoff i (ν : Multiset I)) M) := by
  apply FiniteSupermodule.hom_ext_total
  intro t
  change (contentCapMatrixIso D Sc cutoff M i ν hh).hom.total t =
    (capMatrixModuleMap D Sc cutoff i
      (contentCapCount D cutoff i (ν : Multiset I)) M).total t.obj
  rw [contentCapMatrixIso_hom_total, capMatrixModuleMap_total]

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
    exact (NatTrans.whiskerRight
      (unitMatrixModuleNatTrans D Sc cutoff i (contentUnitCount D cutoff i (ν : Multiset I)))
      (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν))).naturality f)

/-- The output-content restricted cap matrix, natural in the input module. -/
def contentCapMatrixFunctorNatIso (i : I) (ν : List I)
    (hh : contentCrossingHeight D cutoff i (ν : Multiset I) ≤ 0) :
    ((BalancedInduction.restriction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff i)) ⋙
        BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)) ≅
    (capMatrixTargetFunctor D Sc cutoff i (contentCapCount D cutoff i (ν : Multiset I)) ⋙
      BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)) :=
  NatIso.ofComponents (fun M => contentCapMatrixIso D Sc cutoff M i ν hh) (by
    intro M N f
    simp only [contentCapMatrixIso_hom_eq]
    exact (NatTrans.whiskerRight
      (capMatrixModuleNatTrans D Sc cutoff i (contentCapCount D cutoff i (ν : Multiset I)))
      (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν))).naturality f)

/-- The functor isomorphism retains the prescribed unit matrix at every output. -/
theorem contentUnitMatrixFunctorNatIso_hom_total (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldContentCategory D Sc cutoff ν) :
    ((contentUnitMatrixFunctorNatIso D Sc cutoff i ν hh).hom.app M).total t =
      unitMatrixComponent D Sc cutoff i M (contentUnitCount D cutoff i (ν : Multiset I)) t.obj :=
  contentUnitMatrixIso_hom_total D Sc cutoff M i ν hh t

/-- The functor isomorphism retains the prescribed cap matrix at every output. -/
theorem contentCapMatrixFunctorNatIso_hom_total (i : I) (ν : List I)
    (hh : contentCrossingHeight D cutoff i (ν : Multiset I) ≤ 0)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldContentCategory D Sc cutoff ν) :
    ((contentCapMatrixFunctorNatIso D Sc cutoff i ν hh).hom.app M).total t =
      capMatrixComponent D Sc cutoff i M (contentCapCount D cutoff i (ν : Multiset I)) t.obj :=
  contentCapMatrixIso_hom_total D Sc cutoff M i ν hh t

/-- Both directions have even module components, before any factor-action transport. -/
theorem contentUnitMatrixFunctorNatIso_even (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (contentUnitMatrixFunctorNatIso D Sc cutoff i ν hh).hom.app M ∈ parity (R := k) _ _ 0 ∧
      (contentUnitMatrixFunctorNatIso D Sc cutoff i ν hh).inv.app M ∈ parity (R := k) _ _ 0 :=
  contentUnitMatrixIso_even D Sc cutoff M i ν hh

/-- The cap isomorphism and its inverse have even module components. -/
theorem contentCapMatrixFunctorNatIso_even (i : I) (ν : List I)
    (hh : contentCrossingHeight D cutoff i (ν : Multiset I) ≤ 0)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (contentCapMatrixFunctorNatIso D Sc cutoff i ν hh).hom.app M ∈ parity (R := k) _ _ 0 ∧
      (contentCapMatrixFunctorNatIso D Sc cutoff i ν hh).inv.app M ∈ parity (R := k) _ _ 0 :=
  contentCapMatrixIso_even D Sc cutoff M i ν hh

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
