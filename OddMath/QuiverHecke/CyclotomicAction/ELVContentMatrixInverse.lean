import OddMath.Algebra.FiniteSupermodule
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleMatrixInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVQuotientInduction

/-! # Prescribed matrix isomorphisms on fixed output content

DeformedMatrixComparison section 4, the old-category naturality step.
The finite count is constant on output content. The independently specified
even unit/cap entries assemble naturally along every old arrow, and their
verified arbitrary-module component inverses give supermodule isomorphisms.
These are restrictions of the old-category matrices; compatibility with
the chosen content E/F comparisons and input-module naturality is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

/-- The prescribed finite unit family as an old supermodule. -/
def unitMatrixSourceModule (i : I) (m : ℕ) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  FiniteSupermodule.product (unitMatrixFamily D Sc cutoff i M m)

/-- The prescribed finite cap family as an old supermodule. -/
def capMatrixTargetModule (i : I) (m : ℕ) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  FiniteSupermodule.product (capMatrixFamily D Sc cutoff i M m)

/-- The literal assembled unit matrix is natural along all old arrows. -/
def unitMatrixNatTrans (i : I) (m : ℕ) :
    (unitMatrixSourceModule D Sc cutoff M i m).toFunctor ⟶
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).toFunctor :=
  FiniteSupermodule.columns (unitMatrixEntry D Sc cutoff i M m)
    (unitMatrixEntry_mem D Sc cutoff i M m)

/-- The literal assembled cap matrix is natural along all old arrows. -/
def capMatrixNatTrans (i : I) (m : ℕ) :
    ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).toFunctor ⟶
        (capMatrixTargetModule D Sc cutoff M i m).toFunctor :=
  FiniteSupermodule.rows (capMatrixEntry D Sc cutoff i M m)
    (capMatrixEntry_mem D Sc cutoff i M m)

private def unitIsoAtCount (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : ℕ) (hm : contentUnitCount D cutoff i (t.word : Multiset I) = m) :
    unitMatrixSourceSpace D Sc cutoff i M m t ≅ mateTargetSpace D Sc cutoff i M t := by
  subst m
  exact moduleUnitMatrixIso D Sc cutoff M i t hh

private theorem unitIsoAtCount_hom (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : ℕ) (hm : contentUnitCount D cutoff i (t.word : Multiset I) = m) :
    (unitIsoAtCount D Sc cutoff M i t hh m hm).hom = unitMatrixComponent D Sc cutoff i M m t := by
  subst m
  exact moduleUnitMatrixIso_hom D Sc cutoff M i t hh

private def capIsoAtCount (i : I) (t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : ℕ) (hm : contentCapCount D cutoff i (t.word : Multiset I) = m) :
    mateSourceSpace D Sc cutoff i M t ≅ capMatrixTargetSpace D Sc cutoff i M m t := by
  subst m
  exact moduleCapMatrixIso D Sc cutoff M i t hh

private theorem capIsoAtCount_hom (i : I) (t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : ℕ) (hm : contentCapCount D cutoff i (t.word : Multiset I) = m) :
    (capIsoAtCount D Sc cutoff M i t hh m hm).hom = capMatrixComponent D Sc cutoff i M m t := by
  subst m
  exact moduleCapMatrixIso_hom D Sc cutoff M i t hh

/-- The component inverse at the fixed output-content unit count. -/
def contentUnitMatrixComponentIso (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (t : OldContentCategory D Sc cutoff ν) :
    unitMatrixSourceSpace D Sc cutoff i M (contentUnitCount D cutoff i (ν : Multiset I)) t.obj ≅
      mateTargetSpace D Sc cutoff i M t.obj :=
  unitIsoAtCount D Sc cutoff M i t.obj
    (by simpa only [Multiset.coe_eq_coe.mpr t.wordPerm] using hh) _
    (congrArg (contentUnitCount D cutoff i) (Multiset.coe_eq_coe.mpr t.wordPerm))

theorem contentUnitMatrixComponentIso_hom (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (t : OldContentCategory D Sc cutoff ν) :
    (contentUnitMatrixComponentIso D Sc cutoff M i ν hh t).hom =
      unitMatrixComponent D Sc cutoff i M (contentUnitCount D cutoff i (ν : Multiset I)) t.obj :=
  unitIsoAtCount_hom D Sc cutoff M i t.obj _ _ _

/-- The component inverse at the fixed output-content cap count. -/
def contentCapMatrixComponentIso (i : I) (ν : List I)
    (hh : contentCrossingHeight D cutoff i (ν : Multiset I) ≤ 0)
    (t : OldContentCategory D Sc cutoff ν) :
    mateSourceSpace D Sc cutoff i M t.obj ≅
      capMatrixTargetSpace D Sc cutoff i M (contentCapCount D cutoff i (ν : Multiset I)) t.obj :=
  capIsoAtCount D Sc cutoff M i t.obj
    (by simpa only [Multiset.coe_eq_coe.mpr t.wordPerm] using hh) _
    (congrArg (contentCapCount D cutoff i) (Multiset.coe_eq_coe.mpr t.wordPerm))

theorem contentCapMatrixComponentIso_hom (i : I) (ν : List I)
    (hh : contentCrossingHeight D cutoff i (ν : Multiset I) ≤ 0)
    (t : OldContentCategory D Sc cutoff ν) :
    (contentCapMatrixComponentIso D Sc cutoff M i ν hh t).hom =
      capMatrixComponent D Sc cutoff i M (contentCapCount D cutoff i (ν : Multiset I)) t.obj :=
  capIsoAtCount_hom D Sc cutoff M i t.obj _ _ _

/-- Unit-column inversion natural in every arrow of the output content block. -/
def contentUnitMatrixNatIso (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I)) :
    (oldContentInclusion D Sc cutoff ν ⋙
      (unitMatrixSourceModule D Sc cutoff M i (contentUnitCount D cutoff i (ν : Multiset I))).toFunctor) ≅
    (oldContentInclusion D Sc cutoff ν ⋙
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).toFunctor) :=
  NatIso.ofComponents (contentUnitMatrixComponentIso D Sc cutoff M i ν hh) (by
    intro t t' f
    simp only [contentUnitMatrixComponentIso_hom]
    exact (unitMatrixNatTrans D Sc cutoff M i _).naturality f)

/-- Cap-row inversion natural in every arrow of the output content block. -/
def contentCapMatrixNatIso (i : I) (ν : List I)
    (hh : contentCrossingHeight D cutoff i (ν : Multiset I) ≤ 0) :
    (oldContentInclusion D Sc cutoff ν ⋙
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).toFunctor) ≅
    (oldContentInclusion D Sc cutoff ν ⋙
      (capMatrixTargetModule D Sc cutoff M i (contentCapCount D cutoff i (ν : Multiset I))).toFunctor) :=
  NatIso.ofComponents (contentCapMatrixComponentIso D Sc cutoff M i ν hh) (by
    intro t t' f
    simp only [contentCapMatrixComponentIso_hom]
    exact (capMatrixNatTrans D Sc cutoff M i _).naturality f)

/-- Even supermodule inversion on fixed output content, for every old input module. -/
def contentUnitMatrixIso (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I)) :
    (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj
      (unitMatrixSourceModule D Sc cutoff M i (contentUnitCount D cutoff i (ν : Multiset I))) ≅
    (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M)) :=
  moduleIsoOfEvenNatIso _ _ (contentUnitMatrixNatIso D Sc cutoff M i ν hh)
    (fun t => by
      change (contentUnitMatrixComponentIso D Sc cutoff M i ν hh t).hom ∈ _
      rw [contentUnitMatrixComponentIso_hom]
      exact unitMatrixComponent_even D Sc cutoff i M _ t.obj)
    (fun t => Supercategory.inv_mem (contentUnitMatrixComponentIso D Sc cutoff M i ν hh t) (by
      rw [contentUnitMatrixComponentIso_hom]
      exact unitMatrixComponent_even D Sc cutoff i M _ t.obj))

/-- Even supermodule cap inversion on fixed output content, for every old input module. -/
def contentCapMatrixIso (i : I) (ν : List I)
    (hh : contentCrossingHeight D cutoff i (ν : Multiset I) ≤ 0) :
    (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)) ≅
    (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj
      (capMatrixTargetModule D Sc cutoff M i (contentCapCount D cutoff i (ν : Multiset I))) :=
  moduleIsoOfEvenNatIso _ _ (contentCapMatrixNatIso D Sc cutoff M i ν hh)
    (fun t => by
      change (contentCapMatrixComponentIso D Sc cutoff M i ν hh t).hom ∈ _
      rw [contentCapMatrixComponentIso_hom]
      exact capMatrixComponent_even D Sc cutoff i M _ t.obj)
    (fun t => Supercategory.inv_mem (contentCapMatrixComponentIso D Sc cutoff M i ν hh t) (by
      rw [contentCapMatrixComponentIso_hom]
      exact capMatrixComponent_even D Sc cutoff i M _ t.obj))

/-- The content supermodule isomorphism has exactly the prescribed unit components. -/
theorem contentUnitMatrixIso_hom_total (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (t : OldContentCategory D Sc cutoff ν) :
    (contentUnitMatrixIso D Sc cutoff M i ν hh).hom.total t =
      unitMatrixComponent D Sc cutoff i M (contentUnitCount D cutoff i (ν : Multiset I)) t.obj := by
  change (contentUnitMatrixComponentIso D Sc cutoff M i ν hh t).hom + 0 = _
  rw [add_zero, contentUnitMatrixComponentIso_hom]

/-- Both directions preserve parity as module morphisms, not only pointwise. -/
theorem contentUnitMatrixIso_even (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I)) :
    (contentUnitMatrixIso D Sc cutoff M i ν hh).hom ∈ parity (R := k) _ _ 0 ∧
      (contentUnitMatrixIso D Sc cutoff M i ν hh).inv ∈ parity (R := k) _ _ 0 := by
  have h : (contentUnitMatrixIso D Sc cutoff M i ν hh).hom ∈ parity (R := k) _ _ 0 := by
    apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
    intro q hq
    funext t
    change (if q = 0 then _ else 0) = 0
    exact ite_eq_right hq
  exact ⟨h, Supercategory.inv_mem _ h⟩

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
