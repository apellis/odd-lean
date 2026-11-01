import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight
import OddMath.QuiverHecke.CyclotomicAction.ELVFiniteMatrixComponents

/-! # Actual component matrices at the fixed count of a content block
This instantiates the prescribed finite matrices of DeformedMatrixComparison
section 4 uniformly on the actual old-content input category.
No equivalence of full old and content module categories is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.FixedContentMatrix
universe u
variable {k : Type u} [CommRing k]
private theorem iso_bijective {V W : SVec k} (e : V ≅ W) :
    Function.Bijective (fun x => e.hom x) := by
  have hl : Function.LeftInverse (fun y => e.inv y) (fun x => e.hom x) := by
    intro x
    have h := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
    simpa only [SVec.comp_apply, SVec.id_apply] using h
  have hr : Function.RightInverse (fun y => e.inv y) (fun x => e.hom x) := by
    intro y
    have h := congrArg (fun f : W ⟶ W => f y) e.inv_hom_id
    simpa only [SVec.comp_apply, SVec.id_apply] using h
  exact ⟨hl.injective, hr.surjective⟩
end OddMath.QuiverHecke.ELVOld.FixedContentMatrix

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)


/-- The actual odd unit matrix is invertible at one fixed count across the whole input content block. -/
def oldContentUnitMatrixIso (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (ν : List I) (hh : 0 ≤ contentCrossingHeight D cutoff j.1 (ν : Multiset I))
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    (unitMatrixSourceSpace D Sc cutoff j.1 (oldRepresentable D Sc cutoff v.obj) (contentUnitCount D cutoff j.1 (ν : Multiset I)) t) ≅
    (((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.induction (append D Sc cutoff j.1)).obj (oldRepresentable D Sc cutoff v.obj))).obj t) :=
  unitMatrixComponentIso D Sc cutoff p j v.obj.word t.word (contentUnitCount D cutoff j.1 (ν : Multiset I))
    (oldContent_unitCount_height D Sc cutoff j.1 ν hh v)

/-- The blockwise isomorphism retains the literal assembled matrix as forward map. -/
theorem oldContentUnitMatrixIso_hom (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (ν : List I) (hh : 0 ≤ contentCrossingHeight D cutoff j.1 (ν : Multiset I))
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    (oldContentUnitMatrixIso D Sc cutoff p j ν hh v t).hom =
      unitMatrixComponent D Sc cutoff j.1 (oldRepresentable D Sc cutoff v.obj) (contentUnitCount D cutoff j.1 (ν : Multiset I)) t :=
  unitMatrixComponentIso_hom D Sc cutoff p j v.obj.word t.word (contentUnitCount D cutoff j.1 (ν : Multiset I))
    (oldContent_unitCount_height D Sc cutoff j.1 ν hh v)

/-- The blockwise inverse retains the prescribed grading. -/
theorem oldContentUnitMatrixIso_inv_even (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (ν : List I) (hh : 0 ≤ contentCrossingHeight D cutoff j.1 (ν : Multiset I))
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    (oldContentUnitMatrixIso D Sc cutoff p j ν hh v t).inv ∈ parity (R := k) _ _ 0 :=
  unitMatrixComponentIso_inv_even D Sc cutoff p j v.obj.word t.word (contentUnitCount D cutoff j.1 (ν : Multiset I))
    (oldContent_unitCount_height D Sc cutoff j.1 ν hh v)

/-- The actual matrix component is bijective at that fixed content count. -/
theorem oldContentUnitMatrixIso_bijective (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (ν : List I) (hh : 0 ≤ contentCrossingHeight D cutoff j.1 (ν : Multiset I))
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    Function.Bijective (fun x => (unitMatrixComponent D Sc cutoff j.1
      (oldRepresentable D Sc cutoff v.obj) (contentUnitCount D cutoff j.1 (ν : Multiset I)) t) x) := by
  have h := FixedContentMatrix.iso_bijective (oldContentUnitMatrixIso D Sc cutoff p j ν hh v t)
  rw [oldContentUnitMatrixIso_hom] at h
  exact h

/-- The actual odd cap matrix is invertible at one fixed count across the whole input content block. -/
def oldContentCapMatrixIso (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (ν : List I) (hh : contentCrossingHeight D cutoff j.1 (ν : Multiset I) ≤ 0)
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    (((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj (oldRepresentable D Sc cutoff v.obj))).obj t) ≅
    (capMatrixTargetSpace D Sc cutoff j.1 (oldRepresentable D Sc cutoff v.obj) (contentCapCount D cutoff j.1 (ν : Multiset I)) t) :=
  capMatrixComponentIso D Sc cutoff p j v.obj.word t.word (contentCapCount D cutoff j.1 (ν : Multiset I))
    (oldContent_capCount_height D Sc cutoff j.1 ν hh v)

/-- The blockwise isomorphism retains the literal assembled matrix as forward map. -/
theorem oldContentCapMatrixIso_hom (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (ν : List I) (hh : contentCrossingHeight D cutoff j.1 (ν : Multiset I) ≤ 0)
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    (oldContentCapMatrixIso D Sc cutoff p j ν hh v t).hom =
      capMatrixComponent D Sc cutoff j.1 (oldRepresentable D Sc cutoff v.obj) (contentCapCount D cutoff j.1 (ν : Multiset I)) t :=
  capMatrixComponentIso_hom D Sc cutoff p j v.obj.word t.word (contentCapCount D cutoff j.1 (ν : Multiset I))
    (oldContent_capCount_height D Sc cutoff j.1 ν hh v)

/-- The blockwise inverse retains the prescribed grading. -/
theorem oldContentCapMatrixIso_inv_even (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (ν : List I) (hh : contentCrossingHeight D cutoff j.1 (ν : Multiset I) ≤ 0)
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    (oldContentCapMatrixIso D Sc cutoff p j ν hh v t).inv ∈ parity (R := k) _ _ 0 :=
  capMatrixComponentIso_inv_even D Sc cutoff p j v.obj.word t.word (contentCapCount D cutoff j.1 (ν : Multiset I))
    (oldContent_capCount_height D Sc cutoff j.1 ν hh v)

/-- The actual matrix component is bijective at that fixed content count. -/
theorem oldContentCapMatrixIso_bijective (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (ν : List I) (hh : contentCrossingHeight D cutoff j.1 (ν : Multiset I) ≤ 0)
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    Function.Bijective (fun x => (capMatrixComponent D Sc cutoff j.1
      (oldRepresentable D Sc cutoff v.obj) (contentCapCount D cutoff j.1 (ν : Multiset I)) t) x) := by
  have h := FixedContentMatrix.iso_bijective (oldContentCapMatrixIso D Sc cutoff p j ν hh v t)
  rw [oldContentCapMatrixIso_hom] at h
  exact h

/-- The actual even unit matrix is invertible at one fixed count across the whole input content block. -/
def oldContentEvenUnitMatrixIso (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (ν : List I) (hh : 0 ≤ contentCrossingHeight D cutoff i.1 (ν : Multiset I))
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    (unitMatrixSourceSpace D Sc cutoff i.1 (oldRepresentable D Sc cutoff v.obj) (contentUnitCount D cutoff i.1 (ν : Multiset I)) t) ≅
    (((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.induction (append D Sc cutoff i.1)).obj (oldRepresentable D Sc cutoff v.obj))).obj t) :=
  evenUnitMatrixComponentIso D Sc cutoff p i v.obj.word t.word (contentUnitCount D cutoff i.1 (ν : Multiset I))
    (oldContent_unitCount_height D Sc cutoff i.1 ν hh v)

/-- The blockwise isomorphism retains the literal assembled matrix as forward map. -/
theorem oldContentEvenUnitMatrixIso_hom (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (ν : List I) (hh : 0 ≤ contentCrossingHeight D cutoff i.1 (ν : Multiset I))
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    (oldContentEvenUnitMatrixIso D Sc cutoff p i ν hh v t).hom =
      unitMatrixComponent D Sc cutoff i.1 (oldRepresentable D Sc cutoff v.obj) (contentUnitCount D cutoff i.1 (ν : Multiset I)) t :=
  evenUnitMatrixComponentIso_hom D Sc cutoff p i v.obj.word t.word (contentUnitCount D cutoff i.1 (ν : Multiset I))
    (oldContent_unitCount_height D Sc cutoff i.1 ν hh v)

/-- The blockwise inverse retains the prescribed grading. -/
theorem oldContentEvenUnitMatrixIso_inv_even (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (ν : List I) (hh : 0 ≤ contentCrossingHeight D cutoff i.1 (ν : Multiset I))
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    (oldContentEvenUnitMatrixIso D Sc cutoff p i ν hh v t).inv ∈ parity (R := k) _ _ 0 :=
  evenUnitMatrixComponentIso_inv_even D Sc cutoff p i v.obj.word t.word (contentUnitCount D cutoff i.1 (ν : Multiset I))
    (oldContent_unitCount_height D Sc cutoff i.1 ν hh v)

/-- The actual matrix component is bijective at that fixed content count. -/
theorem oldContentEvenUnitMatrixIso_bijective (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (ν : List I) (hh : 0 ≤ contentCrossingHeight D cutoff i.1 (ν : Multiset I))
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    Function.Bijective (fun x => (unitMatrixComponent D Sc cutoff i.1
      (oldRepresentable D Sc cutoff v.obj) (contentUnitCount D cutoff i.1 (ν : Multiset I)) t) x) := by
  have h := FixedContentMatrix.iso_bijective (oldContentEvenUnitMatrixIso D Sc cutoff p i ν hh v t)
  rw [oldContentEvenUnitMatrixIso_hom] at h
  exact h

/-- The actual even cap matrix is invertible at one fixed count across the whole input content block. -/
def oldContentEvenCapMatrixIso (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (ν : List I) (hh : contentCrossingHeight D cutoff i.1 (ν : Multiset I) ≤ 0)
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    (((BalancedInduction.induction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj (oldRepresentable D Sc cutoff v.obj))).obj t) ≅
    (capMatrixTargetSpace D Sc cutoff i.1 (oldRepresentable D Sc cutoff v.obj) (contentCapCount D cutoff i.1 (ν : Multiset I)) t) :=
  evenCapMatrixComponentIso D Sc cutoff p i v.obj.word t.word (contentCapCount D cutoff i.1 (ν : Multiset I))
    (oldContent_capCount_height D Sc cutoff i.1 ν hh v)

/-- The blockwise isomorphism retains the literal assembled matrix as forward map. -/
theorem oldContentEvenCapMatrixIso_hom (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (ν : List I) (hh : contentCrossingHeight D cutoff i.1 (ν : Multiset I) ≤ 0)
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    (oldContentEvenCapMatrixIso D Sc cutoff p i ν hh v t).hom =
      capMatrixComponent D Sc cutoff i.1 (oldRepresentable D Sc cutoff v.obj) (contentCapCount D cutoff i.1 (ν : Multiset I)) t :=
  evenCapMatrixComponentIso_hom D Sc cutoff p i v.obj.word t.word (contentCapCount D cutoff i.1 (ν : Multiset I))
    (oldContent_capCount_height D Sc cutoff i.1 ν hh v)

/-- The blockwise inverse retains the prescribed grading. -/
theorem oldContentEvenCapMatrixIso_inv_even (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (ν : List I) (hh : contentCrossingHeight D cutoff i.1 (ν : Multiset I) ≤ 0)
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    (oldContentEvenCapMatrixIso D Sc cutoff p i ν hh v t).inv ∈ parity (R := k) _ _ 0 :=
  evenCapMatrixComponentIso_inv_even D Sc cutoff p i v.obj.word t.word (contentCapCount D cutoff i.1 (ν : Multiset I))
    (oldContent_capCount_height D Sc cutoff i.1 ν hh v)

/-- The actual matrix component is bijective at that fixed content count. -/
theorem oldContentEvenCapMatrixIso_bijective (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (ν : List I) (hh : contentCrossingHeight D cutoff i.1 (ν : Multiset I) ≤ 0)
    (v : OldContentCategory D Sc cutoff ν) (t : OldCategory D Sc cutoff) :
    Function.Bijective (fun x => (capMatrixComponent D Sc cutoff i.1
      (oldRepresentable D Sc cutoff v.obj) (contentCapCount D cutoff i.1 (ν : Multiset I)) t) x) := by
  have h := FixedContentMatrix.iso_bijective (oldContentEvenCapMatrixIso D Sc cutoff p i ν hh v t)
  rw [oldContentEvenCapMatrixIso_hom] at h
  exact h

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
