import OddMath.Algebra.IntegerMatrixGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelEntryDegrees
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixBijective

/-! # Integer degrees of the actual represented matrix inverses

The homogeneous inverse step (G8) uses the original old-category Hom
degrees and the intrinsic balanced Hom-tensor degrees. The actual finite
unit/cap matrices have degree zero after the prescribed coordinate shifts.
Their existing bijectivity therefore gives homogeneous raw inverses,
including principal inverse degree `+2 dᵢ`. No degree of arbitrary module
Homs or grading transported through a matrix is assumed.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory GradedSupercategory
open OddMath.IntegerMatrix
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The original coefficient Hom grading, before any finite matrix is used. -/
def oldHomIntegerCoordinates (v t : OldCategory D Sc cutoff) :
    Coordinates (k := k) (v ⟶ t) := by
  letI := oldCategoryGradedSupercategory D Sc cutoff sy hc
  exact {
    degree := degree (R := k) v t
    projection := fun n => dproj k n
    projection_mem := fun n x => dproj_mem n x
    projection_of_mem := fun {m n} {x} hx => by
      by_cases h : m = n
      · subst m
        rw [ite_eq_left rfl]
        exact dproj_of_mem hx
      · rw [ite_eq_right h]
        exact dproj_of_mem_ne hx h
    spanning := (isInternal_degree v t).submodule_iSup_eq_top }

/-- The intrinsic quotient grading of the represented lower loop. -/
def representedKernelCoordinates (i : I) (v t : OldCategory D Sc cutoff) :
    Coordinates (k := k) (IndResKernel.Component (k := k) (append D Sc cutoff i) v t) := by
  letI := oldCategoryGradedSupercategory D Sc cutoff sy hc
  letI : IsGradedSuperfunctor k (append D Sc cutoff i) :=
    (oldAppendGraded D Sc cutoff sy hc i).isGraded
  exact {
    degree := IndResKernel.integerDegree (k := k) (append D Sc cutoff i) v t
    projection := IndResKernel.integerProjection (k := k) (append D Sc cutoff i) v t
    projection_mem := IndResKernel.integerProjection_mem (k := k) (append D Sc cutoff i) v t
    projection_of_mem := IndResKernel.integerProjection_of_mem (k := k) (append D Sc cutoff i) v t
    spanning := IndResKernel.iSup_integerDegree_eq_top (k := k) (append D Sc cutoff i) v t }

/-- The positive source shifts are `+2dᵢ` on the kernel and `-2dᵢr` on row `r`. -/
def positiveKernelShift (i : I) (m : ℕ) : Option (Fin m) → ℤ
  | none => 2 * sy.d i
  | some r => -(2 * sy.d i * r.val)

/-- The negative target shifts are `-2dᵢ` on the upper Hom and `+2dᵢr` on row `r`. -/
def negativeKernelShift (i : I) (m : ℕ) : Option (Fin m) → ℤ
  | none => -(2 * sy.d i)
  | some r => 2 * sy.d i * r.val

private def positiveEntryCoordinates (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    ∀ a, Coordinates (k := k) ((positiveKernelFamily D Sc cutoff i m t a).obj (op v))
  | none => representedKernelCoordinates D Sc cutoff sy hc i v t
  | some _ => oldHomIntegerCoordinates D Sc cutoff sy hc v t

private def negativeEntryCoordinates (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    ∀ a, Coordinates (k := k) ((negativeKernelFamily D Sc cutoff i m t a).obj (op v))
  | none => oldHomIntegerCoordinates D Sc cutoff sy hc
      ((append D Sc cutoff i).obj v) ((append D Sc cutoff i).obj t)
  | some _ => oldHomIntegerCoordinates D Sc cutoff sy hc v t

/-- The positive finite source has its prescribed intrinsic shifted decomposition. -/
def positiveKernelIntegerCoordinates (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    Coordinates (k := k) ((BalancedKernelTensor.piKernel
      (positiveKernelFamily D Sc cutoff i m t)).obj (op v)) :=
  Coordinates.shiftedFamily (positiveEntryCoordinates D Sc cutoff sy hc i m v t)
    (positiveKernelShift D sy i m)

/-- The negative finite target has its prescribed intrinsic shifted decomposition. -/
def negativeKernelIntegerCoordinates (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    Coordinates (k := k) ((BalancedKernelTensor.piKernel
      (negativeKernelFamily D Sc cutoff i m t)).obj (op v)) :=
  Coordinates.shiftedFamily (negativeEntryCoordinates D Sc cutoff sy hc i m v t)
    (negativeKernelShift D sy i m)

/-- The literal positive matrix preserves the shifted integer degree. -/
theorem actualPositiveKernelMap_degree (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj (op v)}
    (hz : z ∈ (positiveKernelIntegerCoordinates D Sc cutoff sy hc i m v t).degree n) :
    (actualPositiveKernelMap D Sc cutoff i m t).app (op v) z ∈
      oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) n := by
  have hz' := (Coordinates.mem_shiftedDegree
    (positiveEntryCoordinates D Sc cutoff sy hc i m v t) (positiveKernelShift D sy i m) n z).1 hz
  rw [actualPositiveKernelMap_apply]
  apply Submodule.add_mem
  · have h := actualMateKernelComponent_degree D Sc cutoff sy hc i v t (hz' none)
    simpa only [positiveEntryCoordinates, representedKernelCoordinates, positiveKernelShift,
      add_sub_cancel_right] using h
  · apply Submodule.sum_mem
    intro r _
    have h := actualUnitKernelComponent_degree D Sc cutoff sy hc i v t r.val (hz' (some r))
    simpa only [positiveEntryCoordinates, oldHomIntegerCoordinates, positiveKernelShift,
      neg_add_cancel_right] using h

/-- The literal negative matrix preserves the shifted integer degree. -/
theorem actualNegativeKernelMap_degree (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t}
    (hz : z ∈ representedKernelDegree D Sc cutoff sy hc i v t n) :
    (actualNegativeKernelMap D Sc cutoff i m t).app (op v) z ∈
      (negativeKernelIntegerCoordinates D Sc cutoff sy hc i m v t).degree n := by
  apply (Coordinates.mem_shiftedDegree
    (negativeEntryCoordinates D Sc cutoff sy hc i m v t) (negativeKernelShift D sy i m) n _).2
  intro a
  cases a with
  | none =>
    rw [actualNegativeKernelMap_none]
    exact actualMateKernelComponent_degree D Sc cutoff sy hc i v t hz
  | some r =>
    rw [actualNegativeKernelMap_some]
    exact actualCapKernelComponent_degree D Sc cutoff sy hc i v t r.val hz

omit sy hc in
/-- The raw positive kernel equivalence is the existing actual matrix, with its
proved bijectivity at the actual content height. -/
def positiveKernelEquiv (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :=
  LinearEquiv.ofBijective
    ((actualPositiveKernelMap D Sc cutoff i
      (contentUnitCount D cutoff i (t.word : Multiset I)) t).app (op v)).hom
    (actualPositiveKernelMap_bijective D Sc cutoff i t hh v)

omit sy hc in
/-- The raw negative kernel equivalence is the existing actual cap-row matrix. -/
def negativeKernelEquiv (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) :=
  LinearEquiv.ofBijective
    ((actualNegativeKernelMap D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t).app (op v)).hom
    (actualNegativeKernelMap_bijective D Sc cutoff i t hh v)

/-- The positive inverse preserves the intrinsic shifted coordinate degrees. -/
theorem positiveKernelEquiv_inverse_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) {n : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) n) :
    (positiveKernelEquiv D Sc cutoff i v t hh).symm y ∈
      (positiveKernelIntegerCoordinates D Sc cutoff sy hc i
        (contentUnitCount D cutoff i (t.word : Multiset I)) v t).degree n := by
  exact Coordinates.inverse_mem _ (oldHomIntegerCoordinates D Sc cutoff sy hc _ _)
    (positiveKernelEquiv D Sc cutoff i v t hh)
    (fun n x hx => actualPositiveKernelMap_degree D Sc cutoff sy hc i _ v t hx) hy

/-- The negative inverse preserves the intrinsic shifted coordinate degrees. -/
theorem negativeKernelEquiv_inverse_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) {n : ℤ} {y}
    (hy : y ∈ (negativeKernelIntegerCoordinates D Sc cutoff sy hc i
      (contentCapCount D cutoff i (t.word : Multiset I)) v t).degree n) :
    (negativeKernelEquiv D Sc cutoff i v t hh).symm y ∈
      representedKernelDegree D Sc cutoff sy hc i v t n := by
  exact Coordinates.inverse_mem (representedKernelCoordinates D Sc cutoff sy hc i v t) _
    (negativeKernelEquiv D Sc cutoff i v t hh)
    (fun n x hx => actualNegativeKernelMap_degree D Sc cutoff sy hc i _ v t hx) hy

omit sy hc in
/-- Principal positive inverse component, without a changed normalization. -/
def positiveKernelPrincipalInverse (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :
    ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) →ₗ[k]
      IndResKernel.Component (k := k) (append D Sc cutoff i) v t :=
  LinearMap.proj none ∘ₗ (positiveKernelEquiv D Sc cutoff i v t hh).symm.toLinearMap

/-- The represented principal positive inverse raises raw degree by `2 dᵢ`. -/
theorem positiveKernelPrincipalInverse_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) {n : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) n) :
    positiveKernelPrincipalInverse D Sc cutoff i v t hh y ∈
      representedKernelDegree D Sc cutoff sy hc i v t (n + 2 * sy.d i) :=
  (Coordinates.mem_shiftedDegree _ _ _ _).1
    (positiveKernelEquiv_inverse_degree D Sc cutoff sy hc i v t hh hy) none

omit sy hc in
/-- Principal negative inverse component: first insert the actual upper-Hom column. -/
def negativeKernelPrincipalInverse (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) :
    ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) →ₗ[k]
      IndResKernel.Component (k := k) (append D Sc cutoff i) v t :=
  (negativeKernelEquiv D Sc cutoff i v t hh).symm.toLinearMap ∘ₗ
    LinearMap.single k (fun a => (negativeKernelFamily D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t a).obj (op v)) none

/-- The represented principal negative inverse also raises raw degree by `2 dᵢ`. -/
theorem negativeKernelPrincipalInverse_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) {n : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) n) :
    negativeKernelPrincipalInverse D Sc cutoff i v t hh y ∈
      representedKernelDegree D Sc cutoff sy hc i v t (n + 2 * sy.d i) := by
  apply negativeKernelEquiv_inverse_degree D Sc cutoff sy hc i v t hh
  apply (Coordinates.mem_shiftedDegree _ _ _ _).2
  intro a
  cases a with
  | none =>
    change y ∈ oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i])
      (n + 2 * sy.d i + -(2 * sy.d i))
    simpa only [add_neg_cancel_right] using hy
  | some r =>
    change (Pi.single none y : ∀ a, (negativeKernelFamily D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t a).obj (op v)) (some r) ∈ _
    rw [Pi.single_eq_of_ne (by simp)]
    exact Submodule.zero_mem _

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
