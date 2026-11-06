/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelEntryDegreesOver
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelClosureDegree

/-!
# Integer degrees of the represented matrix inverses over a graded base ring

Over a commutative `K`-algebra `R` graded by `𝒜`, the Hom modules of the old quotient carry the
`K`-linear degrees of `ELVOld.oldCategoryGradedSupercategoryOver`, and the represented kernels
carry `IndResKernel.integerDegreeOver`. The finite unit/cap matrices have degree zero after the
prescribed coordinate shifts (`positiveKernelMap_degreeOver`,
`negativeKernelMap_degreeOver`), so their proved bijectivity gives homogeneous inverses,
with principal inverse degree `+2 dᵢ`, and the unit-inverse-cap closures have degree
`2 dᵢ (r + s + 1)` (`positiveKernelClosure_degreeOver`, `negativeKernelClosure_degreeOver`). The comparison only uses the additive structure
(`IntegerMatrix.Coordinates.toInt`), since the matrices are `R`-linear and the degrees are
`K`-linear.

For `K = R` with the trivial grading these are the statements of
`OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixInteger`.
-/

noncomputable section

open CategoryTheory Opposite StringDiagrams Supercategory GradedSupercategory OddMath.Diagrams
open OddMath.IntegerMatrix

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ)

/-- Homogeneous scalars shift degrees of the old quotient, over a graded base. -/
theorem oldSmul_mem_degreeOver {v w : OldCategory D Sc cutoff} {a n : ℤ} {r : R} {f : v ⟶ w}
    (hr : r ∈ 𝒜 a) (hf : f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w n) :
    r • f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w (a + n) := by
  obtain ⟨b, hb, rfl⟩ := hf
  exact ⟨r • b, smul_mem_elvHomDegreeOver D sy 𝒜 Sc hP cutoff hr hb, map_smul _ r b⟩

/-- The coefficient Hom grading of the old quotient over a graded base, as additive
coordinates. -/
def oldHomIntegerCoordinatesOver (v t : OldCategory D Sc cutoff) :
    Coordinates (k := ℤ) (v ⟶ t) :=
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  Coordinates.toInt
    { degree := degree (R := K) v t
      projection := fun n => dproj K n
      projection_mem := fun n x => dproj_mem n x
      projection_of_mem := fun {m n} {x} hx => by
        by_cases h : m = n
        · subst m
          rw [ite_eq_left rfl]
          exact dproj_of_mem hx
        · rw [ite_eq_right h]
          exact dproj_of_mem_ne hx h
      spanning := (isInternal_degree v t).submodule_iSup_eq_top }

/-- The integer degree of the represented lower loop over a graded base, as additive
coordinates. -/
def representedKernelCoordinatesOver (i : I) (v t : OldCategory D Sc cutoff) :
    Coordinates (k := ℤ) (IndResKernel.Component (k := R) (append D Sc cutoff i) v t) :=
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  letI : ∀ X Y : OldCategory D Sc cutoff, IsScalarTower K R (X ⟶ Y) :=
    Linear.isScalarTower_restrictScalars K R _
  Coordinates.toInt
    { degree := IndResKernel.integerDegreeOver (K := K) (R := R) (append D Sc cutoff i) v t
      projection := IndResKernel.integerProjectionOver 𝒜 (append D Sc cutoff i)
        (fun hf => oldAppend_mem_degreeOver D sy 𝒜 Sc hP cutoff i hf)
        (fun hr hf => oldSmul_mem_degreeOver D sy 𝒜 Sc hP cutoff hr hf) v t
      projection_mem := IndResKernel.integerProjectionOver_mem 𝒜 _ _ _ v t
      projection_of_mem := fun hx => IndResKernel.integerProjectionOver_of_mem 𝒜 _ _ _ v t hx
      spanning := IndResKernel.iSup_integerDegreeOver_eq_top (K := K) (R := R) _ v t }

private def positiveEntryCoordinatesOver (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    ∀ a, Coordinates (k := ℤ) ((positiveKernelFamily D Sc cutoff i m t a).obj (op v))
  | none => representedKernelCoordinatesOver D sy 𝒜 Sc hP cutoff i v t
  | some _ => oldHomIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff v t

private def negativeEntryCoordinatesOver (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    ∀ a, Coordinates (k := ℤ) ((negativeKernelFamily D Sc cutoff i m t a).obj (op v))
  | none => oldHomIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff
      ((append D Sc cutoff i).obj v) ((append D Sc cutoff i).obj t)
  | some _ => oldHomIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff v t

/-- The positive finite source has its prescribed shifted decomposition, over a graded base. -/
def positiveKernelIntegerCoordinatesOver (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    Coordinates (k := ℤ) ((BalancedKernelTensor.piKernel
      (positiveKernelFamily D Sc cutoff i m t)).obj (op v)) :=
  Coordinates.shiftedFamily (positiveEntryCoordinatesOver D sy 𝒜 Sc hP cutoff i m v t)
    (positiveKernelShift D sy i m)

/-- The negative finite target has its prescribed shifted decomposition, over a graded base. -/
def negativeKernelIntegerCoordinatesOver (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    Coordinates (k := ℤ) ((BalancedKernelTensor.piKernel
      (negativeKernelFamily D Sc cutoff i m t)).obj (op v)) :=
  Coordinates.shiftedFamily (negativeEntryCoordinatesOver D sy 𝒜 Sc hP cutoff i m v t)
    (negativeKernelShift D sy i m)

/-- The positive matrix preserves the shifted integer degree, over a graded base. -/
theorem positiveKernelMap_degreeOver (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff)
    {n : ℤ}
    {z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj (op v)}
    (hz : z ∈ (positiveKernelIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff i m v t).degree n) :
    (positiveKernelMap D Sc cutoff i m t).app (op v) z ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
        ((append D Sc cutoff i).obj t) n := by
  have hz' := (Coordinates.mem_shiftedDegree
    (positiveEntryCoordinatesOver D sy 𝒜 Sc hP cutoff i m v t)
    (positiveKernelShift D sy i m) n z).1 hz
  rw [positiveKernelMap_apply]
  apply add_mem
  · have h0 : z none ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t
        (n + 2 * sy.d i) := hz' none
    have h := mateKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t h0
    rwa [add_sub_cancel_right] at h
  · apply sum_mem
    intro r _
    have h0 : z (some r) ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t
        (n + -(2 * sy.d i * r.val)) := hz' (some r)
    have h := unitKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t r.val h0
    rwa [neg_add_cancel_right] at h

/-- The negative matrix preserves the shifted integer degree, over a graded base. -/
theorem negativeKernelMap_degreeOver (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {z : IndResKernel.Component (k := R) (append D Sc cutoff i) v t}
    (hz : z ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n) :
    (negativeKernelMap D Sc cutoff i m t).app (op v) z ∈
      (negativeKernelIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff i m v t).degree n := by
  apply (Coordinates.mem_shiftedDegree
    (negativeEntryCoordinatesOver D sy 𝒜 Sc hP cutoff i m v t)
    (negativeKernelShift D sy i m) n _).2
  intro a
  cases a with
  | none =>
    rw [negativeKernelMap_none]
    have h := mateKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t hz
    rw [sub_eq_add_neg] at h
    exact h
  | some r =>
    rw [negativeKernelMap_some]
    exact capKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t r.val hz

/-- The positive inverse preserves the shifted coordinate degrees, over a graded base. -/
theorem positiveKernelEquiv_inverse_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) {n : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
      ((append D Sc cutoff i).obj t) n) :
    (positiveKernelEquiv D Sc cutoff i v t hh).symm y ∈
      (positiveKernelIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff i
        (contentUnitCount D cutoff i (t.word : Multiset I)) v t).degree n :=
  Coordinates.inverse_mem _ (oldHomIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff _ _)
    (positiveKernelEquiv D Sc cutoff i v t hh).toAddEquiv.toIntLinearEquiv
    (fun _ _ hx => positiveKernelMap_degreeOver D sy 𝒜 Sc hP cutoff i _ v t hx) hy

/-- The negative inverse preserves the shifted coordinate degrees, over a graded base. -/
theorem negativeKernelEquiv_inverse_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) {n : ℤ} {y}
    (hy : y ∈ (negativeKernelIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) v t).degree n) :
    (negativeKernelEquiv D Sc cutoff i v t hh).symm y ∈
      representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n :=
  Coordinates.inverse_mem (representedKernelCoordinatesOver D sy 𝒜 Sc hP cutoff i v t) _
    (negativeKernelEquiv D Sc cutoff i v t hh).toAddEquiv.toIntLinearEquiv
    (fun _ _ hx => negativeKernelMap_degreeOver D sy 𝒜 Sc hP cutoff i _ v t hx) hy

/-- The principal positive inverse raises degree by `2 dᵢ`, over a graded base. -/
theorem positiveKernelPrincipalInverse_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) {n : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
      ((append D Sc cutoff i).obj t) n) :
    positiveKernelPrincipalInverse D Sc cutoff i v t hh y ∈
      representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t (n + 2 * sy.d i) :=
  (Coordinates.mem_shiftedDegree _ _ _ _).1
    (positiveKernelEquiv_inverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh hy) none

/-- The principal negative inverse also raises degree by `2 dᵢ`, over a graded base. -/
theorem negativeKernelPrincipalInverse_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) {n : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
      ((append D Sc cutoff i).obj t) n) :
    negativeKernelPrincipalInverse D Sc cutoff i v t hh y ∈
      representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t (n + 2 * sy.d i) := by
  apply negativeKernelEquiv_inverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh
  apply (Coordinates.mem_shiftedDegree _ _ _ _).2
  intro a
  cases a with
  | none =>
    change y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
      ((append D Sc cutoff i).obj t) (n + 2 * sy.d i + -(2 * sy.d i))
    simpa only [add_neg_cancel_right] using hy
  | some r =>
    change (Pi.single none y : ∀ a, (negativeKernelFamily D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t a).obj (op v)) (some r) ∈ _
    rw [Pi.single_eq_of_ne (by simp)]
    exact zero_mem _

/-- The positive represented closure has degree `2 dᵢ (r + s + 1)`, over a graded base. -/
theorem positiveKernelClosure_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) (r s : ℕ)
    {n : ℤ} {b : v ⟶ t} (hb : b ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t n) :
    positiveKernelClosure D Sc cutoff i v t hh r s b ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff v t (n + 2 * sy.d i * (r + s + 1 : ℕ)) := by
  have h := capKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t s
    (positiveKernelPrincipalInverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh
      (unitKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t r hb))
  have he : n + 2 * sy.d i * r + 2 * sy.d i + 2 * sy.d i * s =
      n + 2 * sy.d i * (r + s + 1 : ℕ) := by push_cast; ring
  simpa only [positiveKernelClosure, LinearMap.comp_apply, he] using h

/-- The negative represented closure has the same degree, over a graded base. -/
theorem negativeKernelClosure_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) (r s : ℕ)
    {n : ℤ} {b : v ⟶ t} (hb : b ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t n) :
    negativeKernelClosure D Sc cutoff i v t hh r s b ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff v t (n + 2 * sy.d i * (r + s + 1 : ℕ)) := by
  have h := capKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t s
    (negativeKernelPrincipalInverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh
      (unitKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t r hb))
  have he : n + 2 * sy.d i * r + 2 * sy.d i + 2 * sy.d i * s =
      n + 2 * sy.d i * (r + s + 1 : ℕ) := by push_cast; ring
  simpa only [negativeKernelClosure, LinearMap.comp_apply, he] using h

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
