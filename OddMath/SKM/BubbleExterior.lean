/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleAlgebra
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The independent exterior part of the abstract bubble algebra

Supporting the full-SYM coefficient problem in research issue #345 and
Brundan–Ellis (1.21)–(1.22). This concerns the abstract presentation only;
it asserts no independence of bubble evaluation in an SKM Hom space.
-/

noncomputable section
open scoped Classical
namespace OddMath.SKM.SYM
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k]

/-- The free module on distinct odd colours. -/
abbrev OddModule := {i : I // D.parity i = 1} →₀ k

def oddLinear : OddModule D k →ₗ[k] SYM D k :=
  Finsupp.linearCombination k (delta D k)

@[simp] theorem oddLinear_single (i : {i : I // D.parity i = 1}) (a : k) :
    oddLinear D k (Finsupp.single i a) = a • delta D k i := by
  simp [oddLinear]

theorem oddLinear_add_mul_swap (x y : OddModule D k) :
    oddLinear D k x * oddLinear D k y + oddLinear D k y * oddLinear D k x = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz =>
    simp only [map_add, add_mul, mul_add]
    convert congrArg₂ (· + ·) hx hz using 1 <;> abel
  | single i a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y z hy hz =>
      simp only [map_add, add_mul, mul_add]
      convert congrArg₂ (· + ·) hy hz using 1 <;> abel
    | single j b =>
      simp only [oddLinear_single, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [mul_comm b a, ← smul_add, delta_anticommute D k i j]
      simp

theorem oddLinear_sq_zero (x : OddModule D k) : oddLinear D k x * oddLinear D k x = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, add_mul, mul_add, mul_add, hx, hy]
    simpa using oddLinear_add_mul_swap D k x y
  | single i a =>
    simp only [oddLinear_single, smul_mul_assoc, mul_smul_comm, smul_smul]
    have hs : delta D k i * delta D k i = 0 := by simpa only [pow_two] using delta_sq D k i
    rw [hs, smul_zero]

/-- All exterior words map into `SYM`, with one generator for every odd colour. -/
def exteriorInclude : ExteriorAlgebra k (OddModule D k) →ₐ[k] SYM D k :=
  ExteriorAlgebra.lift k ⟨oddLinear D k, oddLinear_sq_zero D k⟩

@[simp] theorem exteriorInclude_ι (x : OddModule D k) :
    exteriorInclude D k (ExteriorAlgebra.ι k x) = oddLinear D k x :=
  ExteriorAlgebra.lift_ι_apply _ _ _ _

private def exteriorProjectionGen (g : SYMGen D) : ExteriorAlgebra k (OddModule D k) :=
  match g with
  | .inl _ => 0
  | .inr i => ExteriorAlgebra.ι k (Finsupp.single i 1)

private theorem exteriorProjection_rel {x y : FreeAlgebra k (SYMGen D)}
    (h : SYMRel D k x y) :
    FreeAlgebra.lift k (exteriorProjectionGen D k) x =
      FreeAlgebra.lift k (exteriorProjectionGen D k) y := by
  cases h with
  | polynomial a b => simp [exteriorProjectionGen]
  | mixed a i => simp [exteriorProjectionGen]
  | exterior i j =>
    simp only [map_mul, map_neg, FreeAlgebra.lift_ι_apply, exteriorProjectionGen]
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := k) _ _)
  | square i =>
    rw [map_pow, map_zero, FreeAlgebra.lift_ι_apply]
    change (ExteriorAlgebra.ι k (Finsupp.single i 1 : OddModule D k)) ^ 2 = 0
    simpa only [pow_two] using ExteriorAlgebra.ι_sq_zero (R := k) (Finsupp.single i 1 : OddModule D k)

/-- Kill the elementary polynomial generators and retain the entire exterior algebra. -/
def exteriorProjection : SYM D k →ₐ[k] ExteriorAlgebra k (OddModule D k) :=
  RingQuot.liftAlgHom k
    ⟨FreeAlgebra.lift k (exteriorProjectionGen D k), fun _ _ h => exteriorProjection_rel D k h⟩

@[simp] theorem exteriorProjection_delta (i : {i : I // D.parity i = 1}) :
    exteriorProjection D k (delta D k i) = ExteriorAlgebra.ι k (Finsupp.single i 1) := by
  simp only [exteriorProjection, delta, ι, mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply, exteriorProjectionGen]

@[simp] theorem exteriorProjection_oddLinear (x : OddModule D k) :
    exteriorProjection D k (oddLinear D k x) = ExteriorAlgebra.ι k x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i a =>
    rw [oddLinear_single, map_smul, exteriorProjection_delta]
    rw [show Finsupp.single i a = a • Finsupp.single i 1 by simp]
    rw [map_smul]

/-- The projection is a left inverse, so no exterior relation is introduced
by adjoining the elementary coefficient generators. -/
theorem exteriorProjection_comp_include :
    (exteriorProjection D k).comp (exteriorInclude D k) = AlgHom.id k _ := by
  apply ExteriorAlgebra.hom_ext
  ext x
  simp

/-- The whole free exterior algebra embeds in the abstract coefficient algebra. -/
theorem exteriorInclude_injective : Function.Injective (exteriorInclude D k) := by
  apply Function.LeftInverse.injective (g := exteriorProjection D k)
  intro x
  exact DFunLike.congr_fun (exteriorProjection_comp_include D k) x

end OddMath.SKM.SYM
