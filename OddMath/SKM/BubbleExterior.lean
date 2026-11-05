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

end OddMath.SKM.SYM
