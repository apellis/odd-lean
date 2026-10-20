/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.VermaMixed

/-!
# The actual modified highest-weight representation

The weight idempotents act by quotient weight projection, the negative generators
by left multiplication, and the positive generators by the constructed lowering
operators. All defining relations are verified. No faithfulness is asserted.
-/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I]
variable (D : RootDatum I X) (Λ : X)

/-- The two actual half-algebra actions on the negative Serre quotient. -/
def halfEnd (positive : Bool) : D.serreF Coefficients.q pi →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (D.serreF Coefficients.q pi) :=
  if positive then positiveAction D.toSuperCartanDatum (fun i ↦ D.h i Λ)
  else Algebra.lsmul Coefficients.Ring Coefficients.Ring (D.serreF Coefficients.q pi)

/-- A Chevalley operator without its right weight projection. -/
def chevalley (positive : Bool) (i : I) :
    Module.End Coefficients.Ring (D.serreF Coefficients.q pi) :=
  halfEnd D Λ positive (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))

@[simp] theorem chevalley_true (i : I) :
    chevalley D Λ true i = lower D.toSuperCartanDatum i (D.h i Λ) := by
  simp [chevalley, halfEnd]

@[simp] theorem chevalley_false_apply (i : I) (x : D.serreF Coefficients.q pi) :
    chevalley D Λ false i x = D.toSerreF Coefficients.q pi (θ Coefficients.Ring i) * x := rfl

/-- Both concrete Chevalley operators have the required weight shift. -/
theorem project_chevalley (positive : Bool) (i : I) (μ : X) :
    weightProject D Λ μ * chevalley D Λ positive i =
      chevalley D Λ positive i * weightProject D Λ (μ - halfRoot D positive i) := by
  ext x
  cases positive
  · simpa only [Module.End.mul_apply, chevalley_false_apply, halfRoot, Bool.false_eq_true,
      ite_false, sub_neg_eq_add] using weightProject_θ_mul D Λ μ i x
  · simpa only [Module.End.mul_apply, chevalley_true, halfRoot, ite_true] using
      weightProject_lower D Λ μ i (D.h i Λ) x

private theorem project_chevalley_pow (positive : Bool) (i : I) (n : ℕ) (μ : X) :
    weightProject D Λ μ * chevalley D Λ positive i ^ n =
      chevalley D Λ positive i ^ n *
        weightProject D Λ (μ - n • halfRoot D positive i) := by
  induction n generalizing μ with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mul_assoc, project_chevalley, mul_assoc, ih, ← mul_assoc, ← pow_succ']
    congr 2
    rw [succ_nsmul]
    abel

private theorem project_power_absorb (positive : Bool) (i : I) (n : ℕ) (μ : X) :
    weightProject D Λ (μ + n • halfRoot D positive i) *
      chevalley D Λ positive i ^ n * weightProject D Λ μ =
        chevalley D Λ positive i ^ n * weightProject D Λ μ := by
  classical
  rw [project_chevalley_pow, add_sub_cancel_right, mul_assoc, weightProject_mul]
  simp

/-- The actual action assigned to each generator of the unital envelope. -/
def genAction : Gen I X → Module.End Coefficients.Ring (D.serreF Coefficients.q pi)
  | .one μ => weightProject D Λ μ
  | .e i μ => chevalley D Λ true i * weightProject D Λ μ
  | .f i μ => chevalley D Λ false i * weightProject D Λ μ

/-- Evaluation of the free presentation in concrete endomorphisms. -/
def freeAction : Free Coefficients.Ring I X →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (D.serreF Coefficients.q pi) :=
  FreeAlgebra.lift Coefficients.Ring (genAction D Λ)

@[simp] theorem freeAction_one (μ : X) :
    freeAction D Λ (Free.one Coefficients.Ring μ) = weightProject D Λ μ := by
  simp [freeAction, Free.one, genAction]

@[simp] theorem freeAction_E (i : I) (μ : X) :
    freeAction D Λ (Free.E Coefficients.Ring i μ) =
      chevalley D Λ true i * weightProject D Λ μ := by
  simp [freeAction, Free.E, genAction]

@[simp] theorem freeAction_F (i : I) (μ : X) :
    freeAction D Λ (Free.F Coefficients.Ring i μ) =
      chevalley D Λ false i * weightProject D Λ μ := by
  simp [freeAction, Free.F, genAction]

private theorem freeAction_epow (i : I) (n : ℕ) (μ : X) :
    freeAction D Λ (epow D i n μ) =
      chevalley D Λ true i ^ n * weightProject D Λ μ := by
  induction n with
  | zero => simp [epow]
  | succ n ih =>
    have hp := project_power_absorb D Λ true i n μ
    simp only [halfRoot, ite_true] at hp
    rw [epow, map_mul, freeAction_E, ih, mul_assoc, ← mul_assoc
      (weightProject D Λ _), hp, ← mul_assoc, ← pow_succ']

private theorem freeAction_fpow (i : I) (n : ℕ) (μ : X) :
    freeAction D Λ (fpow D i n μ) =
      chevalley D Λ false i ^ n * weightProject D Λ μ := by
  induction n with
  | zero => simp [fpow]
  | succ n ih =>
    rw [fpow, map_mul, freeAction_F, ih]
    have he : μ - n • D.α i = μ + n • halfRoot D false i := by simp [halfRoot, sub_eq_add_neg]
    rw [he, mul_assoc, ← mul_assoc (weightProject D Λ _),
      project_power_absorb, ← mul_assoc, ← pow_succ']

private theorem projected_serre_term (positive : Bool) (i j : I) (a r : ℕ) (μ : X) :
    (chevalley D Λ positive i ^ a *
      weightProject D Λ (μ + r • halfRoot D positive i + halfRoot D positive j)) *
      (chevalley D Λ positive j * weightProject D Λ (μ + r • halfRoot D positive i)) *
      (chevalley D Λ positive i ^ r * weightProject D Λ μ) =
    (chevalley D Λ positive i ^ a * chevalley D Λ positive j *
      chevalley D Λ positive i ^ r) * weightProject D Λ μ := by
  classical
  have h1 : weightProject D Λ (μ + r • halfRoot D positive i + halfRoot D positive j) *
      chevalley D Λ positive j * weightProject D Λ (μ + r • halfRoot D positive i) =
      chevalley D Λ positive j * weightProject D Λ (μ + r • halfRoot D positive i) := by
    rw [project_chevalley, add_sub_cancel_right, mul_assoc, weightProject_mul]
    simp
  calc
    _ = chevalley D Λ positive i ^ a *
        (weightProject D Λ (μ + r • halfRoot D positive i + halfRoot D positive j) *
          chevalley D Λ positive j * weightProject D Λ (μ + r • halfRoot D positive i)) *
        (chevalley D Λ positive i ^ r * weightProject D Λ μ) := by simp only [mul_assoc]
    _ = chevalley D Λ positive i ^ a * chevalley D Λ positive j *
        (weightProject D Λ (μ + r • halfRoot D positive i) *
          chevalley D Λ positive i ^ r * weightProject D Λ μ) := by
      rw [h1]; simp only [mul_assoc]
    _ = _ := by rw [project_power_absorb]; simp only [mul_assoc]

private theorem chevalley_serre (positive : Bool) {i j : I} (hij : i ≠ j) :
    ∑ r ∈ Finset.range (D.serreDeg i j + 1),
      D.serreCoeff Coefficients.q pi i j r •
        (chevalley D Λ positive i ^ (D.serreDeg i j - r) *
          chevalley D Λ positive j * chevalley D Λ positive i ^ r) = 0 := by
  have h := congrArg (halfEnd D Λ positive) (D.toSerreF_serreElt Coefficients.q pi hij)
  simpa only [SuperCartanDatum.serreElt, map_sum, map_smul, map_mul, map_pow, map_zero,
    chevalley] using h

private theorem freeAction_serreE {i j : I} (hij : i ≠ j) (μ : X) :
    freeAction D Λ (serreE D Coefficients.q pi i j μ) = 0 := by
  simp only [serreE, map_sum, map_smul, map_mul, freeAction_epow, freeAction_E]
  have ht := projected_serre_term D Λ true i j
  simp only [halfRoot, ite_true] at ht
  simp only [ht, ← smul_mul_assoc, ← Finset.sum_mul]
  simpa only [← smul_mul_assoc, zero_mul] using
    congrArg (· * weightProject D Λ μ) (chevalley_serre D Λ true hij)

private theorem freeAction_serreF {i j : I} (hij : i ≠ j) (μ : X) :
    freeAction D Λ (serreF D Coefficients.q pi i j μ) = 0 := by
  simp only [serreF, map_sum, map_smul, map_mul, freeAction_fpow, freeAction_F]
  have ht := projected_serre_term D Λ false i j
  simp only [halfRoot, Bool.false_eq_true, ite_false, smul_neg, ← sub_eq_add_neg] at ht
  simp only [ht, ← smul_mul_assoc, ← Finset.sum_mul]
  simpa only [← smul_mul_assoc, zero_mul] using
    congrArg (· * weightProject D Λ μ) (chevalley_serre D Λ false hij)

private theorem project_step_absorb (positive : Bool) (i : I) (μ : X) :
    weightProject D Λ (μ + halfRoot D positive i) *
      (chevalley D Λ positive i * weightProject D Λ μ) =
        chevalley D Λ positive i * weightProject D Λ μ := by
  classical
  rw [← mul_assoc, project_chevalley, add_sub_cancel_right, mul_assoc, weightProject_mul]
  simp

variable [DecidableEq X]

/-- Every relation of the existing modified presentation holds for the concrete operators. -/
theorem freeAction_rel {x y : Free Coefficients.Ring I X}
    (h : Rel D Coefficients.q pi x y) : freeAction D Λ x = freeAction D Λ y := by
  cases h with
  | one_one μ ν =>
    simp only [map_mul, freeAction_one, weightProject_mul]
    split_ifs <;> simp
  | one_E i μ =>
    simpa only [map_mul, freeAction_one, freeAction_E, halfRoot, ite_true] using
      project_step_absorb D Λ true i μ
  | one_F i μ =>
    simpa only [map_mul, freeAction_one, freeAction_F, halfRoot, Bool.false_eq_true,
      ite_false, sub_eq_add_neg] using project_step_absorb D Λ false i μ
  | E_one i μ => simp only [map_mul, freeAction_E, freeAction_one, mul_assoc,
      weightProject_mul, ite_true]
  | F_one i μ => simp only [map_mul, freeAction_F, freeAction_one, mul_assoc,
      weightProject_mul, ite_true]
  | serreE i j μ hij => rw [freeAction_serreE D Λ hij, map_zero]
  | serreF i j μ hij => rw [freeAction_serreF D Λ hij, map_zero]
  | comm i j μ =>
    have he := project_step_absorb D Λ true i μ
    have hf := project_step_absorb D Λ false j μ
    simp only [halfRoot, ite_true] at he
    simp only [halfRoot, Bool.false_eq_true, ite_false, ← sub_eq_add_neg] at hf
    simp only [map_sub, map_mul, map_smul, freeAction_E, freeAction_F, mul_assoc, he, hf]
    ext z
    have hm := lower_mixed_project D i j Λ μ z
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      chevalley_true, chevalley_false_apply]
    rw [hm, add_sub_cancel_left]
    split_ifs <;> simp

/-- The actual highest-weight action of the unital envelope. It restricts to the
modified algebra; this is a representation, not an injectivity statement. -/
def representation : CoveringUDot Coefficients.Ring D Coefficients.q pi →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (D.serreF Coefficients.q pi) :=
  RingQuot.liftAlgHom Coefficients.Ring ⟨freeAction D Λ, fun _ _ h ↦ freeAction_rel D Λ h⟩

@[simp] theorem representation_mk (x : Free Coefficients.Ring I X) :
    representation D Λ (mk D Coefficients.q pi x) = freeAction D Λ x := by
  simp only [representation, mk, RingQuot.liftAlgHom_mkAlgHom_apply]

@[simp] theorem representation_one (μ : X) :
    representation D Λ (one D Coefficients.q pi μ) = weightProject D Λ μ := by
  rw [one, representation_mk, freeAction_one]

@[simp] theorem representation_E (i : I) (μ : X) :
    representation D Λ (E D Coefficients.q pi i μ) =
      lower D.toSuperCartanDatum i (D.h i Λ) * weightProject D Λ μ := by
  rw [E, representation_mk, freeAction_E, chevalley_true]

@[simp] theorem representation_F (i : I) (μ : X) (x : D.serreF Coefficients.q pi) :
    representation D Λ (F D Coefficients.q pi i μ) x =
      D.toSerreF Coefficients.q pi (θ Coefficients.Ring i) * weightProject D Λ μ x := by
  rw [F, representation_mk, freeAction_F, Module.End.mul_apply, chevalley_false_apply]

/-- Restriction of the constructed action to the actual nonunital modified algebra. -/
def modifiedRepresentation : modified D Coefficients.q pi →ₙₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (D.serreF Coefficients.q pi) :=
  (representation D Λ).toNonUnitalAlgHom.comp
    (NonUnitalSubalgebraClass.subtype (modified D Coefficients.q pi))

end OddMath.CoveringQuantum.UDot.GenericVerma
