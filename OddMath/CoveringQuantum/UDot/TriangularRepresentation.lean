/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TriangularMixed

/-!
# The actual modified regular tensor representation

The weight idempotents act by genuine tensor weight projection, and the Chevalley
generators by the regular two-half operators after projection. Every defining
relation of the actual modified presentation is verified before quotient descent.
-/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open PreF Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (Λ : X)

/-- The two actual half-algebra actions on the full tensor product. -/
def halfEnd (positive : Bool) : D.serreF Coefficients.q pi →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF
    Coefficients.q pi) :=
  if positive then positiveHalfAction D.toSuperCartanDatum (fun i ↦ D.h i Λ)
  else negativeHalfAction D.toSuperCartanDatum

/-- A Chevalley operator without its right weight projection. -/
def chevalley (positive : Bool) (i : I) :
    Module.End Coefficients.Ring (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF
    Coefficients.q pi) :=
  halfEnd D Λ positive (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))

omit [DecidableEq X] in
@[simp] theorem chevalley_true (i : I) :
    chevalley D Λ true i = positive D.toSuperCartanDatum (fun l ↦ D.h l Λ) i := by
  simp [chevalley, halfEnd]

omit [DecidableEq X] in
@[simp] theorem chevalley_false (i : I) :
    chevalley D Λ false i = negative D.toSuperCartanDatum i := rfl

omit [DecidableEq X] in
/-- Both regular Chevalley operators have the required actual weight shift. -/
theorem project_chevalley (positive : Bool) (i : I) (μ : X) :
    weightProject D Λ μ * chevalley D Λ positive i =
      chevalley D Λ positive i * weightProject D Λ (μ - halfRoot D positive i) := by
  classical
  cases positive
  · simpa only [chevalley_false, halfRoot, Bool.false_eq_true, ite_false, sub_neg_eq_add]
      using weightProject_negative D Λ μ i
  · simpa only [chevalley_true, halfRoot, ite_true]
      using weightProject_positive D Λ μ (fun l ↦ D.h l Λ) i

omit [DecidableEq X] in
private theorem project_chevalley_pow (positive : Bool) (i : I) (n : ℕ) (μ : X) :
    weightProject D Λ μ * chevalley D Λ positive i ^ n =
      chevalley D Λ positive i ^ n *
        weightProject D Λ (μ - n • halfRoot D positive i) := by
  classical
  induction n generalizing μ with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mul_assoc, project_chevalley, mul_assoc, ih, ← mul_assoc, ← pow_succ']
    congr 2
    rw [succ_nsmul]
    abel

omit [DecidableEq X] in
private theorem project_power_absorb (positive : Bool) (i : I) (n : ℕ) (μ : X) :
    weightProject D Λ (μ + n • halfRoot D positive i) *
      chevalley D Λ positive i ^ n * weightProject D Λ μ =
        chevalley D Λ positive i ^ n * weightProject D Λ μ := by
  classical
  rw [project_chevalley_pow, add_sub_cancel_right, mul_assoc, weightProject_mul]
  simp

/-- The actual action assigned to each generator of the unital envelope. -/
def genAction : Gen I X → Module.End Coefficients.Ring (D.serreF Coefficients.q pi
    ⊗[Coefficients.Ring] D.serreF Coefficients.q pi)
  | .one μ => weightProject D Λ μ
  | .e i μ => chevalley D Λ true i * weightProject D Λ μ
  | .f i μ => chevalley D Λ false i * weightProject D Λ μ

/-- Evaluation of the free presentation in concrete endomorphisms. -/
def freeAction : Free Coefficients.Ring I X →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF
    Coefficients.q pi) :=
  FreeAlgebra.lift Coefficients.Ring (genAction D Λ)

omit [DecidableEq X] in
@[simp] theorem freeAction_one (μ : X) :
    freeAction D Λ (Free.one Coefficients.Ring μ) = weightProject D Λ μ := by
  classical
  simp [freeAction, Free.one, genAction]

omit [DecidableEq X] in
@[simp] theorem freeAction_E (i : I) (μ : X) :
    freeAction D Λ (Free.E Coefficients.Ring i μ) =
      chevalley D Λ true i * weightProject D Λ μ := by
  classical
  simp [freeAction, Free.E, genAction]

omit [DecidableEq X] in
@[simp] theorem freeAction_F (i : I) (μ : X) :
    freeAction D Λ (Free.F Coefficients.Ring i μ) =
      chevalley D Λ false i * weightProject D Λ μ := by
  classical
  simp [freeAction, Free.F, genAction]

omit [DecidableEq X] in
private theorem freeAction_epow (i : I) (n : ℕ) (μ : X) :
    freeAction D Λ (epow D i n μ) =
      chevalley D Λ true i ^ n * weightProject D Λ μ := by
  classical
  induction n with
  | zero => simp [epow]
  | succ n ih =>
    have hp := project_power_absorb D Λ true i n μ
    simp only [halfRoot, ite_true] at hp
    rw [epow, map_mul, freeAction_E, ih, mul_assoc, ← mul_assoc
      (weightProject D Λ _), hp, ← mul_assoc, ← pow_succ']

omit [DecidableEq X] in
private theorem freeAction_fpow (i : I) (n : ℕ) (μ : X) :
    freeAction D Λ (fpow D i n μ) =
      chevalley D Λ false i ^ n * weightProject D Λ μ := by
  classical
  induction n with
  | zero => simp [fpow]
  | succ n ih =>
    rw [fpow, map_mul, freeAction_F, ih]
    have he : μ - n • D.α i = μ + n • halfRoot D false i := by simp [halfRoot, sub_eq_add_neg]
    rw [he, mul_assoc, ← mul_assoc (weightProject D Λ _),
      project_power_absorb, ← mul_assoc, ← pow_succ']

omit [DecidableEq X] in
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

omit [DecidableEq X] in
private theorem chevalley_serre (positive : Bool) {i j : I} (hij : i ≠ j) :
    ∑ r ∈ Finset.range (D.serreDeg i j + 1),
      D.serreCoeff Coefficients.q pi i j r •
        (chevalley D Λ positive i ^ (D.serreDeg i j - r) *
          chevalley D Λ positive j * chevalley D Λ positive i ^ r) = 0 := by
  have h := congrArg (halfEnd D Λ positive) (D.toSerreF_serreElt Coefficients.q pi hij)
  simpa only [SuperCartanDatum.serreElt, map_sum, map_smul, map_mul, map_pow, map_zero,
    chevalley] using h

omit [DecidableEq X] in
private theorem freeAction_serreE {i j : I} (hij : i ≠ j) (μ : X) :
    freeAction D Λ (serreE D Coefficients.q pi i j μ) = 0 := by
  classical
  simp only [serreE, map_sum, map_smul, map_mul, freeAction_epow, freeAction_E]
  have ht := projected_serre_term D Λ true i j
  simp only [halfRoot, ite_true] at ht
  simp only [ht, ← smul_mul_assoc, ← Finset.sum_mul]
  simpa only [← smul_mul_assoc, zero_mul] using
    congrArg (· * weightProject D Λ μ) (chevalley_serre D Λ true hij)

omit [DecidableEq X] in
private theorem freeAction_serreF {i j : I} (hij : i ≠ j) (μ : X) :
    freeAction D Λ (serreF D Coefficients.q pi i j μ) = 0 := by
  classical
  simp only [serreF, map_sum, map_smul, map_mul, freeAction_fpow, freeAction_F]
  have ht := projected_serre_term D Λ false i j
  simp only [halfRoot, Bool.false_eq_true, ite_false, smul_neg, ← sub_eq_add_neg] at ht
  simp only [ht, ← smul_mul_assoc, ← Finset.sum_mul]
  simpa only [← smul_mul_assoc, zero_mul] using
    congrArg (· * weightProject D Λ μ) (chevalley_serre D Λ false hij)

omit [DecidableEq X] in
private theorem project_step_absorb (positive : Bool) (i : I) (μ : X) :
    weightProject D Λ (μ + halfRoot D positive i) *
      (chevalley D Λ positive i * weightProject D Λ μ) =
        chevalley D Λ positive i * weightProject D Λ μ := by
  classical
  rw [← mul_assoc, project_chevalley, add_sub_cancel_right, mul_assoc, weightProject_mul]
  simp

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
    let : AddCommGroup (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q
    pi) :=
      TensorProduct.addCommGroup
    have he := project_step_absorb D Λ true i μ
    have hf := project_step_absorb D Λ false j μ
    simp only [halfRoot, ite_true] at he
    simp only [halfRoot, Bool.false_eq_true, ite_false, ← sub_eq_add_neg] at hf
    rw [map_sub, map_mul, map_smul, map_mul, freeAction_E, freeAction_F,
      freeAction_F, freeAction_E]
    simp only [mul_assoc, he, hf]
    apply LinearMap.ext
    intro z
    have hm := positive_negative_project D Λ μ i j z
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      chevalley_true, chevalley_false]
    rw [hm, add_sub_cancel_left]
    split_ifs <;> simp

/-- The actual regular tensor action of the unital envelope. It restricts to the
modified algebra; this is a representation, not an injectivity statement. -/
def representation : CoveringUDot Coefficients.Ring D Coefficients.q pi →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF
    Coefficients.q pi) :=
  RingQuot.liftAlgHom Coefficients.Ring ⟨freeAction D Λ, fun _ _ h ↦ freeAction_rel D Λ h⟩

@[simp] theorem representation_mk (x : Free Coefficients.Ring I X) :
    representation D Λ (mk D Coefficients.q pi x) = freeAction D Λ x := by
  simp only [representation, mk, RingQuot.liftAlgHom_mkAlgHom_apply]

@[simp] theorem representation_one (μ : X) :
    representation D Λ (one D Coefficients.q pi μ) = weightProject D Λ μ := by
  rw [one, representation_mk, freeAction_one]

@[simp] theorem representation_E (i : I) (μ : X) :
    representation D Λ (E D Coefficients.q pi i μ) =
      positive D.toSuperCartanDatum (fun l ↦ D.h l Λ) i * weightProject D Λ μ := by
  rw [E, representation_mk, freeAction_E, chevalley_true]

@[simp] theorem representation_F (i : I) (μ : X) :
    representation D Λ (F D Coefficients.q pi i μ) =
      negative D.toSuperCartanDatum i * weightProject D Λ μ := by
  rw [F, representation_mk, freeAction_F, chevalley_false]

/-- Restriction of the constructed action to the actual nonunital modified algebra. -/
def modifiedRepresentation : modified D Coefficients.q pi →ₙₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF
    Coefficients.q pi) :=
  (representation D Λ).toNonUnitalAlgHom.comp (NonUnitalSubalgebraClass.subtype (modified D
    Coefficients.q pi))

end OddMath.CoveringQuantum.UDot.GenericTensor
