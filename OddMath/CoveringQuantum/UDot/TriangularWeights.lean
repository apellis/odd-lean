/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TriangularSerre
import OddMath.CoveringQuantum.UDot.VermaWeights
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Genuine weight projectors on the regular tensor module

Finite support is inherited from the free root grading and descends through the
actual Serre quotient. Equal images in the weight group are grouped, with no
independence assumption on the simple roots. Both regular generators have their
required weight shifts on arbitrary tensors.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open PreF Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

private def gradingFree : PreF Coefficients.Ring I →ₗ[Coefficients.Ring]
    (X →₀ D.serreF Coefficients.q pi) :=
  (Finsupp.mapRange.linearMap (D.toSerreF Coefficients.q pi).toLinearMap).comp
    ((AddMonoidAlgebra.coeffLinearEquiv Coefficients.Ring).toLinearMap.comp
      (rootGrading D).toLinearMap)

omit [DecidableEq I] [DecidableEq X] in
private theorem gradingFree_apply (x : PreF Coefficients.Ring I) (a : X) :
    gradingFree D x a = D.toSerreF Coefficients.q pi (weightProjectFree D 0 (-a) x) := by
  simp [gradingFree, weightProjectFree]

/-- Finite weight support on the actual half, with equal weights grouped together. -/
def grading : D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
    (X →₀ D.serreF Coefficients.q pi) :=
  { toFun := fun x ↦ Finsupp.ofSupportFinite
      (fun a ↦ GenericVerma.weightProject D 0 (-a) x) (by
        obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
        have he : (fun a ↦ GenericVerma.weightProject D 0 (-a)
            (D.toSerreF Coefficients.q pi y)) = gradingFree D y := by
          funext a
          rw [GenericVerma.weightProject_mk, gradingFree_apply]
        simp only [he]
        exact (gradingFree D y).hasFiniteSupport)
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp }

omit [DecidableEq I] [DecidableEq X] in
private theorem grading_mk (x : PreF Coefficients.Ring I) :
    grading D (D.toSerreF Coefficients.q pi x) = gradingFree D x := by
  classical
  ext a
  change GenericVerma.weightProject D 0 (-a) (D.toSerreF Coefficients.q pi x) = _
  rw [GenericVerma.weightProject_mk, gradingFree_apply]

omit [DecidableEq I] [DecidableEq X] in
@[simp] theorem grading_monomial (w : List I) :
    grading D (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) =
      Finsupp.single (halfWeight D true (wordWeight w))
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
  classical
  ext a
  rw [grading_mk, gradingFree_apply, weightProjectFree_monomial]
  simp only [zero_sub, neg_neg, Finsupp.single_apply]
  split_ifs <;> simp

private def projectBilinear (μ ν : X) :
    D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
    D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
      D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi :=
  (Finsupp.lsum Coefficients.Ring fun a ↦
    (TensorProduct.mk Coefficients.Ring _ _).compl₂
      (GenericVerma.weightProject D 0 (μ - ν - a))).comp (grading D)

/-- The projector at total weight `μ - wt(x) + wt(y)` on the full tensor. -/
def weightProject (μ ν : X) : Module.End Coefficients.Ring
    (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :=
  TensorProduct.lift (projectBilinear D μ ν)

omit [DecidableEq I] in
@[simp] theorem weightProject_monomial (μ ν : X) (a b : List I) :
    weightProject D μ ν
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)) =
      if μ - halfWeight D true (wordWeight a) + halfWeight D true (wordWeight b) = ν
      then D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b) else 0 := by
  classical
  simp only [weightProject, TensorProduct.lift.tmul, projectBilinear, LinearMap.comp_apply,
    grading_monomial, Finsupp.lsum_single, LinearMap.compl₂_apply, TensorProduct.mk_apply,
    GenericVerma.weightProject_mk, weightProjectFree_monomial]
  have he : halfWeight D true (wordWeight b) = 0 - (μ - ν - halfWeight D true (wordWeight a)) ↔
      μ - halfWeight D true (wordWeight a) + halfWeight D true (wordWeight b) = ν := by
    constructor
    · intro h; rw [h]; abel
    · intro h
      calc
        _ = (μ - halfWeight D true (wordWeight a) + halfWeight D true (wordWeight b)) - μ +
            halfWeight D true (wordWeight a) := by abel
        _ = _ := by rw [h]; abel
  simp only [he]
  split_ifs <;> simp

omit [DecidableEq I] [DecidableEq X] in
/-- One homogeneous factor suffices to compute the tensor projector. -/
theorem weightProject_tmul_monomial (μ ν : X) (x : D.serreF Coefficients.q pi) (b : List I) :
    weightProject D μ ν (x ⊗ₜ[Coefficients.Ring]
      D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)) =
    GenericVerma.weightProject D (μ + halfWeight D true (wordWeight b)) ν x ⊗ₜ[Coefficients.Ring]
      D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b) := by
  classical
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  induction x using induction_monomial with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
  | smul c x hx => simp only [map_smul, smul_tmul, tmul_smul, hx]
  | word a =>
    rw [weightProject_monomial, GenericVerma.weightProject_mk, weightProjectFree_monomial]
    have he : μ - halfWeight D true (wordWeight a) + halfWeight D true (wordWeight b) = ν ↔
        halfWeight D true (wordWeight a) = μ + halfWeight D true (wordWeight b) - ν := by
      constructor
      · intro h; rw [← h]; abel
      · intro h; rw [h]; abel
    simp only [he]
    split_ifs <;> simp

omit [DecidableEq I] in
/-- Orthogonality, including idempotence, on arbitrary tensors. -/
theorem weightProject_mul (μ ν η : X) :
    weightProject D μ ν * weightProject D μ η =
      if ν = η then weightProject D μ ν else 0 := by
  classical
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi y
  induction y using induction_monomial with
  | zero => simp
  | add y z hy hz =>
    simp only [map_add, tmul_add] at *
    split_ifs at * <;> simp_all
  | smul c y hy =>
    simp only [map_smul, tmul_smul] at *
    split_ifs at * <;> simp_all
  | word b =>
    simp only [Module.End.mul_apply, weightProject_tmul_monomial]
    have hp := congrArg (fun f ↦ f x)
      (GenericVerma.weightProject_mul D (μ + halfWeight D true (wordWeight b)) ν η)
    simp only [Module.End.mul_apply] at hp
    rw [hp]
    split_ifs <;> simp_all [weightProject_tmul_monomial]

omit [DecidableEq I] [DecidableEq X] in
private theorem halfProject_shift (μ ν a : X) (x : D.serreF Coefficients.q pi) :
    GenericVerma.weightProject D (μ + a) ν x =
      GenericVerma.weightProject D μ (ν - a) x := by
  classical
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  rw [GenericVerma.weightProject_mk, GenericVerma.weightProject_mk]
  congr 1
  change (rootGrading D x).coeff (μ + a - ν) = (rootGrading D x).coeff (μ - (ν - a))
  congr 1
  abel

omit [DecidableEq I] [DecidableEq X] in
private theorem halfProject_diagonal (μ ν : X) (c : I → Coefficients.Ring)
    (x : D.serreF Coefficients.q pi) :
    GenericVerma.weightProject D μ ν (diagonal D.toSuperCartanDatum c x) =
      diagonal D.toSuperCartanDatum c (GenericVerma.weightProject D μ ν x) := by
  classical
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  simp only [diagonal_mk, GenericVerma.weightProject_mk, weightProjectFree_diag]

omit [DecidableEq X] in
private theorem halfProject_numerator (μ ν : X) (i : I) (a b : Coefficients.Ring)
    (x : D.serreF Coefficients.q pi) :
    GenericVerma.weightProject D μ ν (numerator D.toSuperCartanDatum i a b x) =
      numerator D.toSuperCartanDatum i a b (GenericVerma.weightProject D μ (ν - D.α i) x) := by
  classical
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  simp only [numerator_mk, GenericVerma.weightProject_mk, weightProjectFree_numerator]

omit [DecidableEq I] [DecidableEq X] in
/-- Negative generators lower the genuine tensor weight by a simple root. -/
theorem weightProject_negative (μ ν : X) (i : I) :
    weightProject D μ ν * negative D.toSuperCartanDatum i =
      negative D.toSuperCartanDatum i * weightProject D μ (ν + D.α i) := by
  classical
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, Module.End.mul_apply]
  obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi y
  induction y using induction_monomial with
  | zero => simp
  | add y z hy hz => simp only [map_add, tmul_add, hy, hz]
  | smul c y hy => simp only [map_smul, tmul_smul, hy]
  | word b => simp only [negative_tmul, weightProject_tmul_monomial,
      GenericVerma.weightProject_θ_mul]

omit [DecidableEq X] in
/-- Positive generators raise the genuine tensor weight by a simple root. -/
theorem weightProject_positive (μ ν : X) (n : I → ℤ) (i : I) :
    weightProject D μ ν * positive D.toSuperCartanDatum n i =
      positive D.toSuperCartanDatum n i * weightProject D μ (ν - D.α i) := by
  classical
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, Module.End.mul_apply]
  obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi y
  induction y using induction_monomial with
  | zero => simp
  | add y z hy hz => simp only [map_add, tmul_add, hy, hz]
  | smul c y hy => simp only [map_smul, tmul_smul, hy]
  | word b =>
    simp only [positive, LinearMap.add_apply, LinearMap.smul_apply, TensorProduct.map_tmul,
      AlgHom.toLinearMap_apply, create, Algebra.lsmul_apply, weight, diagonal_mk,
      diagTwist_monomial, map_smul, tmul_smul, map_add, weightProject_tmul_monomial,
      halfProject_numerator]
    congr 1
    simp only [smul_eq_mul]
    rw [← map_mul, ← monomial_cons, weightProject_tmul_monomial]
    simp only [wordWeight_cons, halfWeight_add, halfWeight_single,
      show halfRoot D true i = D.α i from rfl]
    rw [show μ + (D.α i + halfWeight D true (wordWeight b)) =
      (μ + halfWeight D true (wordWeight b)) + D.α i by abel,
      halfProject_shift, parity, halfProject_diagonal]

end OddMath.CoveringQuantum.UDot.GenericTensor
