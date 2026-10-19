/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.VermaSerre
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Regular triangular tensor operators

Concrete operators on the tensor product of the actual Serre halves and their
vacuum evaluation. These formulas do not yet assert an action of the modified
presentation: that assertion also requires the positive Serre and weight relations.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open PreF Coefficients TensorProduct
variable {I : Type*} [DecidableEq I]
variable (C : SuperCartanDatum I)

/-- Diagonal scaling on the actual Serre quotient. -/
def diagonal (c : I → Coefficients.Ring) :
    C.serreF Coefficients.q pi →ₐ[Coefficients.Ring] C.serreF Coefficients.q pi :=
  RingQuot.liftAlgHom Coefficients.Ring
    ⟨(C.toSerreF Coefficients.q pi).comp (diagTwist c), by
      intro x y h
      cases h with
      | serre i j hij =>
        simp only [AlgHom.comp_apply, C.diagTwist_serreElt, map_smul,
          C.toSerreF_serreElt Coefficients.q pi hij, smul_zero, map_zero]⟩

omit [DecidableEq I] in
@[simp] theorem diagonal_mk (c : I → Coefficients.Ring) (x : PreF Coefficients.Ring I) :
    diagonal C c (C.toSerreF Coefficients.q pi x) =
      C.toSerreF Coefficients.q pi (diagTwist c x) := by
  simp only [diagonal, SuperCartanDatum.toSerreF, RingQuot.liftAlgHom_mkAlgHom_apply,
    AlgHom.comp_apply]

omit [DecidableEq I] in
@[simp] theorem diagonal_θ (c : I → Coefficients.Ring) (i : I) :
    diagonal C c (C.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
      c i • C.toSerreF Coefficients.q pi (θ Coefficients.Ring i) := by
  rw [diagonal_mk, diagTwist_θ, map_smul]

private abbrev projection : PreF Coefficients.Ring I →ₗ[Coefficients.Ring]
    C.serreF Coefficients.q pi := (C.toSerreF Coefficients.q pi).toLinearMap

private theorem numerator_preserves (i : I) (a b : Coefficients.Ring)
    {x : PreF Coefficients.Ring I} (hx : x ∈ C.serreIdeal Coefficients.q pi) :
    C.toSerreF Coefficients.q pi (lowerNumerator C Coefficients.q pi i a b x) = 0 := by
  have hr := C.diagTwist_mem_serreIdeal Coefficients.q pi
    (fun j ↦ pi ^ (C.parity i * C.parity j).val) (GenericVerma.rDeriv_mem_serreIdeal C i hx)
  have hl := C.diagTwist_mem_serreIdeal Coefficients.q pi
    (fun j ↦ ((Coefficients.q ^ C.dot i j : Coefficients.Ringˣ) : Coefficients.Ring))
    (GenericVerma.lDeriv_mem_serreIdeal C i hx)
  rw [C.mem_serreIdeal] at hr hl
  simp only [lowerNumerator, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, map_sub, map_smul, parityTwist, weightTwist, hr, hl,
    smul_zero, sub_zero]

/-- The lowering numerator with arbitrary coefficients, on the genuine half quotient. -/
def numerator (i : I) (a b : Coefficients.Ring) :
    Module.End Coefficients.Ring (C.serreF Coefficients.q pi) :=
  let p := projection C
  let f := p.comp (lowerNumerator C Coefficients.q pi i a b)
  ((LinearMap.ker p).liftQ f (by
    intro x hx
    exact numerator_preserves C i a b ((C.mem_serreIdeal Coefficients.q pi x).mpr hx))).comp
    (p.quotKerEquivOfSurjective (C.toSerreF_surjective Coefficients.q pi)).symm.toLinearMap

@[simp] theorem numerator_mk (i : I) (a b : Coefficients.Ring) (x : PreF Coefficients.Ring I) :
    numerator C i a b (C.toSerreF Coefficients.q pi x) =
      C.toSerreF Coefficients.q pi (lowerNumerator C Coefficients.q pi i a b x) := by
  simp only [numerator, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change (LinearMap.ker (projection C)).liftQ _ _
    (((projection C).quotKerEquivOfSurjective _).symm (projection C x)) = _
  exact congrArg ((LinearMap.ker (projection C)).liftQ _ _)
    ((projection C).quotKerEquivOfSurjective_symm_apply
      (C.toSerreF_surjective Coefficients.q pi) x)

@[simp] theorem numerator_one (i : I) (a b : Coefficients.Ring) :
    numerator C i a b 1 = 0 := by
  rw [← map_one (C.toSerreF Coefficients.q pi), numerator_mk, lowerNumerator_one, map_zero]

/-- Parity on the first tensor factor. -/
def parity (i : I) : C.serreF Coefficients.q pi →ₐ[Coefficients.Ring]
    C.serreF Coefficients.q pi := diagonal C fun j ↦ pi ^ (C.parity i * C.parity j).val

/-- The quantum weight scaling, with either sign of the exponent. -/
def weight (v : Coefficients.Ringˣ) (i : I) : C.serreF Coefficients.q pi →ₐ[Coefficients.Ring]
    C.serreF Coefficients.q pi :=
  diagonal C fun j ↦ ((v ^ C.dot i j : Coefficients.Ringˣ) : Coefficients.Ring)

omit [DecidableEq I] in
private theorem parity_twist (i : I) (x : PreF Coefficients.Ring I) :
    parityTwist C pi i (twist (C.chi Coefficients.q pi) i x) =
      weightTwist C Coefficients.q⁻¹ i x := by
  rw [parityTwist, twist, diagTwist_diagTwist]
  have hc : (fun j ↦ pi ^ (C.parity i * C.parity j).val) *
      (fun j ↦ C.chi Coefficients.q pi i j) =
      (fun j ↦ ((Coefficients.q⁻¹ ^ C.dot i j : Coefficients.Ringˣ) : Coefficients.Ring)) := by
    funext j
    simp only [Pi.mul_apply, SuperCartanDatum.chi_apply, inv_zpow, ← zpow_neg]
    have hp : pi ^ (C.parity i * C.parity j).val * pi ^ (C.parity i * C.parity j).val = 1 := by
      rw [← pow_two, ← pow_mul, mul_comm _ 2, pow_mul, pi_sq, one_pow]
    rw [mul_left_comm, hp, mul_one]
  rw [hc]
  rfl

/-- The mixed relation for quotient numerators with arbitrary coefficients. -/
theorem numerator_create (i j : I) (a b : Coefficients.Ring)
    (x : C.serreF Coefficients.q pi) :
    numerator C i a b (C.toSerreF Coefficients.q pi (θ Coefficients.Ring j) * x) =
      pi ^ (C.parity i * C.parity j).val •
        (C.toSerreF Coefficients.q pi (θ Coefficients.Ring j) * numerator C i a b x) +
      if i = j then a • weight C Coefficients.q⁻¹ i x - b • weight C Coefficients.q i x else 0 := by
  obtain ⟨x, rfl⟩ := C.toSerreF_surjective Coefficients.q pi x
  rw [← map_mul, numerator_mk, lowerNumerator_θ_mul, map_add, map_smul, map_mul,
    numerator_mk]
  congr 1
  split_ifs
  · simp only [parity_twist, map_sub, map_smul, weight, diagonal_mk, weightTwist]
  · exact map_zero _

/-- Left multiplication by a simple generator of the actual half. -/
def create (i : I) : Module.End Coefficients.Ring (C.serreF Coefficients.q pi) :=
  Algebra.lsmul Coefficients.Ring Coefficients.Ring (C.serreF Coefficients.q pi)
    (C.toSerreF Coefficients.q pi (θ Coefficients.Ring i))

/-- The negative regular operator on the first factor. -/
def negative (i : I) : Module.End Coefficients.Ring
    (C.serreF Coefficients.q pi ⊗[Coefficients.Ring] C.serreF Coefficients.q pi) :=
  TensorProduct.map (create C i) LinearMap.id

/-- The positive regular operator. The second factor changes the highest-weight
parameters of the lowering term; it is not a fixed highest-weight action tensored
with the identity. The raising term carries the parity of the first factor. -/
def positive (n : I → ℤ) (i : I) : Module.End Coefficients.Ring
    (C.serreF Coefficients.q pi ⊗[Coefficients.Ring] C.serreF Coefficients.q pi) :=
  TensorProduct.map (parity C i).toLinearMap (create C i) +
    Ring.inverse (vermaDenominator C Coefficients.q pi i) •
      (TensorProduct.map (numerator C i
        (((C.qi Coefficients.q i) ^ n i : Coefficients.Ringˣ) : Coefficients.Ring) 0)
        (weight C Coefficients.q i).toLinearMap +
      TensorProduct.map (numerator C i 0
        (C.pii pi i ^ (n i).natAbs *
          (((C.qi Coefficients.q i) ^ (-n i) : Coefficients.Ringˣ) : Coefficients.Ring)))
        (weight C Coefficients.q⁻¹ i).toLinearMap)

omit [DecidableEq I] in
@[simp] theorem negative_tmul (i : I) (x y : C.serreF Coefficients.q pi) :
    negative C i (x ⊗ₜ[Coefficients.Ring] y) =
      (C.toSerreF Coefficients.q pi (θ Coefficients.Ring i) * x) ⊗ₜ[Coefficients.Ring] y := rfl

/-- On a first-factor vacuum the positive operator is exact creation in the
second factor. There are no lower terms in this regular-module convention. -/
@[simp] theorem positive_one_tmul (n : I → ℤ) (i : I) (y : C.serreF Coefficients.q pi) :
    positive C n i (1 ⊗ₜ[Coefficients.Ring] y) =
      (1 : C.serreF Coefficients.q pi) ⊗ₜ[Coefficients.Ring]
        (C.toSerreF Coefficients.q pi (θ Coefficients.Ring i) * y) := by
  simp [positive, TensorProduct.map_tmul, create, Algebra.lsmul_apply]

/-- Opposite quantum weight scalings on the two tensor factors. -/
def toral (v : Coefficients.Ringˣ) (i : I) : Module.End Coefficients.Ring
    (C.serreF Coefficients.q pi ⊗[Coefficients.Ring] C.serreF Coefficients.q pi) :=
  TensorProduct.map (weight C v⁻¹ i).toLinearMap (weight C v i).toLinearMap

/-- The concrete regular operators satisfy the mixed supercommutator on the
whole tensor product, not just the vacuum or a selected homogeneous submodule. -/
theorem positive_negative (n : I → ℤ) (i j : I) :
    positive C n i * negative C j =
      pi ^ (C.parity i * C.parity j).val • (negative C j * positive C n i) +
      if i = j then Ring.inverse (vermaDenominator C Coefficients.q pi i) •
        (((((C.qi Coefficients.q i) ^ n i : Coefficients.Ringˣ) : Coefficients.Ring)) •
            toral C Coefficients.q i +
          (-(C.pii pi i ^ (n i).natAbs *
            (((C.qi Coefficients.q i) ^ (-n i) : Coefficients.Ringˣ) : Coefficients.Ring))) •
            toral C Coefficients.q⁻¹ i)
      else 0 := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  simp only [Module.End.mul_apply, negative_tmul, positive, LinearMap.add_apply,
    LinearMap.smul_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
    numerator_create, parity, map_mul, diagonal_θ, toral, inv_inv]
  by_cases h : i = j
  · subst j
    simp only [ite_true, zero_smul, sub_zero, zero_sub, add_tmul, smul_tmul,
      create, Algebra.lsmul_apply, map_add, map_smul, smul_mul_assoc, tmul_smul, neg_tmul,
      LinearMap.smul_apply, LinearMap.add_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      negative_tmul]
    simp only [smul_add, smul_tmul', ← neg_tmul, smul_neg, neg_smul, smul_smul,
      mul_comm (Ring.inverse (vermaDenominator C Coefficients.q pi i))]
    abel
  · simp only [h, ite_false, add_zero, zero_smul, smul_tmul,
      create, Algebra.lsmul_apply, map_add, map_smul, smul_mul_assoc, tmul_smul,
      LinearMap.zero_apply, negative_tmul]
    simp only [smul_add, smul_smul,
      mul_comm (Ring.inverse (vermaDenominator C Coefficients.q pi i))]

/-- Free positive words evaluated in the concrete regular operators. Descent
through the positive Serre relations is a separate obligation. -/
def positiveFree (n : I → ℤ) : PreF Coefficients.Ring I →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring
      (C.serreF Coefficients.q pi ⊗[Coefficients.Ring] C.serreF Coefficients.q pi) :=
  FreeAlgebra.lift Coefficients.Ring (positive C n)

/-- The actual negative half acts by left multiplication on the first factor. -/
def negativeHalfAction : C.serreF Coefficients.q pi →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring
      (C.serreF Coefficients.q pi ⊗[Coefficients.Ring] C.serreF Coefficients.q pi) where
  toFun x := TensorProduct.map
    (Algebra.lsmul Coefficients.Ring Coefficients.Ring (C.serreF Coefficients.q pi) x) LinearMap.id
  map_one' := by ext x y; simp
  map_mul' x y := by ext z w; simp [Module.End.mul_apply]
  map_zero' := by ext x y; simp
  map_add' x y := by ext z w; simp [add_tmul]
  commutes' c := by ext x y; simp [Algebra.algebraMap_eq_smul_one, smul_tmul']

@[simp] theorem positiveFree_θ (n : I → ℤ) (i : I) :
    positiveFree C n (θ Coefficients.Ring i) = positive C n i := by
  simp [positiveFree, θ]

/-- All positive words act on a first-factor vacuum by their actual Serre class. -/
theorem positiveFree_vacuum (n : I → ℤ) (x : PreF Coefficients.Ring I)
    (y : C.serreF Coefficients.q pi) :
    positiveFree C n x (1 ⊗ₜ[Coefficients.Ring] y) =
      (1 : C.serreF Coefficients.q pi) ⊗ₜ[Coefficients.Ring]
        (C.toSerreF Coefficients.q pi x * y) := by
  induction x using induction_left with
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one, tmul_smul]
  | smul c x hx => simp [hx, smul_tmul', tmul_smul]
  | add x z hx hz => simp [hx, hz, add_mul, tmul_add]
  | θ_mul i x hx =>
    rw [map_mul, Module.End.mul_apply, hx, positiveFree_θ, positive_one_tmul, map_mul]
    simp only [mul_assoc]

/-- Exact triangular tensor evaluation for the concrete regular operators.
To obtain injectivity of multiplication in the modified algebra, these operators
must still be shown to satisfy every relation of that algebra. -/
theorem triangular_vacuum (n : I → ℤ) (x : C.serreF Coefficients.q pi)
    (y : PreF Coefficients.Ring I) :
    negativeHalfAction C x
      (positiveFree C n y ((1 : C.serreF Coefficients.q pi) ⊗ₜ[Coefficients.Ring] 1)) =
      x ⊗ₜ[Coefficients.Ring] C.toSerreF Coefficients.q pi y := by
  rw [positiveFree_vacuum]
  simp [negativeHalfAction]

omit [DecidableEq I] in
/-- The negative Serre relations already hold on the entire tensor product,
since the negative action factors through the actual quotient. -/
theorem negative_serre (i j : I) (hij : i ≠ j) :
    ∑ r ∈ Finset.range (C.serreDeg i j + 1),
      C.serreCoeff Coefficients.q pi i j r •
        (negative C i ^ (C.serreDeg i j - r) * negative C j * negative C i ^ r) = 0 := by
  have h := congrArg (negativeHalfAction C) (C.toSerreF_serreElt Coefficients.q pi hij)
  have hθ (l : I) : negativeHalfAction C (C.toSerreF Coefficients.q pi (θ Coefficients.Ring l)) =
      negative C l := rfl
  simpa only [SuperCartanDatum.serreElt, map_sum, map_smul, map_mul, map_pow, map_zero, hθ] using h

/-- The positive Serre elements kill every first-factor vacuum. This restricted
statement is not the missing positive Serre operator identity on the full tensor. -/
theorem positive_serre_vacuum (n : I → ℤ) (i j : I) (hij : i ≠ j)
    (y : C.serreF Coefficients.q pi) :
    positiveFree C n (C.serreElt Coefficients.q pi i j)
      ((1 : C.serreF Coefficients.q pi) ⊗ₜ[Coefficients.Ring] y) = 0 := by
  rw [positiveFree_vacuum, C.toSerreF_serreElt Coefficients.q pi hij, zero_mul,
    TensorProduct.tmul_zero]

end OddMath.CoveringQuantum.UDot.GenericTensor
