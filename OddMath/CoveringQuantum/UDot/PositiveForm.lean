import OddMath.CoveringQuantum.UDot.ModifiedFormTransport

/-!
# Positive-normalized bilinear form on the modified covering algebra

Finite diagonal contraction of the actual positive column functional constructs
`positiveModifiedForm`. It has both endpoint orthogonality, rho-adjointness, and
normalization on every pair in the positive half algebra. These properties hold
for finite bar-consistent data over the generic covering ring, without root
independence. This is the bilinear precursor to the sesquilinear form of
Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.1 and its following remark.
Nondegeneracy and existence without bar consistency are not asserted here.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients TensorProduct PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent)

/-- The column functional evaluated on the diagonal corner of actual triangular multiplication. -/
def positiveDiagonalContraction (μ : X) :
    D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
      Coefficients.Ring where
  toFun z := columnFunctional D hD μ
    (one D Coefficients.q pi μ * triangularTensor D Coefficients.q pi μ z)
  map_add' _ _ := by simp [mul_add]
  map_smul' _ _ := by simp

/-- Sum the diagonal column functionals over the genuine finite coordinate support. -/
def positiveDiagonalFunctional : modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring :=
  (Finsupp.lsum Coefficients.Ring (positiveDiagonalContraction D hD)).comp (triangularCoordinates D hD)

@[simp] theorem positiveDiagonalFunctional_triangularModified (μ : X)
    (z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    positiveDiagonalFunctional D hD (triangularModified D Coefficients.q pi μ z) =
      columnFunctional D hD μ (one D Coefficients.q pi μ * triangularTensor D Coefficients.q pi μ z) := by
  rw [← globalTriangular_single]
  simp only [positiveDiagonalFunctional, LinearMap.comp_apply, triangularCoordinates_globalTriangular,
    Finsupp.lsum_single, positiveDiagonalContraction]
  rfl

theorem positiveDiagonalFunctional_column (μ : X) (x : modified D Coefficients.q pi)
    (hx : (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ column D Coefficients.q pi μ) :
    positiveDiagonalFunctional D hD x = columnFunctional D hD μ
      (one D Coefficients.q pi μ * (x : CoveringUDot Coefficients.Ring D Coefficients.q pi)) := by
  obtain ⟨z, hz⟩ := triangularColumn_surjective D Coefficients.q pi μ ⟨x, hx⟩
  have he : triangularModified D Coefficients.q pi μ z = x := by
    apply Subtype.ext
    exact congrArg (fun a : column D Coefficients.q pi μ ↦ a.val) hz
  rw [← he, positiveDiagonalFunctional_triangularModified]
  rfl

/-- Different diagonal endpoints are annihilated, with no root-separation assumption. -/
theorem positiveDiagonalFunctional_offDiagonal (μ ν : X) (x : modified D Coefficients.q pi)
    (hx : (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν)
    (hne : μ ≠ ν) : positiveDiagonalFunctional D hD x = 0 := by
  rw [positiveDiagonalFunctional_column D hD ν x hx.2, one_mul_of_mem_block D Coefficients.q pi hx]
  simp [Ne.symm hne]

/-- The full bilinear form is defined on the actual nonunital modified algebra.
Its multiplication and adjoint are the existing quotient operations. -/
def positiveModifiedForm : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi) where
  toFun x :=
    { toFun := fun y ↦ positiveDiagonalFunctional D hD (rhoModified D Coefficients.q pi pi_sq x * y)
      map_add' := by intro y z; simp [mul_add]
      map_smul' := by intro c y; simp [mul_smul_comm] }
  map_add' := by intro x z; ext y; simp [add_mul]
  map_smul' := by intro c x; ext y; simp [smul_mul_assoc]

@[simp] theorem positiveModifiedForm_apply (x y : modified D Coefficients.q pi) :
    positiveModifiedForm D hD x y = positiveDiagonalFunctional D hD (rhoModified D Coefficients.q pi pi_sq x * y) := rfl

/-- Adjointness for every actual modified element, not only Chevalley generators. -/
theorem positiveModifiedForm_adjoint (u x y : modified D Coefficients.q pi) :
    positiveModifiedForm D hD (u * x) y =
      positiveModifiedForm D hD x (rhoModified D Coefficients.q pi pi_sq u * y) := by
  simp only [positiveModifiedForm_apply, rhoModified_mul, mul_assoc]

/-- Both left and right endpoints are orthogonal. -/
theorem positiveModifiedForm_orthogonal (μ ν μ' ν' : X) (x y : modified D Coefficients.q pi)
    (hx : (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν)
    (hy : (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ' ν')
    (hne : μ ≠ μ' ∨ ν ≠ ν') : positiveModifiedForm D hD x y = 0 := by
  rw [positiveModifiedForm_apply]
  have hr := rho_mem_block D Coefficients.q pi pi_sq hx
  rcases hne with h | h
  · have hz : rhoModified D Coefficients.q pi pi_sq x * y = 0 :=
      Subtype.ext (mul_eq_zero_of_mem_block D Coefficients.q pi hr hy h)
    rw [hz, map_zero]
  · exact positiveDiagonalFunctional_offDiagonal D hD ν ν' _ (mul_mem_block D Coefficients.q pi hr hy) h

/-- Every positive-half pair has the original half form as normalization. -/
theorem positiveModifiedForm_positiveHalf (μ : X) (x y : D.serreF Coefficients.q pi) :
    positiveModifiedForm D hD (positiveHalf D Coefficients.q pi μ x) (positiveHalf D Coefficients.q pi μ y) =
      D.serreForm Coefficients.q pi pi_sq x y := by
  have hx : halfMap D Coefficients.q pi true μ x * one D Coefficients.q pi μ =
      halfMap D Coefficients.q pi true μ x := by
    change halfMap D Coefficients.q pi true μ x ∈ column D Coefficients.q pi μ
    simpa only [triangularTensor_one_tmul] using
      triangularTensor_mem_column D Coefficients.q pi μ (1 ⊗ₜ[Coefficients.Ring] x)
  have hy : halfMap D Coefficients.q pi true μ y * one D Coefficients.q pi μ =
      halfMap D Coefficients.q pi true μ y := by
    change halfMap D Coefficients.q pi true μ y ∈ column D Coefficients.q pi μ
    simpa only [triangularTensor_one_tmul] using
      triangularTensor_mem_column D Coefficients.q pi μ (1 ⊗ₜ[Coefficients.Ring] y)
  have hr : one D Coefficients.q pi μ *
      (rho D Coefficients.q pi pi_sq (halfMap D Coefficients.q pi true μ x)).unop =
      (rho D Coefficients.q pi pi_sq (halfMap D Coefficients.q pi true μ x)).unop := by
    simpa only [rho_mul, rho_one] using congrArg (fun z ↦ (rho D Coefficients.q pi pi_sq z).unop) hx
  rw [positiveModifiedForm_apply, positiveDiagonalFunctional_column D hD μ _ (by
    change ((rho D Coefficients.q pi pi_sq (halfMap D Coefficients.q pi true μ x)).unop *
      halfMap D Coefficients.q pi true μ y) * one D Coefficients.q pi μ = _
    rw [mul_assoc, hy]
    rfl)]
  change columnFunctional D hD μ
    (one D Coefficients.q pi μ * ((rho D Coefficients.q pi pi_sq
      (halfMap D Coefficients.q pi true μ x)).unop * halfMap D Coefficients.q pi true μ y)) = _
  rw [← mul_assoc, hr, columnFunctional_rho_halfMap]

end OddMath.CoveringQuantum.UDot.GenericTensor
