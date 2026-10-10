import OddMath.CoveringQuantum.UDot.TriangularRepresentation
import OddMath.CoveringQuantum.UDot.TriangularTensor

/-!
# A concrete inverse to matched triangular multiplication

The evaluation map is constructed from the genuine weight-projected regular
representation of the modified presentation. Its vacuum value on the actual
matched normal word is the corresponding tensor. Linearity gives a retraction on
all tensors and a linear equivalence with each actual fixed-right column.

The coefficients are the generic covering ring, the datum is finite and
bar-consistent, and no independence of the simple roots is required.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open PreF Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (μ : X)

@[simp] theorem representation_halfGen (positive : Bool) (i : I) (ν : X) :
    representation D hD μ (halfGen D Coefficients.q pi positive i ν) =
      chevalley D hD μ positive i * weightProject D hD μ ν := by
  cases positive <;> simp [halfGen]

/-- The actual weight-labelled half-word acts by the regular half action after projection. -/
theorem representation_halfWord (positive : Bool) (w : List I) (ν : X) :
    representation D hD μ (halfWord D Coefficients.q pi positive w ν) =
      halfEnd D hD μ positive (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) *
        weightProject D hD μ ν := by
  induction w with
  | nil => simp [halfWord, monomial]
  | cons i w ih =>
    rw [halfWord, map_mul, representation_halfGen, mul_assoc, ← representation_one,
      ← map_mul, (halfWord_mem_block D Coefficients.q pi positive w ν).1, ih]
    simp only [monomial_cons, map_mul, ← mul_assoc]
    rfl

/-- Evaluation in the constructed regular tensor representation at its vacuum. -/
def tensorEval : CoveringUDot Coefficients.Ring D Coefficients.q pi →ₗ[Coefficients.Ring]
    D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi :=
  (LinearMap.applyₗ (1 ⊗ₜ[Coefficients.Ring] 1)).comp (representation D hD μ).toLinearMap

@[simp] theorem weightProject_vacuum :
    weightProject D hD μ μ (1 ⊗ₜ[Coefficients.Ring] 1) = 1 ⊗ₜ[Coefficients.Ring] 1 := by
  simpa only [monomial, List.map_nil, List.prod_nil, map_one, wordWeight_nil, halfWeight_zero, sub_zero, add_zero, ite_true]
    using weightProject_monomial D hD μ μ [] []

/-- Evaluation agrees with the genuine matched triangular word, not a replacement multiplication. -/
theorem tensorEval_normalWord (a b : List I) :
    tensorEval D hD μ (normalWord D Coefficients.q pi a b μ) =
      D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b) := by
  change representation D hD μ (normalWord D Coefficients.q pi a b μ) (1 ⊗ₜ[Coefficients.Ring] 1) = _
  rw [normalWord, map_mul, representation_halfWord, mul_assoc, ← representation_one,
    ← map_mul, (halfWord_mem_block D Coefficients.q pi true b μ).1, representation_halfWord]
  simp only [Module.End.mul_apply, weightProject_vacuum, halfEnd, Bool.false_eq_true, ite_false, ite_true]
  exact halfActions_vacuum D.toSuperCartanDatum hD (fun l ↦ D.h l μ) _ _

/-- Concrete retraction on every, possibly inhomogeneous, tensor. -/
@[simp] theorem tensorEval_triangularTensor
    (z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    tensorEval D hD μ (triangularTensor D Coefficients.q pi μ z) = z := by
  have hm : (tensorEval D hD μ).comp (triangularTensor D Coefficients.q pi μ) = LinearMap.id := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply, LinearMap.id_apply]
    obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
    obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi y
    induction x using induction_monomial with
    | zero => simp
    | add x z hx hz => simp only [map_add, add_tmul, hx, hz]
    | smul c x hx => simp only [map_smul, smul_tmul, tmul_smul, hx]
    | word a =>
      induction y using induction_monomial with
      | zero => simp
      | add y z hy hz => simp only [map_add, tmul_add, hy, hz]
      | smul c y hy => simp only [map_smul, tmul_smul, hy]
      | word b => rw [triangularTensor_monomial, tensorEval_normalWord]
  exact congrArg (fun f ↦ f z) hm

include hD in
/-- Matched triangular multiplication is injective over the generic covering ring. -/
theorem triangularTensor_injective :
    Function.Injective (triangularTensor D Coefficients.q pi μ) :=
  Function.LeftInverse.injective (tensorEval_triangularTensor D hD μ)

include hD in
/-- The same triangular multiplication into the actual fixed-right column is injective. -/
theorem triangularColumn_injective :
    Function.Injective (triangularColumn D Coefficients.q pi μ) := by
  intro x y h
  apply triangularTensor_injective D hD μ
  exact congrArg Subtype.val h

/-- Triangular decomposition of each actual fixed-right column. -/
def triangularColumnEquiv :
    (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) ≃ₗ[Coefficients.Ring]
      column D Coefficients.q pi μ :=
  LinearEquiv.ofBijective (triangularColumn D Coefficients.q pi μ)
    ⟨triangularColumn_injective D hD μ, triangularColumn_surjective D Coefficients.q pi μ⟩

@[simp] theorem triangularColumnEquiv_apply
    (z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    triangularColumnEquiv D hD μ z = triangularColumn D Coefficients.q pi μ z := rfl

@[simp] theorem triangularColumnEquiv_symm_apply (x : column D Coefficients.q pi μ) :
    (triangularColumnEquiv D hD μ).symm x = tensorEval D hD μ x := by
  obtain ⟨z, rfl⟩ := triangularColumn_surjective D Coefficients.q pi μ x
  change (triangularColumnEquiv D hD μ).symm ((triangularColumnEquiv D hD μ) z) =
    tensorEval D hD μ (triangularTensor D Coefficients.q pi μ z)
  rw [tensorEval_triangularTensor]
  exact (triangularColumnEquiv D hD μ).symm_apply_apply z

end OddMath.CoveringQuantum.UDot.GenericTensor
