import OddMath.CoveringQuantum.UDot.GlobalTriangular
import OddMath.CoveringQuantum.UDot.RhoHalfWords

/-!
# A positive-column adjoint functional

This is an intermediate construction for the modified-algebra form. The
functional is defined on the actual quotient, using its proved triangular
coordinates, the half form and the actual adjoint involution. Its normalization
holds for every pair in the positive half, not only homogeneous pairs.

The negative-half normalization in Lusztig, Introduction to Quantum Groups,
Theorem 26.1.2, and Clark, arXiv:1312.4855v2, Theorem 5.2, requires a further
convention transport, proved in `NegativeColumnFunctional`. The full bilinear
form is constructed in `ModifiedForm`. In particular this intermediate
functional is not the sesquilinear form of Brundan–Ellis, arXiv:1701.04133v2, §10.

The coefficient ring is the generic covering ring. Finiteness and bar
consistency enter through triangular coordinates. No independence of the
simple roots is imposed.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients TensorProduct PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent)

/-- Contract the negative factor against the half-algebra unit. -/
def positiveProjection :
    D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
      D.serreF Coefficients.q pi :=
  TensorProduct.lift
    { toFun := fun x ↦ (D.serreForm Coefficients.q pi pi_sq 1 x) • LinearMap.id
      map_add' := by intro x y; simp [add_smul]
      map_smul' := by intro c x; simp [smul_smul] }

omit [DecidableEq X] [Finite I] in
@[simp] theorem positiveProjection_tmul (x y : D.serreF Coefficients.q pi) :
    positiveProjection D (x ⊗ₜ[Coefficients.Ring] y) =
      D.serreForm Coefficients.q pi pi_sq 1 x • y := rfl

/-- Sum positive-half components across the genuine finite column support. -/
def positiveTotal : modified D Coefficients.q pi →ₗ[Coefficients.Ring] D.serreF Coefficients.q pi :=
  (Finsupp.lsum Coefficients.Ring fun _ : X ↦ positiveProjection D).comp (triangularCoordinates D hD)

@[simp] theorem positiveTotal_half (μ : X) (x : D.serreF Coefficients.q pi) :
    positiveTotal D hD (positiveHalf D Coefficients.q pi μ x) = x := by
  have he : positiveHalf D Coefficients.q pi μ x =
      globalTriangular D (Finsupp.single μ (1 ⊗ₜ[Coefficients.Ring] x)) := by
    apply Subtype.ext
    simp only [globalTriangular_single]
    exact (triangularTensor_one_tmul D Coefficients.q pi μ x).symm
  rw [he, positiveTotal, LinearMap.comp_apply, triangularCoordinates_globalTriangular,
    Finsupp.lsum_single, positiveProjection_tmul, SuperCartanDatum.serreForm_one_one, one_smul]

/-- Negative half elements arranged at a fixed left endpoint, with their actual shifted columns. -/
def negativeRow (μ : X) : D.serreF Coefficients.q pi →ₗ[Coefficients.Ring] modified D Coefficients.q pi :=
  (Finsupp.lsum Coefficients.Ring fun a : X ↦ negativeHalf D Coefficients.q pi (μ + a)).comp
    (grading D hD)

@[simp] theorem negativeRow_monomial (μ : X) (w : List I) :
    negativeRow D hD μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) =
      negativeHalf D Coefficients.q pi (μ + halfWeight D true (wordWeight w))
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
  simp [negativeRow, grading_monomial]

/-- Undo adjoint reversal by applying the actual involution to a negative row.
The definition uses only existing quotient maps, finite support, and actual multiplication. -/
def undoRho (μ : X) : D.serreF Coefficients.q pi →ₗ[Coefficients.Ring] D.serreF Coefficients.q pi :=
  (positiveTotal D hD).comp ((rhoModified D Coefficients.q pi pi_sq).comp (negativeRow D hD μ))

/-- The unit coefficient is retained rather than silently identifying rho with sigma. -/
theorem undoRho_of_rho_word (μ : X) (w : List I) (c : Coefficients.Ringˣ)
    (hc : (rho D Coefficients.q pi pi_sq (halfWord D Coefficients.q pi true w μ)).unop =
      (c : Coefficients.Ring) • halfWord D Coefficients.q pi false w.reverse
        (μ + halfWeight D true (wordWeight w))) :
    undoRho D hD μ ((c : Coefficients.Ring) •
      D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w.reverse)) =
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w) := by
  have hw : wordWeight w.reverse = wordWeight w := by simp [wordWeight, List.map_reverse]
  have hr : negativeRow D hD μ ((c : Coefficients.Ring) •
      D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w.reverse)) =
      rhoModified D Coefficients.q pi pi_sq
        (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) := by
    rw [map_smul, negativeRow_monomial, hw]
    apply Subtype.ext
    change (c : Coefficients.Ring) • halfMap D Coefficients.q pi false _ _ =
      (rho D Coefficients.q pi pi_sq (halfMap D Coefficients.q pi true μ _)).unop
    rw [halfMap_monomial, halfMap_monomial]
    exact hc.symm
  change positiveTotal D hD (rhoModified D Coefficients.q pi pi_sq
    (negativeRow D hD μ _)) = _
  rw [hr, rhoModified_rhoModified, positiveTotal_half]

/-- The adjoint-corrected contraction on triangular tensors. -/
def columnContraction (μ : X) :
    D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
      Coefficients.Ring :=
  TensorProduct.lift (LinearMap.comp (D.serreForm Coefficients.q pi pi_sq) (undoRho D hD μ))

@[simp] theorem columnContraction_tmul (μ : X) (x y : D.serreF Coefficients.q pi) :
    columnContraction D hD μ (x ⊗ₜ[Coefficients.Ring] y) =
      D.serreForm Coefficients.q pi pi_sq (undoRho D hD μ x) y := rfl

/-- A concrete functional on the actual presentation quotient at a fixed right weight. -/
def columnFunctional (μ : X) : CoveringUDot Coefficients.Ring D Coefficients.q pi →ₗ[Coefficients.Ring]
    Coefficients.Ring :=
  (columnContraction D hD μ).comp (tensorEval D hD μ)

@[simp] theorem columnFunctional_triangularTensor (μ : X)
    (x y : D.serreF Coefficients.q pi) :
    columnFunctional D hD μ (triangularTensor D Coefficients.q pi μ (x ⊗ₜ[Coefficients.Ring] y)) =
      D.serreForm Coefficients.q pi pi_sq (undoRho D hD μ x) y := by
  simp [columnFunctional]

/-- Actual normalization on every pair of positive half words, including unequal lengths. -/
theorem columnFunctional_rho_halfWord (μ : X) (a b : List I) :
    columnFunctional D hD μ
      ((rho D Coefficients.q pi pi_sq (halfWord D Coefficients.q pi true a μ)).unop *
        halfWord D Coefficients.q pi true b μ) =
      D.form Coefficients.q pi (monomial Coefficients.Ring a) (monomial Coefficients.Ring b) := by
  obtain ⟨c, hc⟩ := rho_halfWord_unit D Coefficients.q pi pi_sq true a μ
  simp only [Bool.not_true] at hc
  by_cases hw : halfWeight D true (wordWeight a) = halfWeight D true (wordWeight b)
  · rw [hc, smul_mul_assoc]
    have hn : halfWord D Coefficients.q pi false a.reverse (μ + halfWeight D true (wordWeight a)) *
        halfWord D Coefficients.q pi true b μ = normalWord D Coefficients.q pi a.reverse b μ := by
      rw [hw]; rfl
    rw [hn, ← triangularTensor_monomial, ← map_smul, TensorProduct.smul_tmul',
      columnFunctional_triangularTensor, undoRho_of_rho_word D hD μ a c hc,
      SuperCartanDatum.serreForm_toSerreF]
  · have hb := halfWord_mem_block D Coefficients.q pi true b μ
    have ha := rho_mem_block D Coefficients.q pi pi_sq
      (halfWord_mem_block D Coefficients.q pi true a μ)
    rw [mul_eq_zero_of_mem_block D Coefficients.q pi ha hb (by exact fun h ↦ hw (add_left_cancel h)), map_zero]
    symm
    exact PreF.form_eq_zero_of_ne _ _ (fun h ↦ hw (congrArg (halfWeight D true) h))
      (monomial_mem_weightSpace a) (monomial_mem_weightSpace b)

/-- All half-algebra pairs, not only homogeneous elements or words of equal length. -/
theorem columnFunctional_rho_halfMap (μ : X) (x y : D.serreF Coefficients.q pi) :
    columnFunctional D hD μ
      ((rho D Coefficients.q pi pi_sq (halfMap D Coefficients.q pi true μ x)).unop *
        halfMap D Coefficients.q pi true μ y) = D.serreForm Coefficients.q pi pi_sq x y := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi y
  induction x using induction_monomial with
  | zero => simp
  | add x z hx hz => simp only [map_add, MulOpposite.unop_add, add_mul, hx, hz, LinearMap.add_apply]
  | smul c x hx => simp only [map_smul, MulOpposite.unop_smul, smul_mul_assoc, hx, LinearMap.smul_apply]
  | word a =>
    induction y using induction_monomial with
    | zero => simp
    | add y z hy hz => simp only [map_add, mul_add, hy, hz]
    | smul c y hy => simp only [map_smul, mul_smul_comm, hy]
    | word b => rw [halfMap_monomial, halfMap_monomial, columnFunctional_rho_halfWord,
        SuperCartanDatum.serreForm_toSerreF]

end OddMath.CoveringQuantum.UDot.GenericTensor
