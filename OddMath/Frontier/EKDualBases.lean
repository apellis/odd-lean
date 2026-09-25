import OddMath.Frontier.EKIntegralBases
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Determinant

/-! EK1107.5610v2 §3.1, integral q=-1 only. The restricted form is the
inherited quotient form, not a new dot product. Unimodularity is proved
from Prop2.14 before dual vectors are constructed. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace OddMath.Frontier.EKDualBases
open EKRadicalQuotient EKIntegralBases DegreeShapes
open EKPartitionSpanning (hPartition ePartition)
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-- The exact orientation x ↦ (y ↦ (y,x)). -/
def pairingMap (d : ℕ) : degreePiece d →ₗ[ℤ] Module.Dual ℤ (degreePiece d) where
  toFun x :=
    { toFun := fun y => quotientPairing y.val x.val
      map_add' := by intros; simp
      map_smul' := by intros; simp only [Submodule.coe_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  map_add' := by intros; ext y; simp
  map_smul' := by
    intros; ext y
    simp only [Submodule.coe_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply]
    rfl

@[simp] theorem pairingMap_apply (d : ℕ) (x y : degreePiece d) :
    pairingMap d x y = quotientPairing y.val x.val := rfl

/-- Conjugation permutes the exhaustive degree-d partition index. -/
def transposeShape (d : ℕ) : DegreeShape d ≃ DegreeShape d where
  toFun μ := ⟨μ.val.transpose, by simpa [YoungDiagram.card, YoungDiagram.transpose] using μ.property⟩
  invFun μ := ⟨μ.val.transpose, by simpa [YoungDiagram.card, YoungDiagram.transpose] using μ.property⟩
  left_inv μ := by apply Subtype.ext; simp
  right_inv μ := by apply Subtype.ext; simp

def transposeEBasis (d : ℕ) : Basis (DegreeShape d) ℤ (degreePiece d) :=
  (degreeEBasis d).reindex (transposeShape d)

@[simp] theorem transposeEBasis_apply (d : ℕ) (μ : DegreeShape d) :
    (transposeEBasis d μ : Q) = ePartition μ.val.transpose := by
  simp [transposeEBasis, transposeShape]

def triangularMatrix (d : ℕ) : Matrix (DegreeShape d) (DegreeShape d) ℤ :=
  LinearMap.toMatrix (transposeEBasis d) (degreeHBasis d).dualBasis (pairingMap d)

@[simp] theorem triangularMatrix_apply (d : ℕ) (μ ν : DegreeShape d) :
    triangularMatrix d μ ν = quotientPairing (hPartition μ.val) (ePartition ν.val.transpose) := by
  simp [triangularMatrix, LinearMap.toMatrix_apply]

/-- The source signed diagonal is a unit of Z, not merely nonzero. -/
theorem triangularMatrix_diag (d : ℕ) (μ : DegreeShape d) :
    triangularMatrix d μ μ = (-1 : ℤ)^EKSemiorthogonality.ell μ.val :=
  by
    rw [triangularMatrix_apply]
    exact EKSemiorthogonality.proposition_2_14_diagonal μ.val

private theorem transpose_rows_injective (d : ℕ) :
    Function.Injective (fun μ : DegreeShape d => μ.val.transpose.rowLens) := by
  intro μ ν h
  apply Subtype.ext
  apply YoungDiagram.transpose_eq_iff.mp
  apply YoungDiagram.equivListRowLens.injective
  exact Subtype.ext h

/-- Integral unimodularity, using the mixed semiorthogonality and unit diagonal. -/
theorem triangularMatrix_det_unit (d : ℕ) : IsUnit (triangularMatrix d).det := by
  letI : LinearOrder (DegreeShape d) := LinearOrder.lift'
    (fun μ : DegreeShape d => μ.val.transpose.rowLens) (transpose_rows_injective d)
  have ht : (triangularMatrix d).BlockTriangular OrderDual.toDual := by
    intro μ ν hlt
    change μ.val.transpose.rowLens < ν.val.transpose.rowLens at hlt
    rw [triangularMatrix_apply]
    exact (EKSemiorthogonality.proposition_2_14_vanishing μ.val ν.val.transpose.rowLens
      ν.val.transpose.pos_of_mem_rowLens hlt).1
  rw [Matrix.det_of_lowerTriangular _ ht]
  apply IsUnit.prod_iff.mpr
  intro μ _
  rw [triangularMatrix_diag]
  exact (isUnit_one.neg : IsUnit (-1 : ℤ)).pow _

/-- Inverse is integral because the mixed determinant is a unit. -/
def pairingInverse (d : ℕ) : Module.Dual ℤ (degreePiece d) →ₗ[ℤ] degreePiece d :=
  Matrix.toLin (degreeHBasis d).dualBasis (transposeEBasis d) (triangularMatrix d)⁻¹

theorem pairingInverse_left (d : ℕ) :
    (pairingInverse d).comp (pairingMap d) = LinearMap.id := by
  apply (LinearMap.toMatrix (transposeEBasis d) (transposeEBasis d)).injective
  rw [LinearMap.toMatrix_comp (transposeEBasis d) (degreeHBasis d).dualBasis]
  simp only [pairingInverse, LinearMap.toMatrix_toLin, LinearMap.toMatrix_id]
  exact Matrix.nonsing_inv_mul _ (triangularMatrix_det_unit d)

theorem pairingInverse_right (d : ℕ) :
    (pairingMap d).comp (pairingInverse d) = LinearMap.id := by
  apply (LinearMap.toMatrix (degreeHBasis d).dualBasis (degreeHBasis d).dualBasis).injective
  rw [LinearMap.toMatrix_comp (degreeHBasis d).dualBasis (transposeEBasis d)]
  simp only [pairingInverse, LinearMap.toMatrix_toLin, LinearMap.toMatrix_id]
  exact Matrix.mul_nonsing_inv _ (triangularMatrix_det_unit d)

/-- Perfectness over Z of the actual homogeneous quotient pairing, all d including zero. -/
def pairingEquiv (d : ℕ) : degreePiece d ≃ₗ[ℤ] Module.Dual ℤ (degreePiece d) :=
  LinearEquiv.ofLinear (pairingMap d) (pairingInverse d)
    (pairingInverse_right d) (pairingInverse_left d)

@[simp] theorem pairingEquiv_apply (d : ℕ) (x y : degreePiece d) :
    pairingEquiv d x y = quotientPairing y.val x.val := rfl

/-- Every integral functional has exactly one representing element. -/
theorem unique_representative (d : ℕ) (l : Module.Dual ℤ (degreePiece d)) :
    ∃! x : degreePiece d, ∀ y : degreePiece d, quotientPairing y.val x.val = l y := by
  refine ⟨(pairingEquiv d).symm l, ?_, ?_⟩
  · intro y
    exact congrArg (fun f : Module.Dual ℤ (degreePiece d) => f y)
      ((pairingEquiv d).apply_symm_apply l)
  · intro x hx
    apply (pairingEquiv d).injective
    ext y
    exact (hx y).trans (congrArg (fun f : Module.Dual ℤ (degreePiece d) => f y)
      ((pairingEquiv d).apply_symm_apply l)).symm

/-- The odd monomial basis, INSIDE the actual homogeneous piece. -/
def mBasis (d : ℕ) : Basis (DegreeShape d) ℤ (degreePiece d) :=
  (degreeHBasis d).dualBasis.map (pairingEquiv d).symm

/-- The odd forgotten basis, INSIDE the same homogeneous piece. -/
def fBasis (d : ℕ) : Basis (DegreeShape d) ℤ (degreePiece d) :=
  (degreeEBasis d).dualBasis.map (pairingEquiv d).symm

@[simp] theorem h_m (d : ℕ) (ν μ : DegreeShape d) :
    quotientPairing (hPartition ν.val) (mBasis d μ).val = if ν = μ then 1 else 0 := by
  have he := congrArg (fun f : Module.Dual ℤ (degreePiece d) => f (degreeHBasis d ν))
    ((pairingEquiv d).apply_symm_apply ((degreeHBasis d).dualBasis μ))
  simpa only [mBasis, Basis.map_apply, pairingEquiv_apply, degreeHBasis_apply,
    Basis.dualBasis_apply_self] using he

@[simp] theorem e_f (d : ℕ) (ν μ : DegreeShape d) :
    quotientPairing (ePartition ν.val) (fBasis d μ).val = if ν = μ then 1 else 0 := by
  have he := congrArg (fun f : Module.Dual ℤ (degreePiece d) => f (degreeEBasis d ν))
    ((pairingEquiv d).apply_symm_apply ((degreeEBasis d).dualBasis μ))
  simpa only [fBasis, Basis.map_apply, pairingEquiv_apply, degreeEBasis_apply,
    Basis.dualBasis_apply_self] using he

/-- Genuine arbitrary-element consumers: coordinates are the source pairings. -/
@[simp] theorem m_coordinates (d : ℕ) (x : degreePiece d) (μ : DegreeShape d) :
    (mBasis d).repr x μ = quotientPairing (hPartition μ.val) x.val := by
  simp [mBasis, Basis.map_repr]

@[simp] theorem f_coordinates (d : ℕ) (x : degreePiece d) (μ : DegreeShape d) :
    (fBasis d).repr x μ = quotientPairing (ePartition μ.val) x.val := by
  simp [fBasis, Basis.map_repr]

theorem reconstruct_m (d : ℕ) (x : degreePiece d) :
    x = ∑ μ, quotientPairing (hPartition μ.val) x.val • mBasis d μ := by
  simpa only [m_coordinates] using ((mBasis d).sum_repr x).symm

theorem reconstruct_f (d : ℕ) (x : degreePiece d) :
    x = ∑ μ, quotientPairing (ePartition μ.val) x.val • fBasis d μ := by
  simpa only [f_coordinates] using ((fBasis d).sum_repr x).symm

/-- Uniqueness needs only the defining h-pairings on all degree-d partitions. -/
theorem m_unique (d : ℕ) (μ : DegreeShape d) (x : degreePiece d)
    (hx : ∀ ν, quotientPairing (hPartition ν.val) x.val = if ν = μ then 1 else 0) :
    x = mBasis d μ := by
  apply (mBasis d).repr.injective
  ext ν
  rw [m_coordinates, m_coordinates, hx, h_m]

theorem f_unique (d : ℕ) (μ : DegreeShape d) (x : degreePiece d)
    (hx : ∀ ν, quotientPairing (ePartition ν.val) x.val = if ν = μ then 1 else 0) :
    x = fBasis d μ := by
  apply (fBasis d).repr.injective
  ext ν
  rw [f_coordinates, f_coordinates, hx, e_f]

/-- Literal coefficients (3.2), with source row/column order. -/
def M (d : ℕ) : Matrix (DegreeShape d) (DegreeShape d) ℤ :=
  fun ν μ => quotientPairing (ePartition ν.val) (hPartition μ.val)
def Mh (d : ℕ) : Matrix (DegreeShape d) (DegreeShape d) ℤ :=
  fun ν μ => quotientPairing (hPartition ν.val) (hPartition μ.val)
def Me (d : ℕ) : Matrix (DegreeShape d) (DegreeShape d) ℤ :=
  fun ν μ => quotientPairing (ePartition ν.val) (ePartition μ.val)

/-- Flipping BOTH constant colors changes neither admissibility nor cable signs.
This extra fact, not symmetry of the form alone, justifies M = Mᵀ. -/
theorem mixed_color_flip (ν μ : YoungDiagram) :
    quotientPairing (ePartition ν) (hPartition μ) =
      quotientPairing (hPartition ν) (ePartition μ) := by
  change quotientPairing (EKSemiorthogonality.ePartition ν) (EKSemiorthogonality.hPartition μ) =
    quotientPairing (EKSemiorthogonality.hPartition ν) (EKSemiorthogonality.ePartition μ)
  rw [EKSemiorthogonality.hPartition_eq_mixed, EKSemiorthogonality.ePartition_eq_mixed,
    EKSemiorthogonality.hPartition_eq_mixed, EKSemiorthogonality.ePartition_eq_mixed,
    EKMixedPairing.quotientPairing_eq_matrixSum, EKMixedPairing.quotientPairing_eq_matrixSum]
  simp [EKMixedPairing.matrixSum, EKMixedPairing.matrixWeight, EKMixedPairing.cell]

theorem M_symm (d : ℕ) (ν μ : DegreeShape d) : M d ν μ = M d μ ν := by
  unfold M
  rw [mixed_color_flip, quotientPairing_symm]
theorem Mh_symm (d : ℕ) (ν μ : DegreeShape d) : Mh d ν μ = Mh d μ ν :=
  quotientPairing_symm _ _
theorem Me_symm (d : ℕ) (ν μ : DegreeShape d) : Me d ν μ = Me d μ ν :=
  quotientPairing_symm _ _

/-- All four literal finite expansions (3.3). -/
theorem h_eq_M_f (d : ℕ) (ν : DegreeShape d) :
    degreeHBasis d ν = ∑ μ, M d ν μ • fBasis d μ := by
  rw [reconstruct_f d (degreeHBasis d ν)]
  apply Finset.sum_congr rfl
  intro μ _
  rw [degreeHBasis_apply]
  exact congrArg (fun z : ℤ => z • fBasis d μ) (M_symm d μ ν)
theorem h_eq_Mh_m (d : ℕ) (ν : DegreeShape d) :
    degreeHBasis d ν = ∑ μ, Mh d ν μ • mBasis d μ := by
  simpa only [degreeHBasis_apply, Mh, quotientPairing_symm] using reconstruct_m d (degreeHBasis d ν)
theorem e_eq_M_m (d : ℕ) (ν : DegreeShape d) :
    degreeEBasis d ν = ∑ μ, M d ν μ • mBasis d μ := by
  simpa only [degreeEBasis_apply, quotientPairing_symm, M] using reconstruct_m d (degreeEBasis d ν)
theorem e_eq_Me_f (d : ℕ) (ν : DegreeShape d) :
    degreeEBasis d ν = ∑ μ, Me d ν μ • fBasis d μ := by
  simpa only [degreeEBasis_apply, Me, quotientPairing_symm] using reconstruct_f d (degreeEBasis d ν)

/-- Determinant units are consequences of the proved integral equivalence. -/
theorem M_det_unit (d : ℕ) : IsUnit (M d).det := by
  have he : LinearMap.toMatrix (degreeHBasis d) (degreeEBasis d).dualBasis
      (pairingEquiv d).toLinearMap = M d := by
    ext ν μ
    simp [LinearMap.toMatrix_apply, M]
  rw [← he]
  exact (pairingEquiv d).isUnit_det _ _
theorem Mh_det_unit (d : ℕ) : IsUnit (Mh d).det := by
  have he : LinearMap.toMatrix (degreeHBasis d) (degreeHBasis d).dualBasis
      (pairingEquiv d).toLinearMap = Mh d := by
    ext ν μ
    simp [LinearMap.toMatrix_apply, Mh]
  rw [← he]
  exact (pairingEquiv d).isUnit_det _ _
theorem Me_det_unit (d : ℕ) : IsUnit (Me d).det := by
  have he : LinearMap.toMatrix (degreeEBasis d) (degreeEBasis d).dualBasis
      (pairingEquiv d).toLinearMap = Me d := by
    ext ν μ
    simp [LinearMap.toMatrix_apply, Me]
  rw [← he]
  exact (pairingEquiv d).isUnit_det _ _

open EKPairingMatrices (Mat Raw crossing)
open EKSemiorthogonality (rows)

/-- Literal finite set of 0/1 matrices with row sums ν and column sums μ.
Natural entries bounded by one are exactly the integers 0 and 1. -/
def ZeroOneMatrices (ν μ : YoungDiagram) :=
  {A : Mat (rows ν) (rows μ) // ∀ i j, A i j ≤ 1}

instance (ν μ : YoungDiagram) : Fintype (ZeroOneMatrices ν μ) := by
  classical
  unfold ZeroOneMatrices
  infer_instance

/-- The Me-only internal cable exponent from the printed Proposition 3.1. -/
def cable {r c : ℕ} (A : Raw r c) : ℕ := ∑ i, ∑ j, (A i j).choose 2

/-- Crossing is SW–NE: i<k (north/south), l<j (west/east). -/
theorem crossing_source {r c : ℕ} (A : Raw r c) :
    crossing A = ∑ i, ∑ k, if i < k then
      ∑ j, ∑ l, if l < j then A i j * A k l else 0 else 0 := rfl

/-- Source transpose convention: changing which platforms are rows preserves
SW–NE crossings. This is the inherited genuine four-index transpose identity. -/
theorem crossing_source_transpose {r c : ℕ} (A : Raw r c) :
    crossing (EKPairingMatrices.transpose A) = crossing A :=
  EKPairingMatrices.crossing_transpose A

theorem cable_transpose {r c : ℕ} (A : Raw r c) :
    cable (EKPairingMatrices.transpose A) = cable A := by
  unfold cable EKPairingMatrices.transpose
  exact Finset.sum_comm

/-- The first formula of Prop3.1: M is the signed 0/1 margin-matrix sum. -/
theorem proposition_3_1_M (d : ℕ) (ν μ : DegreeShape d) :
    M d ν μ = ∑ A : ZeroOneMatrices ν.val μ.val, (-1 : ℤ)^crossing A.val := by
  change quotientPairing (EKSemiorthogonality.ePartition ν.val)
    (EKSemiorthogonality.hPartition μ.val) = _
  rw [EKSemiorthogonality.ePartition_eq_mixed, EKSemiorthogonality.hPartition_eq_mixed,
    EKMixedPairing.quotientPairing_eq_restricted_matrices]
  let e : EKMixedPairing.MixedMatrices (rows ν.val) (fun _ => true)
      (rows μ.val) (fun _ => false) ≃ ZeroOneMatrices ν.val μ.val :=
    Equiv.subtypeEquivRight (fun _ => by simp [EKMixedPairing.Admissible])
  apply Fintype.sum_equiv e
  intro A
  simp only [EKMixedPairing.blackPairs, Bool.true_and, Bool.false_eq_true, if_false,
    Finset.sum_const_zero, add_zero]
  rfl

/-- The second formula: all natural matrices, no entry restriction or cable sign. -/
theorem proposition_3_1_Mh (d : ℕ) (ν μ : DegreeShape d) :
    Mh d ν μ = ∑ A : Mat (rows ν.val) (rows μ.val), (-1 : ℤ)^crossing A := by
  change quotientPairing (EKSemiorthogonality.hPartition ν.val)
    (EKSemiorthogonality.hPartition μ.val) = _
  rw [EKSemiorthogonality.hPartition_eq_mixed, EKSemiorthogonality.hPartition_eq_mixed,
    EKMixedPairing.quotientPairing_eq_matrixSum]
  simp [EKMixedPairing.matrixSum, EKMixedPairing.matrixWeight, EKMixedPairing.cell]

/-- The third formula: all natural matrices and precisely the additional
sum of choose(entry,2) internal cable crossings. -/
theorem proposition_3_1_Me (d : ℕ) (ν μ : DegreeShape d) :
    Me d ν μ = ∑ A : Mat (rows ν.val) (rows μ.val),
      (-1 : ℤ)^(crossing A + ∑ i, ∑ j, (A i j).choose 2) := by
  change quotientPairing (EKSemiorthogonality.ePartition ν.val)
    (EKSemiorthogonality.ePartition μ.val) = _
  rw [EKSemiorthogonality.ePartition_eq_mixed, EKSemiorthogonality.ePartition_eq_mixed,
    EKMixedPairing.quotientPairing_eq_matrixSum]
  simp [EKMixedPairing.matrixSum, EKMixedPairing.matrixWeight, EKMixedPairing.cell,
    Finset.prod_pow_eq_pow_sum, pow_add]

end OddMath.Frontier.EKDualBases
