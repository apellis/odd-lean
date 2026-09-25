import OddMath.Frontier.EKDeterminantControls

/-!
# Literal EK1107.5610v2 equation (3.4) fails in degree two

Same exhaustive index on both sides of actual EKDualBases.M.
No corrected all-degree determinant formula is asserted. The first invalid
source inference is cancellation of equal anti-diagonal entries without
retaining the sign of the transpose permutation. Simultaneous reindexing
cannot remove the discrepancy. Controls compiled before this production file.
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKDeterminant
open DegreeShapes EKDualBases EKDualBasesControls EKDeterminantControls
local instance : DecidableEq YoungDiagram := Classical.decEq _
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-- Frozen literal RHS of printed (3.4), not a repaired sign formula. -/
def sourceRHS (d : ℕ) : ℤ :=
  ∏ μ ∈ Finset.univ.filter (fun μ : DegreeShape d => μ.val.transpose = μ.val),
    (-1 : ℤ)^EKSemiorthogonality.ell μ.val

/-- Exhaustive enumeration, proved onto the actual degree index. -/
def degreeTwoEquiv : Fin 2 ≃ DegreeShape 2 where
  toFun i := if i = 0 then row2 else col2
  invFun μ := if μ = row2 then 0 else 1
  left_inv i := by fin_cases i <;> simp [row2_ne_col2, Ne.symm row2_ne_col2]
  right_inv μ := by rcases degree_two_shapes μ with rfl | rfl <;>
                     simp [row2_ne_col2, Ne.symm row2_ne_col2]

/-- Same enumeration for rows AND columns: this is M itself up to conjugate reindexing. -/
theorem degree_two_matrix :
    (M 2).submatrix degreeTwoEquiv degreeTwoEquiv =
      (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix, degreeTwoEquiv, two_matrix.1, two_matrix.2.1,
      two_matrix.2.2.1, two_matrix.2.2.2]

/-- Exact determinant in the exhaustive degree index, not a surrogate. -/
theorem degree_two_det : (M 2).det = -1 := by
  rw [← Matrix.det_submatrix_equiv_self degreeTwoEquiv, degree_two_matrix]
  norm_num [Matrix.det_fin_two]

/-- There are no self-transpose diagrams of size two. -/
theorem degree_two_filter :
    Finset.univ.filter (fun μ : DegreeShape 2 => μ.val.transpose = μ.val) = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro μ h
  exact two_no_self μ (Finset.mem_filter.mp h).2

theorem degree_two_rhs : sourceRHS 2 = 1 := by
  simp [sourceRHS, degree_two_filter]

/-- Decisive literal-source refutation. -/
theorem equation_3_4_counterexample : (M 2).det ≠ sourceRHS 2 := by
  rw [degree_two_det, degree_two_rhs]
  norm_num

theorem equation_3_4_not_all_degrees : ¬ ∀ d : ℕ, (M d).det = sourceRHS d := by
  intro h
  exact equation_3_4_counterexample (h 2)

/-- Ordinary common ordering choices cannot affect the determinant, at ANY degree. -/
theorem simultaneous_reindex_invariant (d : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ DegreeShape d) : ((M d).submatrix e e).det = (M d).det :=
  Matrix.det_submatrix_equiv_self e (M d)

/-- The discrepancy survives every common row/column enumeration. -/
theorem counterexample_under_every_order {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ DegreeShape 2) :
    ((M 2).submatrix e e).det = -1 ∧
    ((M 2).submatrix e e).det ≠ sourceRHS 2 := by
  rw [simultaneous_reindex_invariant]
  exact ⟨degree_two_det, equation_3_4_counterexample⟩

/-- A one-sided transpose change really does change the determinant. -/
theorem degree_two_triangular_det : (triangularMatrix 2).det = 1 := by
  have h : triangularMatrix 2 = 1 := by
    ext μ ν
    simpa only [Matrix.one_apply] using one_sided_matrix μ ν
  rw [h, Matrix.det_one]

theorem one_sided_not_M_det : (triangularMatrix 2).det ≠ (M 2).det := by
  rw [degree_two_triangular_det, degree_two_det]
  norm_num

/-- Zero and one are agreement controls, not excluded by the target. -/
theorem degree_zero_control : (M 0).det = 1 ∧ sourceRHS 0 = 1 := by
  letI : Unique (DegreeShape 0) := ⟨⟨emptyShape⟩, degree_zero_shape⟩
  constructor
  · rw [Matrix.det_unique]; exact zero_matrix _ _
  · apply Finset.prod_eq_one
    intro μ _
    rw [degree_zero_shape μ, zero_ell, pow_zero]

theorem degree_one_control : (M 1).det = 1 ∧ sourceRHS 1 = 1 := by
  letI : Unique (DegreeShape 1) := ⟨⟨oneShape⟩, degree_one_shape⟩
  constructor
  · rw [Matrix.det_unique]; exact one_matrix _ _
  · apply Finset.prod_eq_one
    intro μ _
    rw [degree_one_shape μ, one_ell, pow_zero]

end OddMath.Frontier.EKDeterminant
