import OddMath.Frontier.EKDualBasesControls

/-! Test-first controls, compiled before EKDeterminant exists.
Same-index M in degrees 0,1,2; transpose-reindexing is a different matrix. -/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKDeterminantControls
open DegreeShapes EKDualBases EKDualBasesControls EKRadicalQuotient
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

def oneShape : DegreeShape 1 :=
  ⟨YoungDiagram.ofRowLens [1] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩

@[simp] theorem one_rows : oneShape.val.rowLens = [1] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)

theorem degree_one_shape (μ : DegreeShape 1) : μ = oneShape := by
  apply Subtype.ext
  apply YoungDiagram.equivListRowLens.injective
  apply Subtype.ext
  change μ.val.rowLens = oneShape.val.rowLens
  rw [one_rows]
  have hs := (EKIntegralBases.rowLens_sum μ.val).trans μ.property
  have hp := μ.val.pos_of_mem_rowLens
  cases he : μ.val.rowLens with
  | nil => simp [he] at hs
  | cons a t =>
    have ha := hp a (by simp [he])
    cases t with
    | nil => have h : a = 1 := by simpa [he] using hs
             simp [h]
    | cons b t =>
      have hb := hp b (by simp [he])
      simp only [he, List.sum_cons] at hs
      omega

theorem zero_matrix (μ ν : DegreeShape 0) : M 0 μ ν = 1 := by
  rw [degree_zero_shape μ, degree_zero_shape ν]
  simp [M, empty_pairing]

theorem one_matrix (μ ν : DegreeShape 1) : M 1 μ ν = 1 := by
  rw [degree_one_shape μ, degree_one_shape ν]
  have he : EKElementaryQuotient.e 1 = EKElementaryQuotient.h 1 := by
    simp [EKElementaryQuotient.e, EKElementaryQuotient.h, CompleteElementary.elementary,
      CompleteElementary.ekSign, CompleteElementary.inverseCoeff, Fin.sum_univ_succ, pow_succ]
  simpa [M, EKPartitionSpanning.ePartition, EKPartitionSpanning.hPartition, he] using degree_one

theorem row2_transpose : row2.val.transpose = col2.val := by apply YoungDiagram.ext; decide
theorem col2_transpose : col2.val.transpose = row2.val := by apply YoungDiagram.ext; decide
theorem zero_self : emptyShape.val.transpose = emptyShape.val := by apply YoungDiagram.ext; decide
theorem one_self : oneShape.val.transpose = oneShape.val := by apply YoungDiagram.ext; decide
theorem zero_ell : EKSemiorthogonality.ell emptyShape.val = 0 := by decide
theorem one_ell : EKSemiorthogonality.ell oneShape.val = 0 := by decide

theorem two_matrix :
    M 2 row2 row2 = 0 ∧ M 2 row2 col2 = 1 ∧
    M 2 col2 row2 = 1 ∧ M 2 col2 col2 = 0 :=
  ⟨degree_two_gram.1, degree_two_gram.2.1, degree_two_gram.2.2.1,
    degree_two_gram.2.2.2.1⟩

theorem two_no_self (μ : DegreeShape 2) : μ.val.transpose ≠ μ.val := by
  rcases degree_two_shapes μ with rfl | rfl
  · rw [row2_transpose]
    exact fun h => row2_ne_col2 (Subtype.ext h.symm)
  · rw [col2_transpose]
    exact fun h => row2_ne_col2 (Subtype.ext h)

theorem one_sided_matrix (μ ν : DegreeShape 2) :
    triangularMatrix 2 μ ν = if μ = ν then 1 else 0 := by
  rw [triangularMatrix_apply, quotientPairing_symm]
  rcases degree_two_shapes μ with rfl | rfl <;>
    rcases degree_two_shapes ν with rfl | rfl <;>
    simp only [row2_transpose, col2_transpose]
  all_goals change M 2 _ _ = _
  all_goals simp [two_matrix.1, two_matrix.2.1, two_matrix.2.2.1,
    two_matrix.2.2.2, row2_ne_col2, Ne.symm row2_ne_col2]

theorem raw_sign_control :
    (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℤ).det = -1 ∧
    (!![1,0;0,1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  norm_num [Matrix.det_fin_two]

end OddMath.Frontier.EKDeterminantControls
