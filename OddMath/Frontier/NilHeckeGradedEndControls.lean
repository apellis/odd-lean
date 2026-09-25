import OddMath.Frontier.NilHeckeGradedEnd

namespace OddMath.Frontier.NilHeckeGradedEndControls
open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open NilHeckeAction NilCoxeterWords OddSchubertAction NilHeckeEndomorphism NilHeckeGradedEnd
open scoped BigOperators
noncomputable section

theorem one_not_piece {N : ℕ} {d : ℤ} (hd : d ≠ 0) :
    (1 : SkewPolynomial N) ∉ polynomialPiece N d := by
  intro h
  have hz := h (0 : Fin N → ℕ) (by simpa [pdegree] using hd.symm)
  change Finsupp.single (0 : Fin N → ℕ) (1 : ℤ) 0 = 0 at hz
  norm_num at hz

theorem identity_degree (n : ℕ) : endDegree 0 (1 : rightKernelEnd n) := by
  have h := (actionEquiv_degree_iff n 1 0).mp NilHeckeGrading.unit_mem
  simpa using h

theorem identity_matrix_degree (n : ℕ) :
    matrixDegree 0 (1 : Matrix (Perm n) (Perm n) (K n)) := by
  simpa using (matrixEquiv_degree_iff n 1 0).mp (identity_degree n)

theorem rankTwo_negative : endDegree (-2) (actionEquiv 0 (crossing 0 0)) :=
  (actionEquiv_degree_iff 0 _ (-2)).mp (NilHeckeGrading.crossing_mem 0)

theorem crossing_wrong_positive : ¬endDegree 2 (actionEquiv 0 (crossing 0 0)) := by
  intro h
  have hh := h 2 (generator 0) (generator_mem 0)
  have he : (actionEquiv 0 (crossing 0 0)).val (generator 0) = 1 := by
    change action 0 (crossing 0 0) (generator 0) = 1
    simp [action_crossing, AllRankDivided.divided_generator]
  rw [he] at hh
  exact one_not_piece (by norm_num : (2:ℤ)+2 ≠ 0) hh

theorem zero_negative : polynomialPiece 2 (-2)=⊥ := polynomial_negative 2 (-2) (by norm_num)
theorem odd_zero (N : ℕ) (r : ℤ) : polynomialPiece N (2*r+1)=⊥ :=
  polynomial_odd N _ (by omega)

theorem inhomogeneous_not_pure :
    (1 + generator (0 : Fin 2)) ∉ polynomialPiece 2 2 := by
  intro h
  have hh := h 0 (by norm_num [pdegree])
  have hn : expSingle (0 : Fin 2) ≠ 0 := by
    intro he
    have := congrFun he 0
    simp [expSingle] at this
  change Finsupp.single (0 : Fin 2 → ℕ) (1 : ℤ) 0 + Finsupp.single (expSingle (0 : Fin 2)) (1 : ℤ) 0 = 0 at hh
  rw [Finsupp.single_eq_of_ne hn] at hh
  norm_num at hh

theorem inhomogeneous_inverse :
    (actionEquiv 0).symm (actionEquiv 0 (1 + dot 0 0)) = 1 + dot 0 0 :=
  (actionEquiv 0).symm_apply_apply _

def swapTwo : Perm 0 := Equiv.swap 0 1
@[simp] theorem swapTwo_length : length swapTwo=1 := by decide

def raisingMatrix : Matrix (Perm 0) (Perm 0) (K 0) :=
  fun i j => if i=swapTwo ∧ j=1 then 1 else 0

theorem raisingMatrix_degree : matrixDegree 2 raisingMatrix := by
  intro i j
  by_cases h : i=swapTwo ∧ j=1
  · rcases h with ⟨rfl,rfl⟩
    simp only [raisingMatrix, and_self, ite_true, length_one, swapTwo_length]
    change (1 : SkewPolynomial 2) ∈ polynomialPiece 2 (2+2*0-2*1)
    norm_num
    exact one_mem 2
  · simp only [raisingMatrix, if_neg h]
    exact (kernelPiece 0 _).zero_mem

theorem reversed_shift_rejected : ¬(∀ i j : Perm 0,
    raisingMatrix i j ∈ kernelPiece 0 (2+2*(length i : ℤ)-2*(length j : ℤ))) := by
  intro h
  have hh := h swapTwo 1
  simp only [raisingMatrix, and_self, ite_true, length_one, swapTwo_length] at hh
  exact one_not_piece (by norm_num : (2:ℤ)+2*1-2*0 ≠ 0) hh

theorem arbitrary_source (n : ℕ) (a : Presented n) (d : ℤ) :
    a ∈ NilHeckeGrading.degreePiece n d ↔
      ∀ e : ℤ, ∀ f : SkewPolynomial (n+2), f ∈ polynomialPiece (n+2) e →
        (actionEquiv n a).val f ∈ polynomialPiece (n+2) (e+d) :=
  actionEquiv_degree_iff n a d

theorem arbitrary_matrix (n : ℕ) (T : rightKernelEnd n) (d : ℤ) :
    endDegree d T ↔ ∀ i j : Perm n,
      matrixEquiv n T i j ∈ kernelPiece n (d+2*(length j : ℤ)-2*(length i : ℤ)) :=
  matrixEquiv_degree_iff n T d

theorem rankTwo_dot : endDegree 2 (actionEquiv 0 (dot 0 0)) :=
  (actionEquiv_degree_iff 0 _ 2).mp (NilHeckeGrading.dot_mem 0)

/-- Actual arbitrary homogeneous input, with the hypothesis stated on matrix entries. -/
theorem homogeneous_vector_consumer (n : ℕ) (d e : ℤ) (T : rightKernelEnd n)
    (hT : ∀ i j : Perm n, matrixEquiv n T i j ∈
      kernelPiece n (d+2*(length j : ℤ)-2*(length i : ℤ)))
    (f : polynomialPiece (n+2) e) :
    T.val f.val ∈ polynomialPiece (n+2) (e+d) :=
  (matrixEquiv_degree_iff n T d).mpr hT e f.val f.property

end
end OddMath.Frontier.NilHeckeGradedEndControls
