import OddMath.Frontier.NilHeckeRightBasis

/-! Hand-derived controls written before the RIGHT-basis implementation.
In rank two, d(x₀*x₀)=x₀-x₁, whereas x₀*d(x₀)=x₀.
Thus LEFT and RIGHT differ already on the nonconstant input x₀.
Reversing [0,1] must invert its permutation, not leave it fixed. -/
namespace OddMath.Frontier.NilHeckeRightBasisControls
open NilHeckeAction NilCoxeterWords AllRankDivided
open OddMath.SkewPolynomial (SkewPolynomial generator)
noncomputable section

theorem left_nonconstant :
    action 0 (dot 0 0 * crossing 0 0) (generator 0) = generator 0 := by
  rw [action_mul_apply, action_crossing_apply, divided_generator]
  simp [action_dot_apply]

theorem right_nonconstant :
    action 0 (crossing 0 0 * dot 0 0) (generator 0) = generator 0 - generator 1 := by
  rw [action_mul_apply, action_dot_apply, action_crossing_apply]
  have h := divided_left_mul (n := 0) 0 (generator 0)
  simpa [divided_generator] using h

theorem left_ne_right_nonconstant :
    action 0 (dot 0 0 * crossing 0 0) (generator 0) ≠
      action 0 (crossing 0 0 * dot 0 0) (generator 0) := by
  rw [left_nonconstant, right_nonconstant]
  intro h
  have hz : (generator 1 : SkewPolynomial 2) = 0 := by
    exact (sub_eq_self.mp h.symm)
  exact generator_ne_zero 0 1 hz

theorem empty_crossing_word : product ([] : Word 0) = 1 := rfl

theorem empty_dot_word : NilHeckeBasis.dotWord ([] : List (Fin 2)) = 1 := rfl

theorem rankTwo_square : product ([0,0] : Word 0) = 0 := by
  simp [product, crossing_square]

theorem non_self_inverse :
    permutation ([0,1] : Word 1) ≠ (permutation ([0,1] : Word 1))⁻¹ := by decide

theorem reversed_cycle :
    permutation ([1,0] : Word 1) = (permutation ([0,1] : Word 1))⁻¹ := by decide

theorem reverse_distant_sign : product ([2,0] : Word 2) = -product ([0,2] : Word 2) := by
  simpa [product] using crossing_distant (n := 2) 2 0 (by decide)

/-! The following target consumers were added AFTER the full production proof
passed. The hand-derived controls above were checked before its implementation. -/

theorem right_basis_literal (n : ℕ) (A : Fin (n+2) → ℕ) (w : Perm n) :
    NilHeckeRightBasis.basis n (A,w) = dividedElement w * NilHeckeBasis.dotMonomial A := by
  rw [NilHeckeRightBasis.basis_apply]
  rfl

theorem right_action_literal (n : ℕ) (A : Fin (n+2) → ℕ) (w : Perm n)
    (f : SkewPolynomial (n+2)) :
    action n (NilHeckeRightBasis.basis n (A,w)) f =
      dividedElementOperator w (OddMath.SkewPolynomial.monomial A 1 * f) := by
  rw [NilHeckeRightBasis.basis_apply, NilHeckeRightBasis.action_rightBasisElement_apply]

theorem integral_coordinates (n : ℕ) (x : Presented n) :
    ∃! c : ((Fin (n+2) → ℕ) × Perm n) →₀ ℤ,
      c.sum (fun i a => a • (dividedElement i.2 * NilHeckeBasis.dotMonomial i.1)) = x :=
  NilHeckeRightBasis.existsUnique_expansion x

theorem reversed_cycle_product :
    NilHeckeRightBasis.reverseLinear 1 (product ([0,1] : Word 1)) = product [1,0] := by
  exact NilHeckeRightBasis.reverse_product _

theorem reversed_ordered_dots :
    NilHeckeRightBasis.reverseLinear 0 (NilHeckeBasis.dotMonomial (n := 0) ![1,1]) =
      -(NilHeckeBasis.dotMonomial (n := 0) ![1,1]) := by
  have hm : NilHeckeBasis.dotMonomial (n := 0) ![1,1] = dot 0 0 * dot 0 1 := by
    simp [NilHeckeBasis.dotMonomial, List.finRange_succ]
  rw [hm, NilHeckeRightBasis.reverse_mul, NilHeckeRightBasis.reverse_dot,
    NilHeckeRightBasis.reverse_dot]
  exact eq_neg_iff_add_eq_zero.mpr (NilHeckeBasis.dots_anticommute (n := 0) 1 0 (by decide))

theorem reverse_empty_rankTwo : NilHeckeRightBasis.reverseLinear 0 (product ([] : Word 0)) = 1 := by
  simp [product]

theorem rankTwo_all_coordinates (x : Presented 0) :
    ∃! c : ((Fin 2 → ℕ) × Perm 0) →₀ ℤ,
      c.sum (fun i a => a • NilHeckeRightBasis.rightBasisElement i) = x :=
  NilHeckeRightBasis.existsUnique_expansion x

theorem general_operator_independence (n : ℕ) :
    LinearIndependent ℤ (@NilHeckeRightBasis.rightOperator n) :=
  NilHeckeRightBasis.rightOperator_linearIndependent n

end
end OddMath.Frontier.NilHeckeRightBasisControls
