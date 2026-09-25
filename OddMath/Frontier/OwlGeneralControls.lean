import OddMath.Frontier.OmissionCanonical
import OddMath.Frontier.OddSchubertAction

/-! Preproduction controls for the general OWL module, on the actual carrier.

Hand-checked facts used by the production proof of EKL arXiv:1111.1320v1,
Lemma 2.18, p. 15, for the commutation classes of the block word and of its
diagram flip:
* the canonical words in ranks three and four, and their diagram flips;
* the reversal permutation acts on generators with the global sign of the
  reversal, and the conjugated divided difference picks up that sign
  (rank three, hand computation `∂₁(φ x₀) = -1 = ε · φ(∂₀ x₀)`);
* reducedness of the small flipped words;
* one explicit distant commutation move. -/
namespace OddMath.Frontier.OwlGeneralControls
open OddMath.SkewPolynomial (SkewPolynomial generator)
open OmissionWord NilCoxeterWords AllRankDivided
noncomputable section

/-- The Lean block word at `N = 3` and `N = 4`. -/
theorem word_one : OmissionCanonical.word 1 = [1,0,1] := by decide
theorem word_two : OmissionCanonical.word 2 = [2,1,0,2,1,2] := by decide

/-- Diagram flips `i ↦ n - i` of the block word. -/
theorem flip_one : (OmissionCanonical.word 1).map Fin.rev = [0,1,0] := by decide
theorem flip_two : (OmissionCanonical.word 2).map Fin.rev = [0,1,2,0,1,0] := by decide

/-- At `N = 3` the block word and its flip are the two reduced words of `w₀`. -/
theorem flip_one_reduced : Reduced ([0,1,0] : Word 1) := by decide
theorem flip_two_reduced : Reduced ([0,1,2,0,1,0] : Word 2) := by decide
theorem nonreduced_control : ¬ Reduced ([0,0] : Word 1) := by decide

theorem flip_one_longest :
    permutation ([0,1,0] : Word 1) = LongestElementary.longest 3 := by
  ext i; fin_cases i <;> rfl

/-- The reversal of `Fin 3` is odd (it is the transposition `(0 2)`). -/
theorem epsilon_rev_three :
    SignedPermutation.epsilon (Fin.revPerm : Equiv.Perm (Fin 3)) = -1 := by decide

/-- Hand-checked generator law: `φ x₀ = -x₂` at `N = 3`. -/
theorem rev_generator_zero :
    SignedPermutation.skewAction (Fin.revPerm : Equiv.Perm (Fin 3)) (generator 0) =
      -generator 2 := by
  rw [SignedPermutation.action_generator, epsilon_rev_three]
  simp only [Fin.revPerm_apply, neg_smul, one_smul]
  rfl

theorem divided_zero_x0 : divided (0 : Fin 2) (generator (0 : Fin 3)) = 1 := by
  rw [divided_generator, if_pos (by decide)]

theorem divided_one_x2 : divided (1 : Fin 2) (generator (2 : Fin 3)) = 1 := by
  rw [divided_generator, if_pos (by decide)]

/-- Hand-checked instance of the flip conjugation `∂_{rev i} ∘ φ = ε • φ ∘ ∂_i`
(`i = 0`, `N = 3`, input `x₀`): both sides equal `-1`. -/
theorem flip_conjugation_instance :
    divided (1 : Fin 2)
        (SignedPermutation.skewAction (Fin.revPerm : Equiv.Perm (Fin 3)) (generator 0)) =
      SignedPermutation.epsilon (Fin.revPerm : Equiv.Perm (Fin 3)) •
        SignedPermutation.skewAction (Fin.revPerm : Equiv.Perm (Fin 3))
          (divided (0 : Fin 2) (generator 0)) := by
  rw [rev_generator_zero, map_neg, divided_one_x2, divided_zero_x0, map_one,
    epsilon_rev_three]
  simp

/-- One explicit distant commutation move at `N = 4`, and a non-move. -/
theorem distant_control : (0 : Fin 3).val + 1 < (2 : Fin 3).val := by decide
theorem adjacent_control : ¬ ((0 : Fin 3).val + 1 < (1 : Fin 3).val ∨
    (1 : Fin 3).val + 1 < (0 : Fin 3).val) := by decide

theorem commutation_move_permutation :
    permutation ([0,2] : Word 2) = permutation ([2,0] : Word 2) := by
  ext i; fin_cases i <;> rfl

end
end OddMath.Frontier.OwlGeneralControls
