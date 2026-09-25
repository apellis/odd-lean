import OddMath.Frontier.OmissionCanonical

/-! Controls for the direct OWL proof (compiled BEFORE `OwlDirect.lean`).
Hand-checked small cases on the actual carrier in rank N = 5 (n = 3):
the rank-five odd elementary inputs e₁, e₃ lie in the actual joint kernel, one
signed-permutation value, a one-step divided value, and the finite word facts
used later. Every expected value was first hand/independently computed
(an unpublished script). Controls only: nothing here is an OWL claim. -/
namespace OddMath.Frontier.OwlDirectControls
open OddMath.SkewPolynomial (SkewPolynomial generator)
open AllRankDivided NilCoxeterWords
noncomputable section

local notation "x" => (generator : Fin 5 → SkewPolynomial 5)

/-- Odd elementary e₁ in rank five, increasing-index order, sign (-1)^j. -/
def e1 : SkewPolynomial 5 := x 0 - x 1 + x 2 - x 3 + x 4

/-- Odd elementary e₃ in rank five: ∑_{a<b<c} (-1)^{a+b+c} x_a x_b x_c. -/
def e3 : SkewPolynomial 5 :=
  - x 0 * x 1 * x 2 + x 0 * x 1 * x 3 - x 0 * x 1 * x 4 - x 0 * x 2 * x 3
  + x 0 * x 2 * x 4 - x 0 * x 3 * x 4 + x 1 * x 2 * x 3 - x 1 * x 2 * x 4
  + x 1 * x 3 * x 4 - x 2 * x 3 * x 4

/-- Expansion by the actual laws only: additivity, the signed generator action,
the twisted Leibniz rule and divided values on generators; literal indices are
decided. No normal-form or anticommutation step is hidden here. -/
macro "owl_expand" : tactic => `(tactic| (
  simp (config := {decide := true}) only [map_add, map_sub, map_neg, map_mul, map_one,
    divided_mul, divided_generator, divided_one, s_generator, Equiv.swap_apply_def,
    Fin.reduceSucc, Fin.reduceCastSucc, Fin.isValue, ite_true, ite_false, true_or, or_true,
    false_or, or_false, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, neg_mul,
    mul_neg, neg_neg, mul_assoc, sub_eq_add_neg, neg_add_rev, neg_zero, add_mul, mul_add]))

theorem kernel_of (f : SkewPolynomial 5) (h0 : divided (0 : Fin 4) f = 0)
    (h1 : divided (1 : Fin 4) f = 0) (h2 : divided (2 : Fin 4) f = 0)
    (h3 : divided (3 : Fin 4) f = 0) : f ∈ OddSymmetricKernel.kernelSubring 3 := by
  intro i; fin_cases i
  exacts [h0, h1, h2, h3]

theorem e1_kernel : e1 ∈ OddSymmetricKernel.kernelSubring 3 := by
  apply kernel_of <;> (simp only [e1]; owl_expand) <;> abel

theorem e3_kernel : e3 ∈ OddSymmetricKernel.kernelSubring 3 := by
  apply kernel_of <;> (simp only [e3]; owl_expand) <;> abel

/-- Hand-checked: the all-false suffix [0,3,2,1] sends e₁ to x0+x1-x2+x3-x4. -/
theorem suffix_e1 :
    OmissionWord.hybrid ([(0,false),(3,false),(2,false),(1,false)] : OmissionWord.Marked 3) e1 =
      x 0 + x 1 - x 2 + x 3 - x 4 := by
  simp only [OmissionWord.hybrid, Bool.false_eq_true, if_false, e1]
  owl_expand
  abel

/-- Hand-checked: the nonadjacent pulled-back pair (1,4) gives ∂₁(σ e₁) = (+1) + (-1) = 0
(labels of opposite parity), matching the Python value {}. -/
theorem one_divided_step :
    OmissionWord.hybrid ([(1,true),(0,false),(3,false),(2,false),(1,false)] :
      OmissionWord.Marked 3) e1 = 0 := by
  simp only [OmissionWord.hybrid, Bool.false_eq_true, if_false, if_true, e1]
  owl_expand
  abel

/-- The (later) witness word is reduced and is a word for the actual longest element. -/
theorem witness_word_reduced : Reduced ([0,1,0,3,2,1,0,3,2,1] : Word 3) := by decide

theorem witness_word_longest :
    permutation ([0,1,0,3,2,1,0,3,2,1] : Word 3) = LongestElementary.longest 5 := by
  ext i; fin_cases i <;> rfl

theorem omission_reduced : Reduced ([0,1,0,3,2,1] : Word 3) := by decide

/-- Nonreduced control: the omission test must detect [0,0]. -/
theorem omission_nonreduced : ¬Reduced ([0,0] : Word 3) := by decide

end
end OddMath.Frontier.OwlDirectControls
