import OddMath.Frontier.OmissionWord

namespace OddMath.Frontier.OmissionWordControls
open OddMath.SkewPolynomial (SkewPolynomial generator)
open AllRankDivided NilCoxeterWords
noncomputable section

def step {n : ℕ} (i : Fin (n+1)) (b : Bool) (f : SkewPolynomial (n+2)) :=
  if b then divided i f else s i f

def e1 : SkewPolynomial 3 := generator 0 - generator 1 + generator 2

theorem e1_kernel : e1 ∈ OddSymmetricKernel.kernelSubring 1 := by
  intro i
  fin_cases i <;> norm_num [e1, map_add, map_sub, divided_generator, Fin.ext_iff]

theorem n2_kernel (f : SkewPolynomial 2)
    (hf : f ∈ OddSymmetricKernel.kernelSubring 0) : divided (0 : Fin 1) f = 0 := hf 0

theorem n3_reduced_010 : Reduced ([0,1,0] : Word 1) := by decide
theorem n3_reduced_101 : Reduced ([1,0,1] : Word 1) := by decide
theorem n3_longest_010 : permutation ([0,1,0] : Word 1) = LongestElementary.longest 3 := by
  ext i; fin_cases i <;> rfl
theorem n3_longest_101 : permutation ([1,0,1] : Word 1) = LongestElementary.longest 3 := by
  ext i; fin_cases i <;> rfl

theorem omission00_nonreduced : ¬Reduced ([0,0] : Word 1) := by decide
theorem omission11_nonreduced : ¬Reduced ([1,1] : Word 1) := by decide

-- All eight independent markings, for BOTH braid-related longest words.
-- The sole nonzero nontrivial marking has nonreduced omission.
theorem n3_010 (a b c : Bool) :
    step 0 a (step 1 b (step 0 c e1)) =
      if c then 0 else if b then (if a then 0 else -2) else
      if a then 0 else -e1 := by
  cases a <;> cases b <;> cases c <;>
    norm_num [step, e1, map_add, map_sub, map_neg, s_generator,
      divided_generator, divided_one, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals simp [show (2 : SkewPolynomial 3) = 1+1 by norm_num, map_add, divided_one]
  all_goals abel

theorem n3_101 (a b c : Bool) :
    step 1 a (step 0 b (step 1 c e1)) =
      if c then 0 else if b then (if a then 0 else -2) else
      if a then 0 else -e1 := by
  cases a <;> cases b <;> cases c <;>
    norm_num [step, e1, map_add, map_sub, map_neg, s_generator,
      divided_generator, divided_one, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals simp [show (2 : SkewPolynomial 3) = 1+1 by norm_num, map_add, divided_one]
  all_goals abel
-- Controls below were added AFTER production. They test exact exports and the
-- proposed termwise braid shortcut, not the truth/falsity of the full OWL.
example {n : ℕ} (w : Word n) (f g : SkewPolynomial (n+2)) :
    LongestDivided.applyWord w (f*g) = ((OmissionWord.markings w).map
      (fun m => OmissionWord.hybrid m f * LongestDivided.applyWord
        (OmissionWord.omission m) g)).sum := OmissionWord.generalized_leibniz w f g

example : OmissionWord.omission ([(0,false),(1,true),(0,false)] : OmissionWord.Marked 1) =
    [0,0] := rfl
example : (OmissionWord.markings ([0,1,0] : Word 1)).length = 8 := by decide
example (f : SkewPolynomial 3) :
    OmissionWord.hybrid [(0,true),(1,false),(0,true)] f = divided 0 (s 1 (divided 0 f)) := rfl

/-- This polynomial is deliberately NOT a joint-kernel input. -/
def braidInput : SkewPolynomial 3 := generator 0 * generator 1

theorem braid_split_left : divided (1 : Fin 2) (divided 0 (s 1 braidInput)) = 1 := by
  norm_num [braidInput, map_mul, divided_mul, divided_generator, s_generator,
    Equiv.swap_apply_def, Fin.ext_iff]

theorem braid_split_right : s (1 : Fin 2) (divided 0 (divided 1 braidInput)) = -1 := by
  norm_num [braidInput, map_mul, divided_mul, divided_generator, s_generator,
    Equiv.swap_apply_def, Fin.ext_iff]

theorem braid_split_other : divided (0 : Fin 2) (s 1 (divided 0 braidInput)) = 0 := by
  norm_num [braidInput, map_mul, divided_mul, divided_generator, s_generator,
    Equiv.swap_apply_def, Fin.ext_iff]

/-- Total braid reordering cannot be lifted to this individual marking, even up
    to sign, on arbitrary polynomials. This is NOT an OWL counterexample. -/
theorem no_termwise_braid_identification :
    ¬Signed (divided (1 : Fin 2) (divided 0 (s 1 braidInput)))
      (divided (0 : Fin 2) (s 1 (divided 0 braidInput))) := by
  rw [braid_split_left, braid_split_other]
  simp [Signed]

/-- The two summands genuinely cancel on this non-kernel control. -/
theorem braid_split_cancellation :
    divided (1 : Fin 2) (divided 0 (s 1 braidInput)) +
      s (1 : Fin 2) (divided 0 (divided 1 braidInput)) =
        divided (0 : Fin 2) (s 1 (divided 0 braidInput)) := by
  rw [braid_split_left, braid_split_right, braid_split_other, add_neg_cancel]

/-- Dropping longestness to induct on arbitrary prefixes would make OWL false. -/
theorem short_word_value :
    OmissionWord.hybrid ([(0,true),(1,false)] : OmissionWord.Marked 1) e1 = -2 := by
  norm_num [OmissionWord.hybrid, e1, map_add, map_sub, divided_generator,
    s_generator, Equiv.swap_apply_def, Fin.ext_iff]

theorem short_word_reduced : Reduced ([0,1] : Word 1) := by decide

theorem longest_hypothesis_is_essential :
    ¬OmissionWord.Trichotomy ([(0,true),(1,false)] : OmissionWord.Marked 1) := by
  intro h
  rcases h with h | h | h
  · have hz := h e1 e1_kernel
    rw [short_word_value] at hz
    rw [show (2 : SkewPolynomial 3) = 1+1 by norm_num] at hz
    have hc := congrArg (fun f : SkewPolynomial 3 => f 0) hz
    change (- (Finsupp.single (0 : Fin 3 → ℕ) (1 : ℤ) + Finsupp.single 0 1) : SkewPolynomial 3) 0 = 0 at hc
    norm_num at hc
  · have hb := h (0,true) (by simp)
    contradiction
  · exact h (by decide)

end
end OddMath.Frontier.OmissionWordControls
