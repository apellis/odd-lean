import OddMath.Frontier.OmissionCanonical

/-! # The literal arbitrary-word Omission Word Lemma is false (rank five)

EKL arXiv:1111.1320v1, p.15, Lemma 2.18 (OWL): "Suppose w is a reduced expression
for w0. For any ξ as above, either (1) w^ξ · f = 0 for all f ∈ OΛa, (2) ξ(j) = 0
for all j = 1, . . . , r, or (3) the omission word w^ξ_om is non-reduced."

On the actual existing carrier and vocabulary (`OmissionWord.Marked`, FALSE =
actual signed simple action `s i`, TRUE = actual `AllRankDivided.divided i`,
rightmost acts first, `OmissionWord.Trichotomy` is the literal predicate, the
kernel is the actual joint kernel `OddSymmetricKernel.kernelSubring`), we exhibit,
in rank N = 5 (n = 3), the reduced word w = [0,1,0,3,2,1,0,3,2,1] of the actual
longest element and the marking

  ξ = F F T T T T F F F F   (positions left to right),

whose omission word [0,1,0,3,2,1] is reduced, which has true marks, and whose
generalized action sends the actual kernel element e₃·e₁ to the nonzero
constant 4. Hence all three alternatives fail, and the literal statement for an
arbitrary reduced longest word (frozen target (T2)) is refuted.

The value is computed by the actual laws only: ℤ-additivity, the proved signed
generator action (`s_generator`), the proved twisted Leibniz rule
(`divided_mul`) and divided values on generators (`divided_generator`);
literal `Fin` indices are decided by `decide`. Every monomial is consumed by
the four divided operators, so no normal-form/anticommutation step is used for
the witness value itself. The kernel memberships of e₁ and e₃ additionally use
the proved anticommutation-free expansion followed by `abel`.

This does NOT refute the whole-operator identity (2.64) for this word (the
nonzero summands can cancel in the Leibniz sum), nor the chosen-word OWL
already proved in `OmissionCanonical.trichotomy`. -/
namespace OddMath.Frontier.OwlDirect
open OddMath.SkewPolynomial (SkewPolynomial generator)
open AllRankDivided NilCoxeterWords OmissionWord
noncomputable section

local notation "x" => (generator : Fin 5 → SkewPolynomial 5)

/-- Odd elementary e₁ in rank five, increasing-index order, sign (-1)^j. -/
def e1 : SkewPolynomial 5 := x 0 - x 1 + x 2 - x 3 + x 4

/-- Odd elementary e₃ in rank five: ∑_{a<b<c} (-1)^{a+b+c} x_a x_b x_c. -/
def e3 : SkewPolynomial 5 :=
  - x 0 * x 1 * x 2 + x 0 * x 1 * x 3 - x 0 * x 1 * x 4 - x 0 * x 2 * x 3
  + x 0 * x 2 * x 4 - x 0 * x 3 * x 4 + x 1 * x 2 * x 3 - x 1 * x 2 * x 4
  + x 1 * x 3 * x 4 - x 2 * x 3 * x 4

/-- Expansion by the actual laws only (see module docstring). -/
macro "owl_direct_expand" : tactic => `(tactic| (
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
  apply kernel_of <;> (simp only [e1]; owl_direct_expand) <;> abel

theorem e3_kernel : e3 ∈ OddSymmetricKernel.kernelSubring 3 := by
  apply kernel_of <;> (simp only [e3]; owl_direct_expand) <;> abel

/-- The kernel input: an ordered product of two actual kernel elements. -/
def input : SkewPolynomial 5 := e3 * e1

theorem input_kernel : input ∈ OddSymmetricKernel.kernelSubring 3 :=
  (OddSymmetricKernel.kernelSubring 3).mul_mem e3_kernel e1_kernel

/-- The underlying reduced longest word (not the canonical descending-block word). -/
def word : Word 3 := [0,1,0,3,2,1,0,3,2,1]

/-- The witness marking: F F T T T T F F F F, positions left to right. -/
def witness : Marked 3 :=
  [(0,false),(1,false),(0,true),(3,true),(2,true),(1,true),(0,false),(3,false),(2,false),(1,false)]

theorem erase_witness : erase witness = word := rfl

theorem word_reduced : Reduced word := by decide

theorem word_longest : permutation word = LongestElementary.longest 5 := by
  ext i; fin_cases i <;> rfl

theorem word_ne_canonical : word ≠ OmissionCanonical.word 3 := by decide

theorem omission_witness : omission witness = [0,1,0,3,2,1] := rfl

theorem omission_reduced : Reduced (omission witness) := by
  rw [omission_witness]; decide

theorem witness_has_true_mark : ¬ ∀ a ∈ witness, a.2 = false := by
  intro h
  exact absurd (h (0,true) (by simp [witness])) (by decide)

set_option maxHeartbeats 8000000 in
/-- The generalized action s₀ s₁ ∂₀ ∂₃ ∂₂ ∂₁ s₀ s₃ s₂ s₁ on the kernel element e₃e₁. -/
theorem witness_value : hybrid witness input = 4 := by
  simp only [witness, hybrid, Bool.false_eq_true, if_false, if_true, input, e3, e1]
  owl_direct_expand
  norm_num

theorem four_ne_zero : (4 : SkewPolynomial 5) ≠ 0 := by
  intro h
  have h4 : (4 : SkewPolynomial 5) = 1 + 1 + 1 + 1 := by norm_num
  rw [h4] at h
  have hc := congrArg (fun f : SkewPolynomial 5 => f 0) h
  change (Finsupp.single (0 : Fin 5 → ℕ) (1 : ℤ) + Finsupp.single 0 1 +
    Finsupp.single 0 1 + Finsupp.single 0 1 : SkewPolynomial 5) 0 = 0 at hc
  norm_num at hc

/-- The witness violates all three alternatives of the literal trichotomy. -/
theorem witness_not_trichotomy : ¬ Trichotomy witness := by
  rintro (h | h | h)
  · exact four_ne_zero ((witness_value).symm.trans (h input input_kernel))
  · exact witness_has_true_mark h
  · exact h omission_reduced

/-- HEADLINE: the frozen target (T2), literally as required, is false. -/
theorem owl_trichotomy_false :
    ¬ ∀ (n : ℕ) (w : Word n), Reduced w →
      permutation w = LongestElementary.longest (n+2) →
      ∀ m : Marked n, erase m = w → Trichotomy m := by
  intro h
  exact witness_not_trichotomy (h 3 word word_reduced word_longest witness erase_witness)

/-! ## One braid move from the canonical commutation class

The word [3,2,3,1,0,2,1,3,2,3] is obtained from `OmissionCanonical.word 3`
= [3,2,1,0,3,2,1,3,2,3] by commutation moves only (diagnostic, braid-boundary.json);
applying the single braid move 323 → 232 at the left end gives
[2,3,2,1,0,2,1,3,2,3]. With the SAME marking T T F T T T F F F F both marked
actions send the kernel element e₃e₂ to the same nonzero constant 4; before the
move the omission word is non-reduced (so alternative (3) holds), after it the
omission word is reduced (so the trichotomy fails). This is the exact point where
"free to reorder D_a up to sign" does not transport the termwise lemma. -/

/-- Odd elementary e₂ in rank five: ∑_{a<b} (-1)^{a+b} x_a x_b. -/
def e2 : SkewPolynomial 5 :=
  - x 0 * x 1 + x 0 * x 2 - x 0 * x 3 + x 0 * x 4 - x 1 * x 2 + x 1 * x 3 - x 1 * x 4 - x 2 * x 3 + x 2 * x 4 - x 3 * x 4

theorem e2_kernel : e2 ∈ OddSymmetricKernel.kernelSubring 3 := by
  apply kernel_of <;> (simp only [e2]; owl_direct_expand) <;> abel

def input₂ : SkewPolynomial 5 := e3 * e2

theorem input₂_kernel : input₂ ∈ OddSymmetricKernel.kernelSubring 3 :=
  (OddSymmetricKernel.kernelSubring 3).mul_mem e3_kernel e2_kernel

/-- Before the braid move (a word in the canonical commutation class). -/
def wordBefore : Word 3 := [3,2,3,1,0,2,1,3,2,3]
/-- After the single braid move 323 → 232 in positions 0..2. -/
def wordAfter : Word 3 := [2,3,2,1,0,2,1,3,2,3]

def marksOn (w : Word 3) : Marked 3 :=
  w.zip [true,true,false,true,true,true,false,false,false,false]

theorem erase_before : erase (marksOn wordBefore) = wordBefore := rfl
theorem erase_after : erase (marksOn wordAfter) = wordAfter := rfl

theorem before_reduced : Reduced wordBefore := by decide
theorem before_longest : permutation wordBefore = LongestElementary.longest 5 := by
  ext i; fin_cases i <;> rfl
theorem after_reduced : Reduced wordAfter := by decide
theorem after_longest : permutation wordAfter = LongestElementary.longest 5 := by
  ext i; fin_cases i <;> rfl

theorem omission_before_nonreduced : ¬ Reduced (omission (marksOn wordBefore)) := by decide
theorem omission_after_reduced : Reduced (omission (marksOn wordAfter)) := by decide

set_option maxHeartbeats 16000000 in
theorem value_before : hybrid (marksOn wordBefore) input₂ = 4 := by
  simp only [marksOn, wordBefore, List.zip_cons_cons, List.zip_nil_right, hybrid,
    Bool.false_eq_true, if_false, if_true, input₂, e3, e2]
  owl_direct_expand
  norm_num

set_option maxHeartbeats 16000000 in
theorem value_after : hybrid (marksOn wordAfter) input₂ = 4 := by
  simp only [marksOn, wordAfter, List.zip_cons_cons, List.zip_nil_right, hybrid,
    Bool.false_eq_true, if_false, if_true, input₂, e3, e2]
  owl_direct_expand
  norm_num

/-- After one braid move the literal trichotomy fails. -/
theorem after_not_trichotomy : ¬ Trichotomy (marksOn wordAfter) := by
  rintro (h | h | h)
  · exact four_ne_zero (value_after.symm.trans (h input₂ input₂_kernel))
  · exact absurd (h (2,true) (by decide)) (by decide)
  · exact h omission_after_reduced

/-- Before the move the same marked action is the same nonzero value, and the
trichotomy holds only through the non-reduced omission alternative. -/
theorem before_trichotomy_only_by_nonreduced :
    hybrid (marksOn wordBefore) input₂ ≠ 0 ∧ ¬ Reduced (omission (marksOn wordBefore)) :=
  ⟨by rw [value_before]; exact four_ne_zero, omission_before_nonreduced⟩

end
end OddMath.Frontier.OwlDirect
