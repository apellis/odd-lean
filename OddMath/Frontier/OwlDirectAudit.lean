import OddMath.Frontier.OwlDirect

/-! Audit for the direct OWL proof: exact headline types, restated with no residual
hypothesis, and transitive axioms of every headline and supporting declaration. -/
namespace OddMath.Frontier.OwlDirectAudit
open OddMath.SkewPolynomial (SkewPolynomial)
open NilCoxeterWords OmissionWord

/-- Restatement of the headline: the frozen (T2) shape
`∀ n w, Reduced w → permutation w = longest (n+2) → ∀ m, erase m = w → Trichotomy m`
is refuted outright; no hypothesis is left open. -/
theorem restated_owl_trichotomy_false :
    ¬ ∀ (n : ℕ) (w : Word n), Reduced w →
      permutation w = LongestElementary.longest (n+2) →
      ∀ m : Marked n, erase m = w → Trichotomy m :=
  OwlDirect.owl_trichotomy_false

/-- Restatement of the concrete witness data. -/
theorem restated_witness :
    Reduced OwlDirect.word ∧ permutation OwlDirect.word = LongestElementary.longest 5 ∧
    OwlDirect.word ≠ OmissionCanonical.word 3 ∧ erase OwlDirect.witness = OwlDirect.word ∧
    Reduced (omission OwlDirect.witness) ∧ (¬ ∀ a ∈ OwlDirect.witness, a.2 = false) ∧
    OwlDirect.input ∈ OddSymmetricKernel.kernelSubring 3 ∧
    hybrid OwlDirect.witness OwlDirect.input = 4 ∧ (4 : SkewPolynomial 5) ≠ 0 :=
  ⟨OwlDirect.word_reduced, OwlDirect.word_longest, OwlDirect.word_ne_canonical,
    OwlDirect.erase_witness, OwlDirect.omission_reduced, OwlDirect.witness_has_true_mark,
    OwlDirect.input_kernel, OwlDirect.witness_value, OwlDirect.four_ne_zero⟩

#check @OwlDirect.owl_trichotomy_false
#check @OwlDirect.witness_not_trichotomy
#check @OwlDirect.witness_value
#check @OwlDirect.input_kernel
#print OwlDirect.word
#print OwlDirect.witness
#print OwlDirect.input
#print OwlDirect.e1
#print OwlDirect.e3
#print OmissionWord.Trichotomy

#print axioms restated_owl_trichotomy_false
#print axioms restated_witness
#print axioms OwlDirect.owl_trichotomy_false
#print axioms OwlDirect.witness_not_trichotomy
#print axioms OwlDirect.witness_value
#print axioms OwlDirect.four_ne_zero
#print axioms OwlDirect.input_kernel
#print axioms OwlDirect.e1_kernel
#print axioms OwlDirect.e3_kernel
#print axioms OwlDirect.word_reduced
#print axioms OwlDirect.word_longest
#print axioms OwlDirect.word_ne_canonical
#print axioms OwlDirect.omission_reduced
#print axioms OwlDirect.witness_has_true_mark
#check @OwlDirect.after_not_trichotomy
#check @OwlDirect.before_trichotomy_only_by_nonreduced
#print OwlDirect.wordBefore
#print OwlDirect.wordAfter
#print axioms OwlDirect.after_not_trichotomy
#print axioms OwlDirect.before_trichotomy_only_by_nonreduced
#print axioms OwlDirect.value_before
#print axioms OwlDirect.value_after
#print axioms OwlDirect.e2_kernel
#print axioms OwlDirect.after_reduced
#print axioms OwlDirect.after_longest
#print axioms OwlDirect.before_reduced
#print axioms OwlDirect.before_longest

end OddMath.Frontier.OwlDirectAudit
