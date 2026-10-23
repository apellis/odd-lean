import OddMath.SKM.BubbleTruncation

/-! Checks on the abstract coefficient algebra, not a claim about the bubble map. -/

noncomputable section
open scoped Classical
open OddMath.SKM

namespace NonVacuity.BubbleTruncation

variable {I X : Type} [AddCommGroup X] (D : Datum I X)

/-- Truncation retains a product of distinct-colour odd coefficients whenever both
of its generators are retained; no single-colour square-zero shortcut is used. -/
example (i j : {i : I // D.parity i = 1}) :
    SYM.truncate D ℚ ({Sum.inr i, Sum.inr j} : Finset (SYMGen D))
      (SYM.delta D ℚ i * SYM.delta D ℚ j) =
        SYM.delta D ℚ i * SYM.delta D ℚ j := by
  simp [map_mul, SYM.delta]

example {A : Type} (c : A →₀ SYM D ℚ) :
    ∃ S : Finset (SYMGen D), ∀ a, SYM.truncate D ℚ S (c a) = c a :=
  SYM.exists_truncate_fixed_coefficients D ℚ c

#print axioms SYM.exists_truncate_fixed
#print axioms SYM.exists_truncate_fixed_finset
#print axioms SYM.exists_truncate_fixed_coefficients
#print axioms SYM.truncations_separate
#print axioms SYM.exists_truncate_ne_zero

end NonVacuity.BubbleTruncation
