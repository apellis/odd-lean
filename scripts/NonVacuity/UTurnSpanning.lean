import OddMath

/-! # BE2 Theorem 11.7, surjectivity: endomorphisms of sorted words modulo U-turns

The two-odd-colour rational datum of `OddMath.SKM.DimensionFormulaExamples`, at the sorted word
`E_true F_false` (one upward and one downward letter).
-/

noncomputable section
namespace NonVacuity.UTurnSpanning
open CategoryTheory StringDiagrams OddMath OddMath.SKM
open OddMath.CoveringQuantum.UDot.ContextualExchangeExamples OddMath.SKM.DimensionFormulaExamples

/-- Every endomorphism of `E_true F_false 1_0` is split diagrams times bubbles, modulo composites
through the empty word. -/
example : SplitSpan scalars cScalars (0 : Bool → ℤ) [up true, dn false] [up true, dn false] ⊔
    ShortSpan scalars (0 : Bool → ℤ) [up true, dn false] [up true, dn false] = ⊤ :=
  splitSpan_sup_shortSpan scalars cScalars 0 (lSorted_of_sorted ⟨[true], [false], rfl⟩)
    (lSorted_of_sorted ⟨[true], [false], rfl⟩) rfl

/-- A bottom U-turn forces a shorter word; no U-turns forces sorted crossings only. -/
example := @exists_strictReduced_matching_shape

#print axioms OddMath.SKM.splitSpan_sup_shortSpan
#print axioms OddMath.SKM.exists_strictReduced_matching_shape

end NonVacuity.UTurnSpanning
