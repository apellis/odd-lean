import OddMath

/-! # `K₀` is spanned by shifted products of divided powers (BE2 Theorem 11.3, surjectivity)

On the datum of `OddMath.QuiverHecke.AlgebraExamples` over `ℚ`: every class of the envelope `HKar`
lies in the span of the classes `[P(i₁^{(r₁)} ⋯ i_l^{(r_l)})⟨n⟩Πᵖ]`.
-/

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples

example : dpSpan datum scalars symmetrizer homogeneous = ⊤ :=
  dpSpan_eq_top datum scalars symmetrizer homogeneous

example (P : HKar datum scalars symmetrizer homogeneous) :
    K₀.mk P ∈ dpSpan datum scalars symmetrizer homogeneous :=
  mk_mem_dpSpan datum scalars symmetrizer homogeneous P

#print axioms dpSpan_eq_top
