import OddMath.SKM.BubbleELVGrading
import NonVacuity.ELVCoefficientCategory

noncomputable section
namespace ELVCoefficientGradingConsumer
open OddMath.SKM OddMath.SKM.SYM ELVCoefficientCategoryConsumer

def sy : Symmetrizer datum where
  d := fun _ => 1
  pos := fun _ => by decide
  symm := fun _ _ => rfl

example : delta ∈ coefficientDegreePart datum ℚ sy 2 :=
  delta_mem_coefficientDegreePart datum ℚ sy oddColour

example : e datum ℚ () 0 ∈ coefficientDegreePart datum ℚ sy 4 := by
  simpa [elementaryWeight, datum, sy] using
    elementary_mem_coefficientDegreePart datum ℚ sy () 0

example : GradedAlgebra (coefficientDegreePart datum ℚ sy) := inferInstance

example : ∃ M : ℤ, 0 ≤ M ∧ ∀ a : CoefficientIndex datum,
    coefficientDegree datum sy a ≤ M * coefficientWeight datum a :=
  exists_coefficientDegree_bound datum sy

example : GradedAlgebra (elvCoefficientDegree (k := ℚ) datum sy (fun _ => 2)) := inferInstance

example : ∃ b : ℤ, ∀ n, b < n →
    truncatedELVCoefficientDegree (k := ℚ) datum sy (fun _ => 2) 3 n = ⊥ :=
  truncatedELVCoefficientDegree_bounded datum sy (fun _ => 2) 3

/-- The odd coefficient is retained by the additional homogeneous truncation. -/
theorem truncated_delta_ne_zero :
    truncatedELVCoefficientQuotient datum (fun _ => 2) 3 delta ≠ 0 := by
  have hd : delta ∈ CoefficientAtMost datum ℚ 1 := by
    exact Submodule.subset_span ⟨(0, {oddColour}), by simp [coefficientWeight],
      coefficientBasis_delta datum ℚ oddColour⟩
  intro hz
  have hi := truncatedELVCoefficient_quotient_injective (k := ℚ) datum
    (cutoff := fun _ => 2) (d := 1) (N := 3) (by intro i; decide) (by decide)
  have he := hi (a₁ := ⟨delta, hd⟩) (a₂ := 0) hz
  exact delta_ne_zero (congrArg Subtype.val he)

def vacuum : StringDiagrams.GSuperAlg ℚ :=
  truncatedELVCoefficientGSuperAlg datum sy (fun _ => 2) 3

example : StringDiagrams.GSuperAlg ℚ := elvCoefficientGSuperAlg datum sy (fun _ => 2)

example : ∃ b : ℤ, ∀ n, b < n → vacuum.degree n = ⊥ :=
  truncatedELVCoefficientDegree_bounded datum sy (fun _ => 2) 3

example : truncatedELVCoefficientQuotient datum (fun _ => 2) 3 delta ∈ vacuum.grading 1 := by
  change truncatedELVCoefficientQuotient datum (fun _ => 2) 3 delta ∈
    truncatedELVCoefficientParity datum (fun _ => 2) 3 1
  simpa only [ELVCoefficientCategoryConsumer.delta, coefficientBasis_delta,
    Finset.card_singleton, Nat.cast_one] using
    truncatedELVCoefficientBasis_mem_parity (k := ℚ) datum (fun _ => 2) 3 (0, {oddColour})

example : truncatedELVCoefficientQuotient datum (fun _ => 2) 3 delta ∈ vacuum.degree 2 :=
  ⟨delta, delta_mem_coefficientDegreePart datum ℚ sy oddColour, rfl⟩

/-- Integer degree mod two is zero for the nonzero odd generator. -/
example : (2 : ZMod 2) = 0 := by decide

example : elvCoefficientTruncation datum (fun _ => 2) 3
    (elvCoefficientQuotient datum (fun _ => 2) delta) =
    truncatedELVCoefficientQuotient datum (fun _ => 2) 3 delta := rfl

#print axioms OddMath.SKM.SYM.elvCoefficientGSuperAlg
#print axioms OddMath.SKM.SYM.truncatedELVCoefficientGSuperAlg
#print axioms OddMath.SKM.SYM.coefficientDegreeGradedAlgebra
#print axioms OddMath.SKM.SYM.elvCoefficientDegreeGrading
#print axioms OddMath.SKM.SYM.truncatedELVCoefficientDegreeGrading
#print axioms OddMath.SKM.SYM.truncatedELVCoefficientDegree_bounded
#print axioms ELVCoefficientGradingConsumer.truncated_delta_ne_zero

end ELVCoefficientGradingConsumer
