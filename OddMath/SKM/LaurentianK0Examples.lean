/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.LaurentianK0
import OddMath.SKM.DimensionFormulaExamples
import StringDiagrams.Super.KrullSchmidtLaurentExamples

/-!
# Concrete consumers of the Laurent basis theorem

Two orthogonal odd colours with rational scalar and bubble parameters discharge
all hypotheses of the Laurentian K₀ theorem for the completed SKM hom categories.
The independent rational-field envelope also records a nonzero indecomposable
class. No nondegeneracy assertion for the SKM presentation is inferred from freeness.
-/

noncomputable section
namespace OddMath.SKM.LaurentianK0Examples
open CategoryTheory StringDiagrams
open CoveringQuantum.UDot.ContextualExchangeExamples
open DimensionFormulaExamples

/-- The concrete two-odd-colour graded SKM category. -/
abbrev B := UGr twoOddDatum.toSKM scalars twoOddDatum.skmSymmetrizer homogeneous

/-- Every pair of weights satisfies the Laurent freeness theorem, without NDC. -/
theorem k0_free (a b : B) :
    letI := K₀.moduleLaurentInt ℚ (GSKAR.mkObj ℚ B a ⟶ GSKAR.mkObj ℚ B b)
    Module.Free (LaurentPolynomial ℤ) (K₀ (GSKAR.mkObj ℚ B a ⟶ GSKAR.mkObj ℚ B b)) :=
  UDot.k0_free_laurentInt twoOddDatum.skmSymmetrizer cScalars homogeneous locallyFinite a b

/-- The concrete Laurent orbit basis, not only an existential freeness proposition. -/
def basis (a b : B) :=
  UDot.laurentBasis twoOddDatum.skmSymmetrizer cScalars homogeneous locallyFinite a b

/-- The generic theorem also applies to a provably nonzero rank-one projective. -/
example : K₀.mk KrullSchmidtLaurentExamples.line ≠ 0 :=
  KrullSchmidtLaurentExamples.line_class_ne_zero

#print axioms k0_free
#print axioms basis

end OddMath.SKM.LaurentianK0Examples
