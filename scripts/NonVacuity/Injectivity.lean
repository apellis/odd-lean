import OddMath

/-! # BE2 Theorem 12.1 (injectivity of `γ`), on a concrete datum

The two-odd-colour rational datum of `OddMath.SKM.LaurentianK0Examples`. Every hypothesis of
`QuiverHecke.SerreComplex.theorem_12_1` is proved here except the Nondegeneracy Conjecture,
which is a hypothesis in the source as well; no instance of the conjecture is asserted.
-/

noncomputable section
namespace NonVacuity.Injectivity
open CategoryTheory StringDiagrams LaurentPolynomial OddMath OddMath.QuiverHecke.SerreComplex
open OddMath.SKM.LaurentianK0Examples OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.SKM.DimensionFormulaExamples

theorem twoOdd_root_independent : LinearIndependent ℤ twoOddDatum.α := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg i
  cases i <;> simpa [twoOddDatum, OddMath.CoveringQuantum.RootDatum.α] using h

theorem twoOdd_coroot_independent : LinearIndependent ℤ twoOddDatum.cd.coroot := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (fun f : Module.Dual ℤ (Bool → ℤ) ↦ f (Pi.single i 1)) hg
  cases i <;> simpa [twoOddDatum, Pi.single_apply] using h

/-- Injectivity of `γ`, given the Nondegeneracy Conjecture. -/
example (hN : OddMath.SKM.NondegeneracyConjecture cScalars) :
    Function.Injective (gammaInt twoOddDatum homogeneous cScalars locallyFinite) :=
  theorem_12_1 twoOddDatum homogeneous cScalars locallyFinite hN twoOdd_barConsistent
    twoOdd_root_independent twoOdd_coroot_independent

#print axioms OddMath.QuiverHecke.SerreComplex.theorem_12_1

end NonVacuity.Injectivity
