import OddMath

/-! Consumers of `OddMath/SKM/SymComponentBasis.lean` on the two-odd-colour datum:
the monomials of each bidegree form a basis of the homogeneous component of `SYM`, and the
graded superdimension of `SYM` counts monomials. -/
noncomputable section
namespace SymComponentBasisConsumer
open OddMath OddMath.SKM
open OddMath.SKM.DimensionFormulaExamples
open OddMath.SKM.Theorem103Examples
open OddMath.CoveringQuantum.UDot.ContextualExchangeExamples

example (z : ℤ × ZMod 2) (η : {η : SYM.CoefficientIndex twoOddDatum.toSKM //
      SYM.coefficientBidegree twoOddDatum.skmSymmetrizer η = z}) :
    (SYM.componentBasis twoOddDatum.skmSymmetrizer ℤ z η : SYM twoOddDatum.toSKM ℤ) =
      SYM.coefficientBasis twoOddDatum.toSKM ℤ η.1 :=
  SYM.componentBasis_apply _ _ z η

example (z : ℤ × ZMod 2) :
    Module.finrank ℚ (SYM.component twoOddDatum.skmSymmetrizer ℚ z) =
      Nat.card {η : SYM.CoefficientIndex twoOddDatum.toSKM //
        SYM.coefficientBidegree twoOddDatum.skmSymmetrizer η = z} :=
  SYM.finrank_component _ ℚ z

example (σ : ℚ) (n : ℤ) :
    (symDimension twoOddDatum.skmSymmetrizer ℚ σ).coeff n = ∑ p : ZMod 2, σ ^ p.val *
      (Nat.card {η : SYM.CoefficientIndex twoOddDatum.toSKM //
        SYM.coefficientBidegree twoOddDatum.skmSymmetrizer η = (n, p)} : ℚ) :=
  symDimension_coeff_eq_card _ ℚ σ n

#print axioms OddMath.SKM.SYM.componentBasis
#print axioms OddMath.SKM.SYM.finrank_component
#print axioms OddMath.SKM.symDimension_coeff_eq_card

end SymComponentBasisConsumer
