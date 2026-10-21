import OddMath

/-! BE2 (dum): populated mixed-boundary checks and both rational parity signs.
The formula remains conditional on the Nondegeneracy Conjecture, exactly as
in its source. No instance of the conjecture is asserted by this file. -/
noncomputable section
namespace DimensionFormulaConsumer
open OddMath.SKM OddMath.CoveringQuantum
open OddMath.SKM.DimensionFormulaExamples
open OddMath.SKM.Theorem103Examples
open OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.CoveringQuantum.UDot.GenericTensor
open OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram

example : ((matchingChoice true).members).Nonempty := matchingChoice_nonempty true
example : ((matchingChoice false).members).Nonempty := matchingChoice_nonempty false

example (μ : Bool → ℤ) : Function.Surjective
    ((matchingChoice true).componentExpansion twoOddDatum.skmSymmetrizer cScalars μ (0, 0)) :=
  component_surjective true μ 0 0

example (μ : Bool → ℤ) : Function.Surjective
    ((matchingChoice false).componentExpansion twoOddDatum.skmSymmetrizer cScalars μ (2, 1)) :=
  component_surjective false μ 2 1

example : FiniteDimensional ℚ (SYM.component twoOddDatum.skmSymmetrizer ℚ (2, 1)) :=
  coefficient_finite 2 1

example : (symDimension twoOddDatum.skmSymmetrizer ℚ (-1)).coeff (-1) = 0 :=
  coefficient_negative (-1) (-1) (by norm_num)

example (hN : NondegeneracyConjecture cScalars) (μ : Bool → ℤ) :
    homDimension twoOddDatum.skmSymmetrizer cScalars homogeneous locallyFinite
      μ (boundary true) (boundary true) 1 =
      signLaurent 1 (by norm_num) (sesquilinearForm twoOddDatum
        (algebraWord twoOddDatum μ (boundary true)) (algebraWord twoOddDatum μ (boundary true))) *
      symDimension twoOddDatum.skmSymmetrizer ℚ 1 :=
  mixed_formula hN true μ 1 (by norm_num)

example (hN : NondegeneracyConjecture cScalars) (μ : Bool → ℤ) :
    homDimension twoOddDatum.skmSymmetrizer cScalars homogeneous locallyFinite
      μ (boundary false) (boundary false) (-1) =
      signLaurent (-1) (by norm_num) (sesquilinearForm twoOddDatum
        (algebraWord twoOddDatum μ (boundary false)) (algebraWord twoOddDatum μ (boundary false))) *
      symDimension twoOddDatum.skmSymmetrizer ℚ (-1) :=
  mixed_formula hN false μ (-1) (by norm_num)

#print axioms OddMath.SKM.MatchingBasisChoice.componentExpansion_surjective
#print axioms OddMath.SKM.MatchingBasisChoice.componentExpansionEquiv
#print axioms OddMath.SKM.homPar_eq_homDeg
#print axioms OddMath.SKM.wordHomComponent_finrank_of_nondegeneracy
#print axioms OddMath.SKM.laurentSeries_coeff_mul_eq_sum_bounded
#print axioms OddMath.SKM.hom_dimension_eq_form_mul_sym
end DimensionFormulaConsumer
