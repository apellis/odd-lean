import OddMath

/-! Consumers of `OddMath/QuiverHecke/HomBases.lean` on the two-odd-colour datum over `ℚ`
with constant parameters: `β_λ` is an isomorphism, the decorated matchings times the monomials
of `SYM` form a basis of a populated mixed Hom space, and BE2 (dum) holds for both signs. -/
noncomputable section
namespace HomBasesConsumer
open CategoryTheory OddMath OddMath.SKM OddMath.CoveringQuantum
open OddMath.SKM.DimensionFormulaExamples
open OddMath.SKM.Theorem103Examples
open OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.CoveringQuantum.UDot.GenericTensor
open OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram

theorem two_isUnit : IsUnit (2 : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)

example (μ : Bool → ℤ) : Function.Bijective (betaSYM cScalars μ) :=
  QuiverHecke.betaSYM_bijective twoOddDatum.skmSymmetrizer two_isUnit homogeneous cScalars μ

example (μ : Bool → ℤ) :
    SYM twoOddDatum.toSKM ℚ ≃ₐ[ℚ] End ((pres twoOddDatum.toSKM scalars).obj
      (ob twoOddDatum.toSKM μ [])) :=
  QuiverHecke.betaSYMEquiv twoOddDatum.skmSymmetrizer two_isUnit homogeneous cScalars μ

example (μ : Bool → ℤ) (t : (matchingChoice true).Labels)
    (η : SYM.CoefficientIndex twoOddDatum.toSKM) :
    (matchingChoice true).homBasisOfSymmetrizer twoOddDatum.skmSymmetrizer two_isUnit
      homogeneous cScalars rfl μ ⟨t, η⟩ =
      bubAt twoOddDatum.toSKM scalars μ (boundary true)
        (betaSYM cScalars μ (SYM.coefficientBasis twoOddDatum.toSKM ℚ η)) ≫
        xev cScalars μ (boundary true) (boundary true) ((matchingChoice true).layers t) :=
  (matchingChoice true).homBasisOfSymmetrizer_apply twoOddDatum.skmSymmetrizer two_isUnit
    homogeneous cScalars rfl μ t η

example (μ : Bool → ℤ) : Module.Free ℚ
    ((pres twoOddDatum.toSKM scalars).obj (ob twoOddDatum.toSKM μ (boundary false)) ⟶
      (pres twoOddDatum.toSKM scalars).obj (ob twoOddDatum.toSKM μ (boundary false))) :=
  (matchingChoice false).free_hom twoOddDatum.skmSymmetrizer two_isUnit homogeneous cScalars
    rfl μ

example (μ : Bool → ℤ) :
    homDimension twoOddDatum.skmSymmetrizer cScalars homogeneous locallyFinite
      μ (boundary true) (boundary true) (-1) =
      signLaurent (-1) (by norm_num) (sesquilinearForm twoOddDatum
        (algebraWord twoOddDatum μ (boundary true)) (algebraWord twoOddDatum μ (boundary true))) *
      symDimension twoOddDatum.skmSymmetrizer ℚ (-1) :=
  QuiverHecke.homDimension_eq_form_mul_symDimension twoOddDatum (by norm_num) homogeneous
    cScalars locallyFinite μ (boundary true) (boundary true) rfl (-1) (by norm_num)

example (μ : Bool → ℤ) (n : ℤ) :
    (homDimension twoOddDatum.skmSymmetrizer cScalars homogeneous locallyFinite
      μ (boundary false) (boundary false) 1).coeff n =
      ∑ t : (matchingChoice false).boundedLabels twoOddDatum.skmSymmetrizer μ n,
        1 ^ ((matchingChoice false).labelBidegree twoOddDatum.skmSymmetrizer μ t.val).2.val *
        (symDimension twoOddDatum.skmSymmetrizer ℚ 1).coeff
          (n - ((matchingChoice false).labelBidegree twoOddDatum.skmSymmetrizer μ t.val).1) :=
  QuiverHecke.homDimension_coeff_eq_sum (matchingChoice false) twoOddDatum.skmSymmetrizer
    (by norm_num) homogeneous cScalars locallyFinite rfl μ 1 (by norm_num) n

#print axioms OddMath.QuiverHecke.betaSYM_bijective
#print axioms OddMath.SKM.MatchingBasisChoice.expansionEquiv
#print axioms OddMath.SKM.MatchingBasisChoice.expansion_mapRange_mul
#print axioms OddMath.SKM.MatchingBasisChoice.homBasisOfSymmetrizer_apply
#print axioms OddMath.SKM.MatchingBasisChoice.componentEquiv
#print axioms OddMath.QuiverHecke.wordHomComponent_finrank_eq_sum
#print axioms OddMath.QuiverHecke.homDimension_coeff_eq_sum
#print axioms OddMath.QuiverHecke.homDimension_eq_form_mul_symDimension

end HomBasesConsumer
