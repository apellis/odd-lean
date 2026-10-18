import OddMath.CoveringQuantum.PreF.PermutationForm
import OddMath.CoveringQuantum.UDot.SesquilinearForm

/-!
# Positive-word values of the sesquilinear form

Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.3, Claim 1: the equal-length
algebraic weighted-permutation calculation for the existing modified form.
The normalization and crossing factors are the `norm` and `chi` of `HalfAlgebra`.
Permutations map source positions to target positions, so colour preservation is
`a r = b (w r)`, with source colours in the inversion product.

The existing constructed sesquilinear form requires finite bar-consistent data;
these route restrictions remain explicit. No matching enumeration, generating-series
identity, or mixed-sign case of Theorem 10.3 is asserted here.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  [Finite I] (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent)

/-- Weighted-permutation value of reversed positive words in the existing sesquilinear
form ([BE2], Theorem 10.3, Claim 1, algebraic step). The finite/bar-consistent
hypotheses come from the constructed form, not from the free-form calculation. -/
theorem sesquilinearForm_positive_words_permutations (μ : X) (n : ℕ)
    (a b : Fin n → I) :
    sesquilinearForm D hD
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring (List.ofFn a).reverse)))
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring (List.ofFn b).reverse))) =
      (∏ r, D.norm Coefficients.q pi (a r)) *
        ∑ w : Equiv.Perm (Fin n), if ∀ r, a r = b (w r) then
          ∏ r, ∏ s with r < s ∧ w s < w r, D.chi Coefficients.q pi (a r) (a s)
        else 0 := by
  rw [sesquilinearForm_reversed_words, SuperCartanDatum.serreForm_toSerreF]
  exact form_monomial_permutations (D.chi Coefficients.q pi)
    (D.norm Coefficients.q pi) n a b

end OddMath.CoveringQuantum.UDot.GenericTensor
