/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.PreF.PermutationForm
import OddMath.CoveringQuantum.UDot.SesquilinearForm

/-!
# Positive-word values of the sesquilinear form

Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.3, Claim 1: the equal-length
algebraic weighted-permutation calculation and unequal-length vanishing for the
existing modified form.
The normalization and crossing factors are the `norm` and `chi` of `HalfAlgebra`.
Permutations map source positions to target positions, so colour preservation is
`a r = b (w r)`, with source colours in the inversion product.

The existing constructed sesquilinear form allows arbitrary colours without
bar consistency. No matching enumeration, generating-series
identity, or mixed-sign case of Theorem 10.3 is asserted here.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (D : RootDatum I X)

/-- Weighted-permutation value of reversed positive words in the existing sesquilinear
form ([BE2], Theorem 10.3, Claim 1, algebraic step), for arbitrary colours
without bar consistency. -/
theorem sesquilinearForm_positive_words_permutations (μ : X) (n : ℕ)
    (a b : Fin n → I) :
    sesquilinearForm D
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

/-- Unequal positive boundary lengths give zero in the existing modified form
([BE2], Theorem 10.3, Claim 1). Orthogonality uses formal colour multidegrees,
not root independence. Colours may be infinite, without bar consistency. -/
theorem sesquilinearForm_positive_words_eq_zero_of_length_ne
    (μ : X) {m n : ℕ} (a : Fin m → I) (b : Fin n → I) (hmn : m ≠ n) :
    sesquilinearForm D
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi
          (monomial Coefficients.Ring (List.ofFn a).reverse)))
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi
          (monomial Coefficients.Ring (List.ofFn b).reverse))) = 0 := by
  rw [sesquilinearForm_reversed_words, SuperCartanDatum.serreForm_toSerreF]
  apply form_monomial_eq_zero (D.chi Coefficients.q pi)
    (D.norm Coefficients.q pi) (List.ofFn a) _ _ (monomial_mem_weightSpace _)
  intro hw
  have hp : (List.ofFn a).Perm (List.ofFn b) :=
    List.perm_iff_count.mpr (fun i => by
      simpa only [← wordWeight_apply] using
        congrArg (fun ν : I →₀ ℕ => ν i) hw)
  exact hmn (by simpa using hp.length_eq)

end OddMath.CoveringQuantum.UDot.GenericTensor
