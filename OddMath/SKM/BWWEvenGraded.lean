/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BWWEvenDictionary
import OddMath.SKM.BWWGradedParameters

/-!
# The grading condition on the Brundan–Wang–Webster polynomials

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2: over an `ℕ`-graded commutative ring
`k = ⨁ₙ 𝒜 n`, with `x` of degree `2dᵢ` and `y` of degree `2dⱼ`, each `Qᵢⱼ(x, y)` is
homogeneous of degree `-2dᵢaᵢⱼ`. Coefficientwise: the coefficient of `x^p y^q` lies in
`𝒜 n` with `n = 2(dᵢdᵢⱼ - dᵢp - dⱼq)` (`coefficientDegree`).

* `BWWPolynomials.GradedHomogeneous`: this condition on every nonzero coefficient.
* `BWWPolynomials.gradedHomogeneous_toBWWScalars_iff`: on purely even data it is equivalent
  to `BWWScalars.GradedHomogeneous` of the coefficient function (`bwwPolynomialsEquiv`).
  The corner coefficients `tᵢⱼ` have coefficient degree `0`, by symmetrizability
  `dᵢdᵢⱼ = dⱼdⱼᵢ` at the corner `y^{dⱼᵢ}`.
-/

noncomputable section

namespace OddMath.SKM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
variable {k : Type w} [CommRing k]

namespace BWWPolynomials

/-- Brundan–Wang–Webster §2.2 over `k = ⨁ₙ 𝒜 n`: `Qᵢⱼ` is homogeneous of degree `-2dᵢaᵢⱼ`
when `x`, `y` have degrees `2dᵢ`, `2dⱼ`, coefficientwise. -/
def GradedHomogeneous {σ : Type*} [SetLike σ k] (sy : Symmetrizer D) (𝒜 : ℕ → σ)
    (P : BWWPolynomials D k) : Prop :=
  ∀ i j (p q : ℕ), (P.Q i j).coeff (bwwExp p q) ≠ 0 →
    ∃ n : ℕ, (n : ℤ) = coefficientDegree sy i j p q ∧ (P.Q i j).coeff (bwwExp p q) ∈ 𝒜 n

/-- The corner `x^{dᵢⱼ}` has coefficient degree `0`. -/
theorem coefficientDegree_corner (sy : Symmetrizer D) {i j : I} (hij : i ≠ j) :
    coefficientDegree sy i j (D.dn i j) 0 = 0 := by
  unfold coefficientDegree
  rw [D.dn_cast hij]
  ring

/-- The corner `y^{dⱼᵢ}` has coefficient degree `0`. -/
theorem coefficientDegree_corner' (sy : Symmetrizer D) {i j : I} (hij : i ≠ j) :
    coefficientDegree sy i j 0 (D.dn j i) = 0 := by
  rw [coefficientDegree_symm]
  exact coefficientDegree_corner sy (Ne.symm hij)

/-- **The graded even dictionary.** On purely even data, the grading condition on the
polynomials `Qᵢⱼ` is the grading condition on their coefficient function. -/
theorem gradedHomogeneous_toBWWScalars_iff {σ : Type*} [SetLike σ k] [AddSubmonoidClass σ k]
    (sy : Symmetrizer D) (𝒜 : ℕ → σ) [SetLike.GradedOne 𝒜] (P : BWWPolynomials D k)
    (hD : ∀ i, D.parity i = 0) :
    (P.toBWWScalars hD).GradedHomogeneous sy 𝒜 ↔ P.GradedHomogeneous sy 𝒜 := by
  constructor
  · rintro ⟨ht, hc⟩ i j p q hs
    have hij : i ≠ j := by
      rintro rfl
      exact hs (by rw [P.Q_self]; simp)
    have hdn : (D.dn i j : ℤ) = D.d i j := D.dn_cast hij
    have hdn' : (D.dn j i : ℤ) = D.d j i := D.dn_cast (Ne.symm hij)
    obtain ⟨⟨hp, hq⟩, htop, hright⟩ := P.support i j p q hs
    by_cases h1 : p = D.dn i j
    · obtain rfl := htop h1
      subst h1
      refine ⟨0, (coefficientDegree_corner sy hij).symm, ?_⟩
      rw [← P.t_of_ne hij]
      exact ht i j
    by_cases h2 : q = D.dn j i
    · obtain rfl := hright h2
      subst h2
      refine ⟨0, (coefficientDegree_corner' sy hij).symm, ?_⟩
      rw [← P.coeff_symm, ← P.t_of_ne (Ne.symm hij)]
      exact ht j i
    exact hc i j p q hij (by omega) (by omega) hs
  · intro h
    refine ⟨fun i j => ?_, fun i j p q hij _ _ hs => h i j p q hs⟩
    by_cases hij : i = j
    · subst hij
      rw [show ((P.toBWWScalars hD).t i i : k) = 1 by
        rw [(P.toBWWScalars hD).t_self]; rfl]
      exact SetLike.GradedOne.one_mem
    change ((P.t i j : kˣ) : k) ∈ 𝒜 0
    rw [P.t_of_ne hij]
    by_cases hs : (P.Q i j).coeff (bwwExp (D.dn i j) 0) = 0
    · rw [hs]
      exact zero_mem _
    obtain ⟨n, hn, hm⟩ := h i j _ _ hs
    rw [coefficientDegree_corner sy hij] at hn
    obtain rfl : n = 0 := by omega
    exact hm

end BWWPolynomials

end OddMath.SKM
