/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BWWScalars
import OddMath.SKM.GradedParameters

/-!
# Graded Brundan–Wang–Webster parameters

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2: over an `ℕ`-graded commutative ring
`k = ⨁ₙ 𝒜 n`, the units `tᵢⱼ` have degree `0` and the coefficient of `u^p v^q` in `Qᵢⱼ` for
`p < dᵢⱼ`, `q < dⱼᵢ` is homogeneous of degree `2(dᵢdᵢⱼ - dᵢp - dⱼq)`
(`coefficientDegree`).

* `BWWScalars.GradedHomogeneous`: this condition, on every monomial below the corners.
* `coefficientDegree_pos_of_pure`: the monomials with `p = 0` or `q = 0` below the corners have
  positive coefficient degree, by symmetrizability `dᵢdᵢⱼ = dⱼdⱼᵢ`.
* `Scalars.GradedHomogeneous.toBWW`: graded-homogeneous Brundan–Ellis parameters
  (`Scalars.GradedHomogeneous`, the same condition on the interior monomials) are
  graded-homogeneous Brundan–Wang–Webster parameters, and conversely
  (`Scalars.gradedHomogeneous_toBWW_iff`).
-/

noncomputable section

namespace OddMath.SKM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
variable {k : Type w} [CommRing k]

/-- The parameter condition of Brundan–Wang–Webster §2.2 over an `ℕ`-graded commutative ring:
`tᵢⱼ` in degree `0`, and each nonzero coefficient of `u^p v^q` with `p < dᵢⱼ`, `q < dⱼᵢ`
homogeneous of its coefficient degree. -/
def BWWScalars.GradedHomogeneous {σ : Type*} [SetLike σ k] (sy : Symmetrizer D) (𝒜 : ℕ → σ)
    (Sc : BWWScalars D k) : Prop :=
  (∀ i j, ((Sc.t i j : kˣ) : k) ∈ 𝒜 0) ∧
    ∀ i j (p q : ℕ), i ≠ j → (p : ℤ) < D.d i j → (q : ℤ) < D.d j i →
      Sc.c i j p q ≠ 0 → ∃ n : ℕ, (n : ℤ) = coefficientDegree sy i j p q ∧ Sc.c i j p q ∈ 𝒜 n

/-- Below the corners, the coefficient degree is positive when `p = 0` or `q = 0`. -/
theorem coefficientDegree_pos_of_pure (sy : Symmetrizer D) {i j : I} {p q : ℕ}
    (hp : (p : ℤ) < D.d i j) (hq : (q : ℤ) < D.d j i) (hpq : p = 0 ∨ q = 0) :
    0 < coefficientDegree sy i j p q := by
  have hsy := sy.symm i j
  have hi := sy.pos i
  have hj := sy.pos j
  unfold coefficientDegree
  rcases hpq with rfl | rfl
  · have : sy.d j * q < sy.d j * D.d j i := mul_lt_mul_of_pos_left hq hj
    push_cast
    linarith
  · have : sy.d i * p < sy.d i * D.d i j := mul_lt_mul_of_pos_left hp hi
    push_cast
    linarith

/-- Graded-homogeneous Brundan–Ellis parameters are graded-homogeneous Brundan–Wang–Webster
parameters, and conversely. -/
theorem Scalars.gradedHomogeneous_toBWW_iff {σ : Type*} [SetLike σ k] (sy : Symmetrizer D)
    (𝒜 : ℕ → σ) (Sc : Scalars D k) :
    Sc.toBWW.GradedHomogeneous sy 𝒜 ↔ Sc.GradedHomogeneous sy 𝒜 := by
  refine and_congr Iff.rfl ⟨fun h i j p q hp hp' hq hq' hs => ?_,
    fun h i j p q hij hp hq hs => ?_⟩
  · have hij : i ≠ j := by
      rintro rfl
      have := D.d_self i
      omega
    have hdn : (D.dn i j : ℤ) = D.d i j := D.dn_cast hij
    have hdn' : (D.dn j i : ℤ) = D.d j i := D.dn_cast (Ne.symm hij)
    have hc := ScalarData.toBWW_c_of_interior Sc hij hp (by omega) hq (by omega)
    rw [← hc] at hs ⊢
    exact h i j p q hij hp' hq' hs
  · have hdn : (D.dn i j : ℤ) = D.d i j := D.dn_cast hij
    have hdn' : (D.dn j i : ℤ) = D.d j i := D.dn_cast (Ne.symm hij)
    by_cases hpq : p = 0 ∨ q = 0
    · exact absurd (ScalarData.toBWW_c_eq_zero_of_pure Sc hij (by omega) (by omega) hpq) hs
    push Not at hpq
    have hc := ScalarData.toBWW_c_of_interior Sc hij (p := p) (q := q) (by omega) (by omega)
      (by omega) (by omega)
    rw [hc] at hs ⊢
    exact h i j p q (by omega) hp (by omega) hq hs

/-- Graded-homogeneous Brundan–Ellis parameters are graded-homogeneous Brundan–Wang–Webster
parameters. -/
theorem Scalars.GradedHomogeneous.toBWW {σ : Type*} [SetLike σ k] {sy : Symmetrizer D}
    {𝒜 : ℕ → σ} {Sc : Scalars D k} (h : Sc.GradedHomogeneous sy 𝒜) :
    Sc.toBWW.GradedHomogeneous sy 𝒜 :=
  (Scalars.gradedHomogeneous_toBWW_iff sy 𝒜 Sc).mpr h

end OddMath.SKM
