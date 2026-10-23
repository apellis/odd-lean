/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.PreF.GaugeForm
import LieLean.Algebra.QuantumGroup.GabberKac.VermaOperator

/-!
# Raising operators on the free half algebra

For bicharacters `χ`, `ψ` on `I` with `ψ(i, j) χ(i, j) = 1` for all `j`, and scalars `a`, `b`,
the operator `E = a σ'ᵢ ∘ ᵢr - b rᵢ` on `'f` (`σ'ᵢ` the twist of `ψ`, `ᵢr`, `rᵢ` the skew
derivations of `χ`) satisfies `E(θⱼ y) = θⱼ E(y) + δᵢⱼ c(μ) y` for `y ∈ 'f_μ`, with
`c(μ) = a ψ(i, μ) - b χ(i, μ)` (`PreF.raiseOp_θ_mul`). So it is the Verma-type operator of
`LieLean` with these coefficients (`PreF.raiseOp_eq_vermaOp`). When `(θᵢ, θᵢ)` is a unit for
every `i`, these operators preserve the radical of the form, hence the Shapovalov-type pairings
`ε(E_w y)` vanish on the radical (`PreF.vermaForm_eq_zero_of_mem_radical`).

For the covering bicharacter `χ(i, j) = q^{-i·j} π^{|i||j|}` with `π² = 1`, `ψ` is the covering
bicharacter at `q⁻¹`, and suitable `a`, `b` make `E` the action of `Eᵢ` on a Verma module of the
covering quantum group pulled back to `'f`; the coefficients are computed in
`OddMath.CoveringQuantum.SuperCount.Coefficients`. The argument is the one used for Lusztig's
`'f` in `LieLean` (`LusztigF.vermaOpQ_eq_vermaOp`), carried out for an arbitrary bicharacter.

## Main definitions

* `PreF.raiseOp χ ψ a b i`.

## Main results

* `PreF.raiseOp_θ_mul`, `PreF.raiseOp_eq_vermaOp`, `PreF.raiseOp_mem_radical`,
  `PreF.vermaForm_eq_zero_of_mem_radical`.
-/

noncomputable section

namespace OddMath.CoveringQuantum

namespace PreF

open FreeAlgebra

variable {k I : Type*} [CommRing k] [DecidableEq I] (χ ψ : Bichar k I)

/-- The raising operator `E = a σ'ᵢ ∘ ᵢr - b rᵢ`, with `σ'ᵢ` the twist of `ψ` and `ᵢr`, `rᵢ`
the skew derivations of `χ`. -/
def raiseOp (a b : k) (i : I) : Module.End k (PreF k I) :=
  a • ((twist ψ i).toLinearMap ∘ₗ lDeriv χ i) - b • rDeriv χ i

lemma raiseOp_apply (a b : k) (i : I) (y : PreF k I) :
    raiseOp χ ψ a b i y = a • twist ψ i (lDeriv χ i y) - b • rDeriv χ i y := rfl

variable {χ ψ}

/-- The recursion `E(θⱼ y) = θⱼ E(y) + δᵢⱼ (a σ'ᵢ(y) - b σᵢ(y))`. -/
theorem raiseOp_θ_mul {i : I} (hψ : ∀ j, ψ i j * χ i j = 1) (a b : k) (j : I) (y : PreF k I) :
    raiseOp χ ψ a b i (θ k j * y) = θ k j * raiseOp χ ψ a b i y +
      if i = j then a • twist ψ i y - b • twist χ i y else 0 := by
  rw [raiseOp_apply, raiseOp_apply, lDeriv_θ_mul, rDeriv_θ_mul, map_add, map_smul, map_mul,
    twist_θ, smul_mul_assoc, smul_smul, mul_comm (χ i j), hψ j, one_smul]
  split_ifs
  · simp only [smul_add, mul_sub, mul_smul_comm]; abel
  · simp only [mul_sub, mul_smul_comm, add_zero, map_zero, zero_add]

omit [DecidableEq I] in
/-- On the word `w` the twist `σᵢ` is multiplication by `χ(i, |w|)`. -/
lemma twist_wordBasis (i : I) (w : List I) :
    twist χ i (wordBasis k I w) = χ.wt (Finsupp.single i 1) (LusztigF.wordWeight w) •
      wordBasis k I w := by
  have h : wordBasis k I w = monomial k w := by rw [wordBasis_apply]; rfl
  rw [h]
  exact twist_of_mem i (monomial_mem_weightSpace w)

/-- `E` is the Verma-type operator with coefficients `c(μ) = a ψ(i, μ) - b χ(i, μ)`. -/
theorem raiseOp_eq_vermaOp {i : I} (hψ : ∀ j, ψ i j * χ i j = 1) (a b : k) :
    raiseOp χ ψ a b i = LusztigF.vermaOp i fun μ ↦
      a * ψ.wt (Finsupp.single i 1) μ - b * χ.wt (Finsupp.single i 1) μ := by
  refine (wordBasis k I).ext fun w ↦ ?_
  induction w with
  | nil =>
    rw [LusztigF.vermaOp_wordBasis, wordBasis_nil, raiseOp_apply]
    simp [LusztigF.vermaOpWord]
  | cons j w ih =>
    rw [← ι_mul_wordBasis, LusztigF.vermaOp_ι_mul, ← ih, LusztigF.weightScale_wordBasis]
    erw [raiseOp_θ_mul hψ a b j (wordBasis k I w)]
    rw [twist_wordBasis, twist_wordBasis, smul_smul, smul_smul, ← sub_smul]

variable (χ ψ) {nm : I → k}

/-- The raising operators preserve the radical when `(θᵢ, θᵢ)` is a unit. -/
theorem raiseOp_mem_radical (a b : k) {i : I} (hi : IsUnit (nm i)) {y : PreF k I}
    (hy : y ∈ radical χ nm) : raiseOp χ ψ a b i y ∈ radical χ nm := by
  have hsm : ∀ (c : k) {z : PreF k I}, z ∈ radical χ nm → c • z ∈ radical χ nm :=
    fun c z hz ↦ by rw [Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hz
  have htw : ∀ {z : PreF k I}, z ∈ radical χ nm → twist ψ i z ∈ radical χ nm := fun {z} hz ↦ by
    rw [mem_radical_iff']
    intro x
    rw [twist, ← form_diagTwist, (mem_radical_iff' χ nm).1 hz]
  rw [raiseOp_apply]
  exact TwoSidedIdeal.sub_mem _ (hsm _ (htw (lDeriv_mem_radical χ nm hi hy)))
    (hsm _ (rDeriv_mem_radical χ nm hi hy))

/-- **The Shapovalov-type pairings vanish on the radical.** If `ψ(i, j) χ(i, j) = 1` and
`(θᵢ, θᵢ)` is a unit for all `i, j`, then `ε(E_w y) = 0` for every word `w` and every `y` in the
radical, where `E_w` is the composite of the raising operators `E = aᵢ σ'ᵢ ∘ ᵢr - bᵢ rᵢ`. -/
theorem vermaForm_eq_zero_of_mem_radical (hψ : ∀ i j, ψ i j * χ i j = 1)
    (hnm : ∀ i, IsUnit (nm i)) (a b : I → k) (w : List I) {y : PreF k I}
    (hy : y ∈ radical χ nm) :
    LusztigF.vermaForm (fun i μ ↦ a i * ψ.wt (Finsupp.single i 1) μ -
      b i * χ.wt (Finsupp.single i 1) μ) w y = 0 := by
  suffices h : ∀ w (y : PreF k I), y ∈ radical χ nm →
      LusztigF.vermaWordOp (fun i μ ↦ a i * ψ.wt (Finsupp.single i 1) μ -
        b i * χ.wt (Finsupp.single i 1) μ) w y ∈ radical χ nm by
    rw [LusztigF.vermaForm_apply, ← form_one_right χ nm]
    exact (mem_radical_iff χ nm).1 (h w y hy) 1
  intro w
  induction w with
  | nil => intro y hy; exact hy
  | cons i w ih =>
    intro y hy
    rw [LusztigF.vermaWordOp_cons]
    refine ih _ ?_
    rw [← raiseOp_eq_vermaOp (hψ i)]
    exact raiseOp_mem_radical χ ψ _ _ (hnm i) hy

end PreF

end OddMath.CoveringQuantum
