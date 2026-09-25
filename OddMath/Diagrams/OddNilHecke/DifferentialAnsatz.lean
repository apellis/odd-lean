import OddMath.Diagrams.OddNilHecke.Differential
import OddMath.Diagrams.OddNilHecke.Action

/-!
# Which local ansatz is compatible with the odd nilHecke relations

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*,
arXiv:1504.01712v2, §3.2, ansatz (3.6)–(3.7), constraints (3.8)–(3.10) and their solution
(3.11), Proposition 3.3.

Ellis–Qi consider a differential on `ONH_2` with `d(x_i) = x_i²` and, for degree reasons,

  `d(∂) = a + b x ∂ + c y ∂`

((3.7); `x ∂` is the crossing with a dot at the top of the left strand, `y ∂` with a dot at
the top of the right strand). **Proposition 3.3 as printed** assumes that this differential is
the one induced from a dg module structure `OPol_n(α)` on the skew polynomial representation
((3.2)–(3.3)), and derives `a = α + β = 1`, `b = c = 0` ((3.11)) from the constraints (3.8)–(3.10)
obtained by differentiating `∂ · 1 = 0`, `∂(x · 1) = 1`, `∂(y · 1) = 1`.

This file proves an **intrinsic variant**, not the printed statement: it asks which values
`(a, b, c)` make the local assignment `δ(dot) = x²`, `δ(crossing) = a + b x₀∂ + c x₁∂`
compatible with the defining relations of the diagrammatic odd nilHecke category itself, so
that it descends to a derivation of `ONH` (no polynomial representation or `α` is involved in
the hypothesis). Over `ℤ` the answer is the same as in Proposition 3.3:
`ansatz_compatible_iff`: compatible `↔ a = 1 ∧ b = 0 ∧ c = 0`.

The exact obstructions (over any commutative ring, in `OddMath.Diagrams.OddNilHecke.Differential`)
are

* square relation `ψ² = 0`: `d(ψ²) = -(b + c) ψ`;
* mixed relation `x₀ ψ + ψ x₁ = 1`: `(1 - a + b) x₀ + (a - 1 + c) x₁ - 2b x₀² ψ`;
* mixed relation `ψ x₀ + x₁ ψ = 1`: `(a - 1 + b) x₀ + (1 - a + c) x₁ - 2c x₁² ψ`.

The coefficients of `x₀` and `x₁` in the two mixed relations are the linear constraints
`a - b = 1`, `a + c = 1`, `a + b = 1`, `a - c = 1`; these are exactly the constraints
(3.9)–(3.10) of Ellis–Qi after substituting (3.8), `α + β = a` (the constraint (3.8) itself
has no intrinsic counterpart). The intrinsic computation also produces the conditions
`2b = 0`, `2c = 0` (coefficients of `x₀² ψ`, `x₁² ψ`) and `b + c = 0` (square relation). Over `ℤ` they force `a = 1`, `b = c = 0`; the necessity proof
uses only the two mixed relations, and detects the coefficients by acting on the constant
polynomial `1` in the faithful polynomial representation.
-/

noncomputable section

namespace OddMath.Diagrams.OddNilHecke

open CategoryTheory StringDiagrams
open OddMath.SkewPolynomial (SkewPolynomial generator expSingle)
open OddMath.Frontier NilHeckeAction

/-- The action on the constant polynomial `1` of `r • x₀ + s • x₁ - t • F`, where `F` ends
(acts first) with a crossing, is `r x₀ + s x₁`. -/
theorem realize_apply_one (r s t : ℤ) (F : End ((pres ℤ).obj (strands 2))) :
    realize 2 (r • x ℤ 2 0 + s • x ℤ 2 1 - t • (F * ψ ℤ 2 0)) 1 =
      r • generator (0 : Fin 2) + s • generator (1 : Fin 2) := by
  simp only [Algebra.smul_def, algebraMap_int_eq, Int.coe_castRingHom, map_sub, map_add,
    map_mul, map_intCast]
  have h0 := realize_x 0 (0 : Fin 2)
  have h1 := realize_x 0 (1 : Fin 2)
  have hψ := realize_ψ 0 (0 : Fin 1)
  simp only [Fin.val_zero, Fin.val_one, zero_add] at h0 h1 hψ
  rw [h0, h1, hψ]
  simp [AllRankDivided.divided_one, Module.End.intCast_apply]

theorem generator_apply_expSingle (i j : Fin 2) :
    (generator i : SkewPolynomial 2) (expSingle j) = if i = j then 1 else 0 := by
  have : expSingle i = expSingle j ↔ i = j := by
    constructor
    · intro h
      have := congrFun h i
      by_contra hij
      simp only [expSingle, if_true, if_neg (Ne.symm hij)] at this
      exact one_ne_zero this
    · rintro rfl; rfl
  simp only [generator, OddMath.SkewPolynomial.monomial, Finsupp.single_apply, this]

/-- Coefficient extraction: `r x₀ + s x₁ = 0` forces `r = s = 0`. -/
theorem eq_zero_of_smul_generator (r s : ℤ)
    (h : r • generator (0 : Fin 2) + s • generator (1 : Fin 2) = (0 : SkewPolynomial 2)) :
    r = 0 ∧ s = 0 := by
  have h0 := congrArg (fun f : SkewPolynomial 2 => f (expSingle (0 : Fin 2))) h
  have h1 := congrArg (fun f : SkewPolynomial 2 => f (expSingle (1 : Fin 2))) h
  simp only [Finsupp.add_apply, Finsupp.smul_apply, generator_apply_expSingle,
    Finsupp.coe_zero, Pi.zero_apply] at h0 h1
  simp at h0 h1
  exact ⟨h0, h1⟩

/-- **Intrinsic variant of Ellis–Qi, Proposition 3.3** (over `ℤ`). The local assignment
`δ(dot) = x²`, `δ(crossing) = a + b x₀∂ + c x₁∂` is compatible with the relations of the
diagrammatic odd nilHecke category (so descends to a derivation of `ONH ℤ`) if and only if
`a = 1` and `b = c = 0`, that is, `d(crossing) = 1`. -/
theorem ansatz_compatible_iff (a b c : ℤ) :
    (ansatz ℤ a b c).Compatible (pres ℤ) ↔ a = 1 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hR := h.rel .mixedRight
    have hL := h.rel .mixedLeft
    rw [lin_derivFree_mixedRight] at hR
    rw [lin_derivFree_mixedLeft] at hL
    have eR := congrArg (fun f => realize 2 f 1) hR
    have eL := congrArg (fun f => realize 2 f 1) hL
    simp only [← mul_assoc] at eR eL
    rw [realize_apply_one, map_zero, LinearMap.zero_apply] at eR eL
    obtain ⟨r1, r2⟩ := eq_zero_of_smul_generator _ _ eR
    obtain ⟨l1, l2⟩ := eq_zero_of_smul_generator _ _ eL
    omega
  · rintro ⟨rfl, rfl, rfl⟩
    exact compatible ℤ

end OddMath.Diagrams.OddNilHecke

end
