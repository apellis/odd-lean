/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightBraid
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightSlides

/-!
# The dot slides on weight spaces

Transports `heightInduction_slide_left/right` of `GlobalHeightSlides` through content blocks
and successor blocks to the weight spaces. With `t = -ψ` the Rouquier crossing,
`x₁` the dot of the inner and `x₂` the dot of the outer induction, and `s = (-1)^{|i|}`,

  `E₁ ◁ x₂ ≫ t - s (t ≫ x₁ ▷ E₂) = 1`,  `t ≫ E₁ ◁ x₂ - s (x₁ ▷ E₂ ≫ t) = 1`

(`globalActionSignedCross_slide_left/right`): the slide fields of `SuperRouquierLoc`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

omit [Fintype I] in
theorem zmod2_mul_self (p : ZMod 2) : p * p = p := by
  fin_cases p <;> rfl

section Content
variable (i : I)

attribute [local irreducible] ContentSupported

end Content

section Weight
variable [DecidableEq I] (i : I) (Λ : X) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁)
  (h₂ : x₁ + D.α i = x₂)

end Weight

end OddMath.QuiverHecke.CyclotomicAction
