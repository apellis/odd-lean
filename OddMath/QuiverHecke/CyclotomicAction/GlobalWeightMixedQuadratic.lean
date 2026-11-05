/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightMixedSlides
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightMixedInductionSquare
import OddMath.QuiverHecke.CyclotomicAction.GlobalRouquierMateKernel
import OddMath.QuiverHecke.CyclotomicAction.GlobalRouquierData

/-!
# The distinct-colour quadratic relation on the global weight factors

Brundan–Ellis, *Super Kac–Moody 2-categories* (arXiv:1701.04133v2), relation (1.7) for
`i ≠ j`, for the cyclotomic global action on weight factors, with the parameters of
`parameterTwist`.

* `heightContentMixedSquareNe`, `heightContentMixedSquareZero`: the relation on content
  blocks, with arbitrary height and content transports, from `heightInduction_square_ne`,
  `heightInduction_square_zero`.
* `globalActionCross_square_ne`, `globalActionCross_square_zero`: the relation for the
  weight-level crossings.
* `globalActionSignedCross_square_ne`, `globalActionSignedCross_square_zero`: the `quadNe` and
  `quadZero` fields of `RouquierMulticolour` for the crossing of `globalRouquierData`, with the
  scalars `parameterTwist D Sc`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

/-! ### Powers of endomorphisms -/

section EndoPower

end EndoPower

/-! ### Components in `𝔖ℭ𝔞𝔱` and in products -/

section Components
variable {A B : SCat k}

omit [Fintype I] in

end Components

section ContentHom
variable (i : I) (n : ℕ) (β : Multiset I)

end ContentHom

/-! ### Content blocks -/

section Content
variable {i j : I} (hij : i ≠ j)
include hij

attribute [local irreducible] ContentSupported SuperBimodule.tensor

end Content

omit [Fintype I] in

/-! ### Weight level -/

section Weight
variable {i j : I} (hij : i ≠ j) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃) (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)
include hij

attribute [local irreducible] ContentSupported SuperBimodule.tensor

omit hij in

omit hij in

omit hij in

variable [DecidableEq I]

end Weight

end OddMath.QuiverHecke.CyclotomicAction
