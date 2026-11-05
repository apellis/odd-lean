/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightSlides
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightMixedSlides

/-!
# Distinct-colour dot slides on the global weight factors

Brundan–Ellis, *Super Kac–Moody 2-categories* (arXiv:1701.04133v2), relation (1.8) for
`i ≠ j`: a dot slides through the crossing of two distinct colours, with the sign
`(-1)^{|i||j|}`. Here it is proved for the cyclotomic global action on weight factors.

* `heightContentMixedSlideLeft`, `heightContentMixedSlideRight`: the slides on content blocks,
  with arbitrary height and content transports, from the height-level slides
  `heightInduction_slide_left_ne`, `heightInduction_slide_right_ne`.
* `globalActionCross_slide_left_ne`, `globalActionCross_slide_right_ne`: the slides for the
  weight-level crossing, with the Koszul sign.
* `globalActionSignedCross_slide_left_ne`, `globalActionSignedCross_slide_right_ne`: the
  `slideLeft` and `slideRight` fields of `RouquierMulticolour` for the crossing of
  `globalRouquierData`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

omit [Fintype I] in

section Content
variable {i j : I} (hij : i ≠ j)
include hij

attribute [local irreducible] ContentSupported

end Content

section WeightTransport
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

end WeightTransport

section Weight
variable {i j : I} (hij : i ≠ j) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃) (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)
include hij

variable [DecidableEq I]

end Weight

end OddMath.QuiverHecke.CyclotomicAction
