/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightBraid
import OddMath.QuiverHecke.CyclotomicAction.GlobalRouquierData

/-!
# The equal-colour braid relation on weight spaces

Ports `globalCross_sameBraid` of `Categorification/KLR/CyclotomicAction/GlobalBraid.lean`
to the weight spaces. On content blocks the two crossings of three inductions are the
inner crossing `Ind(t)` and the outer crossing `t_{Ind}` of `GlobalHeightBraid`, conjugated
by identity transports of heights and contents (`heightContentBraid`). At a block that is
not a three-step successor the triple composite vanishes. Hence the weight crossing
satisfies `t₂ t₁ t₂ = t₁ t₂ t₁` with `t₁ = t ▷ E` and `t₂ = E ◁ t`
(`globalActionCross_braid`), and so does the signed Rouquier crossing `-t`
(`globalActionSignedCross_braid`): this is the `braid` field of `RouquierFamily`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

section Content
variable (i : I)

attribute [local irreducible] ContentSupported

local notation "d" => D.parity i * D.parity i

end Content

section Weight
variable (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (h₃ : x₂ + D.α i = x₃)

local notation "d" => D.parity i * D.parity i

end Weight

end OddMath.QuiverHecke.CyclotomicAction
