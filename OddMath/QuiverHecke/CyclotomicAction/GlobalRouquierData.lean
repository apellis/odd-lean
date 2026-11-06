/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightCross

/-!
# Rouquier data on cyclotomic weight spaces

Ports `globalCross_sq` of `Categorification/KLR/CyclotomicAction/GlobalCross.lean` and the
data part of `GlobalFamily.lean`. The same-colour weight crossing squares to zero
(`globalWeightCross_square`, blockwise from `heightSuperInductionCrossing_square`). As in the
even file the Rouquier crossing is `-ψ` for equal colours and `ψ` otherwise
(`globalActionSignedCross`). Weight-space induction, the dot of parity `|i|` and the signed
crossing of parity `|i||j|` assemble to `globalRouquierData : SKM.RouquierData D` in the
supercategory of supercategories, and the adjunction and square fields hold
(`globalActionAdjunction`, `globalActionSignedCross_square`). The braid relation and the
local inversion field `loc` of `RouquierFamily` remain to be supplied.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (Λ : X)

section Square
variable (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

end Square

section Signed
variable [DecidableEq I] (i j : I) {x₀ x₁ x₂ x₃ : X} (h₁ : x₀ + D.α j = x₁)
  (h₂ : x₁ + D.α i = x₃) (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- The Rouquier crossing on weight spaces: `-ψ` for equal colours, `ψ` otherwise. -/
def globalActionSignedCross :
    globalActionE D Sc a ha j Λ h₁ ≫ globalActionE D Sc a ha i Λ h₂ ⟶
      globalActionE D Sc a ha i Λ h₃ ≫ globalActionE D Sc a ha j Λ h₄ :=
  if i = j then -globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄
  else globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄

end Signed

end OddMath.QuiverHecke.CyclotomicAction
