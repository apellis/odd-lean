/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightNilHeckeRelation

/-! # The prescribed local Rouquier action on weight products

BE (1.13)–(1.14): combine the selected weight adjunctions, dots, crossing,
signed slides and constructed local inverse families. No factor-action
or local-inverse existence assumption is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

/-- The selected weight fields form the local Rouquier data with their
actual categorical height and both constructed inverse presentations. -/
theorem elvWeightRouquierLocal_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) :
    Nonempty (SKM.SuperRouquierLoc
      (elvActionAdjunction D Sc cutoff N i Λ h₁)
      (elvActionAdjunction D Sc cutoff N i Λ h₂)
      (elvActionDot D Sc cutoff N i Λ h₁)
      (elvActionDot D Sc cutoff N i Λ h₂)
      (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
      (D.parity i) (D.h i x₁)) := by
  refine ⟨{
    dot₁_mem := elvActionDot_mem D Sc cutoff N i Λ h₁
    dot₂_mem := elvActionDot_mem D Sc cutoff N i Λ h₂
    cross_mem := ?_
    slide_left := elvActionCross_slideLeft D Sc cutoff N i Λ h₁ h₂
    slide_right := elvActionCross_slideRight D Sc cutoff N i Λ h₁ h₂
    invPos := fun hh => Classical.choice
      (elvWeightLocalCapFamily_nonempty D Sc cutoff N i Λ h₁ h₂ hcutoff hh)
    invNeg := fun hh => Classical.choice
      (elvWeightLocalUnitFamily_nonempty D Sc cutoff N i Λ h₁ h₂ hcutoff hh) }⟩
  simpa only [SKM.zmod2_mul_self] using
    elvActionCross_mem D Sc cutoff N i i Λ h₁ h₂ h₁ h₂

end OddMath.QuiverHecke.ELVOld
