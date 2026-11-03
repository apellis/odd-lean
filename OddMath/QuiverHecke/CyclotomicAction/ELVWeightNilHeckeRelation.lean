/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightNilHecke

/-! # Native signed slides of the original-weight action

Brundan--Ellis (1.8), DeformedActionAssembly §6: the actual independently
whiskered dots and crossing obey both local signed slides as two-morphisms.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
section Evaluation
variable {k : Type u} [CommRing k] {C : Type*} [Category* C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {J : Type u} {A : J → Type u}
  [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
  [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
  {F : Superfunctor k C (∀ j, Superfunctor k (A j) (SVec k))}

private theorem moduleFamily_slide_of_components
    (a b c d : End F) (s : k)
    (h : ∀ M t w, ModuleNilHeckeSlide
      (a.total M t) (b.total M t) (c.total M t) (d.total M t) w s) :
    b ≫ a - s • (d ≫ c) = 𝟙 F := by
  apply moduleFamilyEndEvaluation_ext
  intro M t w
  change (moduleFamilyEndEvaluation F M t w) (a * b - s • (c * d)) =
    (moduleFamilyEndEvaluation F M t w) 1
  rw [map_sub, map_mul, map_smul, map_mul, map_one]
  exact h M t w
end Evaluation

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

theorem elvActionCross_slideLeft :
    (elvE D Sc cutoff bound i Λ h₁ ◁ elvActionDot D Sc cutoff bound i Λ h₂) ≫ elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ - koszulSign (D.parity i) (D.parity i) •
      (elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ ≫ (elvActionDot D Sc cutoff bound i Λ h₁ ▷ elvE D Sc cutoff bound i Λ h₂)) = 𝟙 _ := by
  rw [koszulSign_smul (R := k)]
  apply moduleFamily_slide_of_components
  intro M ε w
  rw [supernatural_total_of_mem
      (elvActionCross_mem D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂) M,
    supernatural_total_of_mem
      (TwoSupercategory.whiskerRight_mem (elvE D Sc cutoff bound i Λ h₂)
        (elvActionDot_mem D Sc cutoff bound i Λ h₁)) M,
    supernatural_total_of_mem
      (TwoSupercategory.whiskerLeft_mem (elvE D Sc cutoff bound i Λ h₁)
        (elvActionDot_mem D Sc cutoff bound i Λ h₂)) M]
  exact elvWeightCrossComponent_slideLeft D Sc cutoff bound i Λ h₁ h₂ M ε w

theorem elvActionCross_slideRight :
    elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ ≫ (elvE D Sc cutoff bound i Λ h₁ ◁ elvActionDot D Sc cutoff bound i Λ h₂) - koszulSign (D.parity i) (D.parity i) •
      ((elvActionDot D Sc cutoff bound i Λ h₁ ▷ elvE D Sc cutoff bound i Λ h₂) ≫ elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂) = 𝟙 _ := by
  rw [koszulSign_smul (R := k)]
  apply moduleFamily_slide_of_components
  intro M ε w
  rw [supernatural_total_of_mem
      (elvActionCross_mem D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂) M,
    supernatural_total_of_mem
      (TwoSupercategory.whiskerRight_mem (elvE D Sc cutoff bound i Λ h₂)
        (elvActionDot_mem D Sc cutoff bound i Λ h₁)) M,
    supernatural_total_of_mem
      (TwoSupercategory.whiskerLeft_mem (elvE D Sc cutoff bound i Λ h₁)
        (elvActionDot_mem D Sc cutoff bound i Λ h₂)) M]
  exact elvWeightCrossComponent_slideRight D Sc cutoff bound i Λ h₁ h₂ M ε w

end OddMath.QuiverHecke.ELVOld
