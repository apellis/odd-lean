/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDistinctSlides

/-! # Native distinct-colour dot slides

Brundan--Ellis (1.8), the two distinct-colour fields of
RouquierMulticolour on the prescribed original-weight generators.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
section Totals
variable {k : Type u} [CommRing k] {C B : Type*} [Category* C] [Category* B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
private theorem supernatural_total_smul {F G : Superfunctor k C B}
    (s : k) (c : F ⟶ G) (M : C) : (s • c).total M = s • c.total M :=
  (supernaturalTotalLinearMap F G M).map_smul s c
end Totals

section Evaluation
variable {k : Type u} [CommRing k] {C : Type*} [Category* C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {J : Type u} {A : J → Type u}
  [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
  [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
  {F G : Superfunctor k C (∀ j, Superfunctor k (A j) (SVec k))}
private theorem moduleFamily_crossSlide_of_components
    (c : F ⟶ G) (x : F ⟶ F) (y : G ⟶ G) (s : k)
    (h : ∀ M t w, ModuleCrossSlide (c.total M t) (x.total M t) (y.total M t) w s) :
    x ≫ c = s • (c ≫ y) := by
  apply supernatural_hom_ext_total
  intro M
  rw [Superfunctor.comp_total, supernatural_total_smul, Superfunctor.comp_total]
  funext t
  change x.total M t ≫ c.total M t = s • (c.total M t ≫ y.total M t)
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total, supernatural_total_smul, Superfunctor.comp_total]
  exact h M t w
end Evaluation

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

theorem elvActionCross_slideLeft_distinct (hij : i ≠ j) :
    elvE D Sc cutoff bound j Λ h₁ ◁ elvActionDot D Sc cutoff bound i Λ h₂ ≫
      elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ =
    SKM.zsign k (D.parity i * D.parity j) •
      (elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ ≫
        elvActionDot D Sc cutoff bound i Λ h₃ ▷ elvE D Sc cutoff bound j Λ h₄) := by
  rw [← sign_eq_zsign]
  apply moduleFamily_crossSlide_of_components
  intro M ε w
  rw [supernatural_total_of_mem (elvActionCross_mem D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄) M,
    supernatural_total_of_mem (TwoSupercategory.whiskerLeft_mem
      (elvE D Sc cutoff bound j Λ h₁) (elvActionDot_mem D Sc cutoff bound i Λ h₂)) M,
    supernatural_total_of_mem (TwoSupercategory.whiskerRight_mem
      (elvE D Sc cutoff bound j Λ h₄) (elvActionDot_mem D Sc cutoff bound i Λ h₃)) M]
  exact elvWeightDistinct_slideLeft_component D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij M ε w

theorem elvActionCross_slideRight_distinct (hij : i ≠ j) :
    elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ ≫
      elvE D Sc cutoff bound i Λ h₃ ◁ elvActionDot D Sc cutoff bound j Λ h₄ =
    SKM.zsign k (D.parity i * D.parity j) •
      (elvActionDot D Sc cutoff bound j Λ h₁ ▷ elvE D Sc cutoff bound i Λ h₂ ≫
        elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄) := by
  have h : elvActionDot D Sc cutoff bound j Λ h₁ ▷ elvE D Sc cutoff bound i Λ h₂ ≫
      elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ =
      sign k (D.parity i * D.parity j) •
        (elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ ≫
          elvE D Sc cutoff bound i Λ h₃ ◁ elvActionDot D Sc cutoff bound j Λ h₄) := by
    apply moduleFamily_crossSlide_of_components
    intro M ε w
    rw [supernatural_total_of_mem (elvActionCross_mem D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄) M,
      supernatural_total_of_mem (TwoSupercategory.whiskerRight_mem
        (elvE D Sc cutoff bound i Λ h₂) (elvActionDot_mem D Sc cutoff bound j Λ h₁)) M,
      supernatural_total_of_mem (TwoSupercategory.whiskerLeft_mem
        (elvE D Sc cutoff bound i Λ h₃) (elvActionDot_mem D Sc cutoff bound j Λ h₄)) M]
    exact elvWeightDistinct_slideRight_component D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij M ε w
  rw [← sign_eq_zsign]
  have hh := congrArg (fun z => sign k (D.parity i * D.parity j) • z) h
  simpa only [smul_smul, Supercategory.sign_mul_self, one_smul] using hh.symm
end OddMath.QuiverHecke.ELVOld
