/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVEndEvaluation
import OddMath.SKM.RouquierMateSectors

/-! # The quadratic two-morphism of the original-weight action

Brundan--Ellis (1.7), DeformedActionAssembly §6 (9): evaluate the actual
weight crossing and two whiskered weight dots on every module and output.
The ordered polynomial retains the original scalar parameters.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

theorem elvActionCross_quadratic (hij : i ≠ j) :
    elvActionCross D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ h₃ h₄ ≫
      elvActionCross D (parameterTwist D Sc) cutoff bound j i Λ h₃ h₄ h₁ h₂ =
    orderedPairOperatorPolynomial (R := End
      (elvE D (parameterTwist D Sc) cutoff bound j Λ h₁ ≫
        elvE D (parameterTwist D Sc) cutoff bound i Λ h₂)) D Sc j i
      (elvActionDot D (parameterTwist D Sc) cutoff bound j Λ h₁ ▷
        elvE D (parameterTwist D Sc) cutoff bound i Λ h₂)
      (elvE D (parameterTwist D Sc) cutoff bound j Λ h₁ ◁
        elvActionDot D (parameterTwist D Sc) cutoff bound i Λ h₂) := by
  apply moduleFamily_polynomial_of_components
  intro M ε w
  rw [supernatural_total_of_mem
      (elvActionCross_mem D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ h₃ h₄) M,
    supernatural_total_of_mem
      (elvActionCross_mem D (parameterTwist D Sc) cutoff bound j i Λ h₃ h₄ h₁ h₂) M,
    supernatural_total_of_mem
      (TwoSupercategory.whiskerRight_mem
        (elvE D (parameterTwist D Sc) cutoff bound i Λ h₂)
        (elvActionDot_mem D (parameterTwist D Sc) cutoff bound j Λ h₁)) M,
    supernatural_total_of_mem
      (TwoSupercategory.whiskerLeft_mem
        (elvE D (parameterTwist D Sc) cutoff bound j Λ h₁)
        (elvActionDot_mem D (parameterTwist D Sc) cutoff bound i Λ h₂)) M]
  exact elvWeightCrossComponent_quadratic_total D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij M ε w
/-- The disconnected field of the native multicolour presentation. -/
theorem elvActionCross_quadZero (hij : i ≠ j) (hd : D.d i j = 0) :
    elvActionCross D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ h₃ h₄ ≫
      elvActionCross D (parameterTwist D Sc) cutoff bound j i Λ h₃ h₄ h₁ h₂ =
      (Sc.t i j : k) • 𝟙 _ := by
  rw [elvActionCross_quadratic D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij]
  simp only [orderedPairOperatorPolynomial, (D.d_eq_zero_iff i j).mp hd, ite_true]
  rw [Sc.t_symm_of_d_eq_zero j i ((D.d_eq_zero_iff i j).mp hd)]
  rfl

/-- The connected field, in the exact whiskered order of RouquierMulticolour. -/
theorem elvActionCross_quadNe (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    elvActionCross D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ h₃ h₄ ≫
      elvActionCross D (parameterTwist D Sc) cutoff bound j i Λ h₃ h₄ h₁ h₂ =
      (Sc.t i j : k) • (elvE D (parameterTwist D Sc) cutoff bound j Λ h₁ ◁
        SKM.rouquierPower (elvActionDot D (parameterTwist D Sc) cutoff bound i Λ h₂) (D.dn i j)) +
      (Sc.t j i : k) • (SKM.rouquierPower
        (elvActionDot D (parameterTwist D Sc) cutoff bound j Λ h₁) (D.dn j i) ▷
        elvE D (parameterTwist D Sc) cutoff bound i Λ h₂) +
      ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
        Sc.s i j p q • (SKM.rouquierPower
          (elvActionDot D (parameterTwist D Sc) cutoff bound j Λ h₁) q ▷
          elvE D (parameterTwist D Sc) cutoff bound i Λ h₂ ≫
          elvE D (parameterTwist D Sc) cutoff bound j Λ h₁ ◁
          SKM.rouquierPower (elvActionDot D (parameterTwist D Sc) cutoff bound i Λ h₂) p) := by
  rw [elvActionCross_quadratic D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij]
  have hd' : D.d j i ≠ 0 := fun h => hd ((D.d_eq_zero_iff i j).mpr h)
  have hL (n : ℕ) := SKM.whiskerLeft_rouquierPower (k := k)
    (B := PiSCat.{u, u, u + 1} k)
    (elvE D (parameterTwist D Sc) cutoff bound j Λ h₁)
    (elvActionDot D (parameterTwist D Sc) cutoff bound i Λ h₂) n
  have hR (n : ℕ) := SKM.whiskerRight_rouquierPower (k := k)
    (B := PiSCat.{u, u, u + 1} k)
    (elvActionDot D (parameterTwist D Sc) cutoff bound j Λ h₁)
    (elvE D (parameterTwist D Sc) cutoff bound i Λ h₂) n
  simp only [orderedPairOperatorPolynomial, hd', ite_false]
  simp_rw [hL, hR]
  simp only [End.mul_def]
  rw [Finset.sum_comm]
  simp only [Sc.s_symm j i]
  abel
end OddMath.QuiverHecke.ELVOld
