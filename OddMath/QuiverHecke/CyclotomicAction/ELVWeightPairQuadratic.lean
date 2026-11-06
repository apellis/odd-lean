/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairCrossingTotals
import OddMath.QuiverHecke.CyclotomicAction.ELVContentOperatorQuadratic

/-! # The weight crossing square in the selected pair coordinates

DeformedActionAssembly §6 (9) requires the original parameter polynomial
at the actual output content, before attaching the two independent weight
dots. The content endpoint is arbitrary, with its specified equality.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The ordered operator polynomial at a specified common content endpoint. -/
def contentInductionPairPolynomialTo (β : Multiset I) (i j : I)
    (γ : Multiset I) (hγ : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D (parameterTwist D Sc) cutoff bound β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff bound γ) :=
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff bound hγ hγ
      (firstDot_parity D (parameterTwist D Sc) i [j])) M w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff bound hγ hγ
      (contentPairDot_one_parity D (parameterTwist D Sc) i j)) M w
  if D.d i j = 0 then (Sc.t i j : k) • (1 : Module.End k _) else
    ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
      Sc.s i j r s • (B ^ s * A ^ r) +
    ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

/-- Both prescribed crossings give the original-Sc polynomial at any chosen
common endpoint. No equality of module objects is assumed. -/
theorem contentInduction_quadratic_linear_to (β : Multiset I) {i j : I}
    (hij : i ≠ j) (γ : Multiset I)
    (hγ : β + ([i,j] : Multiset I) = γ)
    (hγ' : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D (parameterTwist D Sc) cutoff bound β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff bound γ) :
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff bound hγ hγ'
        (contentCrossAffine_mem D (parameterTwist D Sc) i j)) M w).comp
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff bound hγ' hγ
          (contentCrossAffine_mem D (parameterTwist D Sc) j i)) M w) =
      contentInductionPairPolynomialTo D Sc cutoff bound β i j γ hγ M w := by
  subst γ
  exact contentInduction_quadratic_linear D Sc cutoff bound β hij M w

variable (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- On every supported output block, the two given weight crossings have
the original-Sc ordered polynomial in their selected source coordinates.
Identification of its positioned dots with the independent weight dots is
a separate step. -/
theorem elvWeightCrossVia_quadratic_total (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₃)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D (parameterTwist D Sc) cutoff bound Λ x₀)
    (w : ContentCategory D (parameterTwist D Sc) cutoff bound ε.1) :
    let hε' := blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε
    let hs := elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε
    let e := moduleIsoLinearEquiv
      ((elvWeightPairComparison D (parameterTwist D Sc) cutoff bound
        i j Λ h₁ h₂ β ε hε).app M) w
    (((elvWeightCrossVia D (parameterTwist D Sc) cutoff bound
        j i Λ h₃ h₄ h₁ h₂ β ε hε').app
        (D.parity j * D.parity i) M).total w).comp
      (((elvWeightCrossVia D (parameterTwist D Sc) cutoff bound
        i j Λ h₁ h₂ h₃ h₄ β ε hε).app
        (D.parity i * D.parity j) M).total w) =
      e.symm.conjAlgEquiv k
        (contentInductionPairPolynomialTo D Sc cutoff bound β.1 j i ε.1 hs (M β) w) := by
  dsimp only
  rw [elvWeightCrossVia_composite_total]
  congr 1
  rw [contentInductionTransform_total, contentInductionTransform_total]
  exact contentInduction_quadratic_linear_to D Sc cutoff bound β.1 hij.symm ε.1 _ _ (M β) w

end OddMath.QuiverHecke.ELVOld
