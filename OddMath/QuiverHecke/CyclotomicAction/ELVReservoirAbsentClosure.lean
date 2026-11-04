import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosures

/-! # Vanishing of reservoir closures at absent predecessors

The source-coefficient closure calculation of ReservoirClosureDegree also
covers blocks without a lower predecessor. The literal chosen closure
factors through the zero lower induction component, independently of the
principal inverse choice and all dot powers.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirClosures
open CyclotomicAction
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (δ : WeightBlocks D Λ x₁)
  (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ)
include hδ

/-- The actual positive chosen closure vanishes on every absent predecessor
block, for every input family and every pair of dot powers. -/
theorem positive_total_absent (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M δ = 0 := by
  have hz := elvInductionComponent_isZero D Sc cutoff N i Λ h₁ δ hδ
    ((elvF D Sc cutoff N i Λ h₁).obj M)
  have hc : (elvActionAdjunction D Sc cutoff N i Λ h₁).counit.total M δ = 0 := hz.eq_of_src _ 0
  dsimp only [positive, elvRouquierFamily, elvRouquierData]
  simp only [Superfunctor.comp_total, Pi.comp_apply]
  rw [hc, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero]

/-- The actual negative chosen closure has the same absent-block vanishing. -/
theorem negative_total_absent (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M δ = 0 := by
  have hz := elvInductionComponent_isZero D Sc cutoff N i Λ h₁ δ hδ
    ((elvF D Sc cutoff N i Λ h₁).obj M)
  have hc : (elvActionAdjunction D Sc cutoff N i Λ h₁).counit.total M δ = 0 := hz.eq_of_src _ 0
  dsimp only [negative, elvRouquierFamily, elvRouquierData]
  simp only [Superfunctor.comp_total, Pi.comp_apply]
  rw [hc, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero]

end OddMath.QuiverHecke.ELVOld.ReservoirClosures
