/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightQuadraticComponents

/-! # Same-colour crossing squares on every weight block

DeformedActionAssembly §6 and Brundan--Ellis (1.9): the prescribed weight
crossing has square zero, including absent double predecessors.
-/

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

theorem contentInductionTransform_square_total_to (β : Multiset I) (i : I)
    (γ : Multiset I) (hγ : β + ([i,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    let f := ((contentInductionTransform D Sc cutoff bound hγ hγ
      (contentCrossAffine_mem D Sc i i)).app (D.parity i * D.parity i) M).total w
    f.comp f = 0 := by
  dsimp only
  simp only [contentInductionTransform_total]
  subst γ
  exact contentInductionCross_square_linear D Sc cutoff bound β i M w

variable (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

theorem elvWeightCrossVia_square_total (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₂) (hε : blockSucc₂ D i i Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    let f := ((elvWeightCrossVia D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β ε hε).app
      (D.parity i * D.parity i) M).total w
    f.comp f = 0 := by
  dsimp only
  have h := elvWeightCrossVia_composite_total D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β ε hε M w
  dsimp only at h
  rw [contentInductionTransform_square_total_to] at h
  simpa only [map_zero] using h

/-- The given same-colour global crossing has square zero at every actual
output block, with no predecessor or nonvanishing hypothesis. -/
theorem elvWeightCrossComponent_square_total
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (ε : WeightBlocks D Λ x₂)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    let f := (elvWeightCrossComponent D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
      (D.parity i * D.parity i) M ε).total w
    f.comp f = 0 := by
  dsimp only
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    simp only [elvWeightCrossComponent_of D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
      (D.parity i * D.parity i) M β _ rfl]
    exact elvWeightCrossVia_square_total D Sc cutoff bound i Λ h₁ h₂ β _ rfl M w
  · rw [elvWeightCrossComponent_total_absent D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
      (D.parity i * D.parity i) M ε hε w]
    exact LinearMap.zero_comp _

end OddMath.QuiverHecke.ELVOld
