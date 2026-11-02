/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightModules
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleRelations

/-! # Actual two-successor ELV induction and absent-sector support

The actual product induction coordinate is compared to its two actual block
inductions, with their stored intermediate content retained. The even direct
induction comparison supplies the supported crossing interface. No finite
weight-fibre hypothesis or change of block-successor convention is used.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The source-to-successor content equality, with the actual successor retained. -/
theorem elvBlockSucc_content_eq (i : I) (Λ : X) {x y : X}
    (h : x + D.α i = y) (β : WeightBlocks D Λ x) :
    β.1 + ([i] : Multiset I) = (blockSucc D Λ i h β).1 := by
  rw [blockSucc_val, add_comm]
  rfl

section Pair
variable (i j : I) (Λ : X) {x₀ x₁ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)

/-- Both actual block inductions, before comparison to block induction by a word. -/
abbrev elvBlockPairInd (β : WeightBlocks D Λ x₀) :=
  (elvBlockInd D Sc cutoff bound j Λ h₁ β).comp
    (elvBlockInd D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β))

theorem elvBlockPair_content_eq (β : WeightBlocks D Λ x₀) :
    β.1 + ([j,i] : Multiset I) = (blockSucc₂ D i j Λ h₁ h₂ β).1 := by
  change β.1 + (([j] : Multiset I) + ([i] : Multiset I)) =
    ([i] : Multiset I) + (([j] : Multiset I) + β.1)
  ac_rfl

/-- The supported comparison uses the true first intermediate content. -/
def elvBlockPairComparison (β : WeightBlocks D Λ x₀) :
    (elvBlockPairInd D Sc cutoff bound i j Λ h₁ h₂ β).toFunctor ≅
      contentInductionTo D Sc cutoff bound β.1 [j,i]
        (blockSucc₂ D i j Λ h₁ h₂ β).1
        (elvBlockPair_content_eq D i j Λ h₁ h₂ β) :=
  contentInductionCompTo D Sc cutoff bound β.1 [j]
    (blockSucc D Λ j h₁ β).1 (elvBlockSucc_content_eq D j Λ h₁ β)
    [i] (blockSucc₂ D i j Λ h₁ h₂ β).1
    (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β))
    (elvBlockPair_content_eq D i j Λ h₁ h₂ β)

theorem elvBlockPairComparison_mem (β : WeightBlocks D Λ x₀)
    (M : ContentModules D Sc cutoff bound β.1) :
    EvenComparisonAt (k := k) (elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β) M :=
  contentInductionCompTo_mem D Sc cutoff bound β.1 [j]
    (blockSucc D Λ j h₁ β).1 (elvBlockSucc_content_eq D j Λ h₁ β)
    [i] (blockSucc₂ D i j Λ h₁ h₂ β).1
    (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β))
    (elvBlockPair_content_eq D i j Λ h₁ h₂ β) M

/-- Literal coordinate of the composed product induction at a double successor. -/
theorem elvEFunctor_comp₂_blockSucc (β : WeightBlocks D Λ x₀) :
    elvEFunctor D Sc cutoff bound j Λ h₁ ⋙
        (elvInductionComponent D Sc cutoff bound i Λ h₂
          (blockSucc₂ D i j Λ h₁ h₂ β)).toFunctor =
      (elvBlockEval D Sc cutoff bound Λ β).toFunctor ⋙
        (elvBlockPairInd D Sc cutoff bound i j Λ h₁ h₂ β).toFunctor := by
  rw [elvInductionComponent_blockSucc]
  change (elvInductionComponent D Sc cutoff bound j Λ h₁
      (blockSucc D Λ j h₁ β)).toFunctor ⋙
    (elvBlockInd D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).toFunctor = _
  rw [elvInductionComponent_blockSucc]
  rfl

/-- An absent double predecessor gives the actual zero coordinate, including
when only the inner predecessor is absent. -/
theorem elvEFunctor_comp₂_isZero (ε : WeightBlocks D Λ x₃)
    (hε : ¬ ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    Limits.IsZero ((elvEFunctor D Sc cutoff bound j Λ h₁ ⋙
      (elvInductionComponent D Sc cutoff bound i Λ h₂ ε).toFunctor).obj M) := by
  by_cases hγ : ∃ γ, blockSucc D Λ i h₂ γ = ε
  · obtain ⟨γ, rfl⟩ := hγ
    have hz : Limits.IsZero ((elvEFunctor D Sc cutoff bound j Λ h₁).obj M γ) :=
      elvInductionComponent_isZero D Sc cutoff bound j Λ h₁ γ
        (fun ⟨β, hβ⟩ => hε ⟨β, by rw [blockSucc₂, hβ]⟩) M
    exact Limits.IsZero.of_iso
      ((elvBlockInd D Sc cutoff bound i Λ h₂ γ).toFunctor.map_isZero hz)
      (eqToIso (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₂ γ _))
  · exact elvInductionComponent_isZero D Sc cutoff bound i Λ h₂ ε hγ _

end Pair
end OddMath.QuiverHecke.ELVOld
