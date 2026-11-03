/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightModules
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightCross

/-! # Supported and absent two-step OLD probe induction

`SwappedActionAssembly` F2: identify the actual two global OLD probe
induction coordinates with their stored-target block inductions. An absent
double predecessor contributes the actual zero evaluated module, including
when the first predecessor alone is absent. No weight-fibre finiteness or
coefficient-power quotient is used.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
universe u
namespace OddMath.QuiverHecke
open ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

section Pair
variable (i j : I) (Λ : X) {x₀ x₁ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)

/-- Both actual block inductions, retaining their chosen intermediate content. -/
abbrev probeOldBlockPairInd (β : WeightBlocks D Λ x₀) :=
  (probeOldBlockInd D Sc m j Λ h₁ β).comp
    (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ j h₁ β))

/-- Literal coordinate of the composed product induction at a double successor. -/
theorem probeOldEFunctor_comp₂_blockSucc (β : WeightBlocks D Λ x₀) :
    probeOldEFunctor D Sc m j Λ h₁ ⋙
        (probeOldInductionComponent D Sc m i Λ h₂
          (blockSucc₂ D i j Λ h₁ h₂ β)).toFunctor =
      (probeOldBlockEval D Sc m Λ β).toFunctor ⋙
        (probeOldBlockPairInd D Sc m i j Λ h₁ h₂ β).toFunctor := by
  rw [probeOldInductionComponent_blockSucc]
  change (probeOldInductionComponent D Sc m j Λ h₁
      (blockSucc D Λ j h₁ β)).toFunctor ⋙
    (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)).toFunctor = _
  rw [probeOldInductionComponent_blockSucc]
  rfl

/-- An absent double predecessor gives the actual zero coordinate, including
when only the inner predecessor is absent. -/
theorem probeOldEFunctor_comp₂_isZero (ε : WeightBlocks D Λ x₃)
    (hε : ¬ ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    Limits.IsZero ((probeOldEFunctor D Sc m j Λ h₁ ⋙
      (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor).obj M) := by
  by_cases hγ : ∃ γ, blockSucc D Λ i h₂ γ = ε
  · obtain ⟨γ, rfl⟩ := hγ
    have hz : Limits.IsZero ((probeOldEFunctor D Sc m j Λ h₁).obj M γ) :=
      probeOldInductionComponent_isZero D Sc m j Λ h₁ γ
        (fun ⟨β, hβ⟩ => hε ⟨β, by rw [blockSucc₂, hβ]⟩) M
    exact Limits.IsZero.of_iso
      ((probeOldBlockInd D Sc m i Λ h₂ γ).toFunctor.map_isZero hz)
      (eqToIso (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ γ _))
  · exact probeOldInductionComponent_isZero D Sc m i Λ h₂ ε hγ _

end Pair
end OddMath.QuiverHecke
