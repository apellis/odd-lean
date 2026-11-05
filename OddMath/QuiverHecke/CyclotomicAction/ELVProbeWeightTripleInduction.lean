/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightPairInduction

/-! # Three-step OLD probe induction on original weights

Brundan–Ellis (1.9): retain all actual intermediate content blocks in
three successive OLD probe inductions. The literal product coordinate
is the selected block triple; absent triple predecessors have the actual
zero evaluated module, including missing inner predecessors.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)

/-- The actual block reached by the three successive inductions. -/
abbrev probeOldBlockSucc₃ (β : WeightBlocks D Λ x₀) : WeightBlocks D Λ x₃ :=
  blockSucc D Λ i h₃ (blockSucc₂ D j l Λ h₁ h₂ β)

/-- All three chosen block inductions, retaining both stored intermediate targets. -/
abbrev probeOldBlockTripleInd (β : WeightBlocks D Λ x₀) :=
  (probeOldBlockPairInd D Sc m j l Λ h₁ h₂ β).comp
    (probeOldBlockInd D Sc m i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β))

/-- The literal global triple coordinate is the selected actual block triple. -/
theorem probeOldEFunctor_comp₃_blockSucc (β : WeightBlocks D Λ x₀) :
    (probeOldEFunctor D Sc m l Λ h₁ ⋙ probeOldEFunctor D Sc m j Λ h₂) ⋙
      (probeOldInductionComponent D Sc m i Λ h₃
        (probeOldBlockSucc₃ D i j l Λ h₁ h₂ h₃ β)).toFunctor =
    (probeOldBlockEval D Sc m Λ β).toFunctor ⋙
      (probeOldBlockTripleInd D Sc m i j l Λ h₁ h₂ h₃ β).toFunctor := by
  rw [probeOldInductionComponent_blockSucc]
  change (probeOldEFunctor D Sc m l Λ h₁ ⋙
      (probeOldEFunctor D Sc m j Λ h₂ ⋙
        (probeOldBlockEval D Sc m Λ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor)) ⋙
      (probeOldBlockInd D Sc m i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor = _
  change (probeOldEFunctor D Sc m l Λ h₁ ⋙
      (probeOldInductionComponent D Sc m j Λ h₂ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor) ⋙
      (probeOldBlockInd D Sc m i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor = _
  rw [probeOldEFunctor_comp₂_blockSucc]
  rfl

/-- The selected equality on the entire supported output object. -/
theorem probeOldWeightTriple_obj_eq (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldEFunctor D Sc m l Λ h₁ ⋙ probeOldEFunctor D Sc m j Λ h₂) ⋙
      (probeOldInductionComponent D Sc m i Λ h₃
        (probeOldBlockSucc₃ D i j l Λ h₁ h₂ h₃ β)).toFunctor).obj M =
      (probeOldBlockTripleInd D Sc m i j l Λ h₁ h₂ h₃ β).obj (M β) :=
  congrArg (fun H => H.obj M) (probeOldEFunctor_comp₃_blockSucc D Sc m i j l Λ h₁ h₂ h₃ β)

/-- An absent triple predecessor gives the actual zero coordinate, at every input. -/
theorem probeOldEFunctor_comp₃_isZero (ε : WeightBlocks D Λ x₃)
    (hε : ¬ ∃ β, probeOldBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    Limits.IsZero (((probeOldEFunctor D Sc m l Λ h₁ ⋙ probeOldEFunctor D Sc m j Λ h₂) ⋙
      (probeOldInductionComponent D Sc m i Λ h₃ ε).toFunctor).obj M) := by
  by_cases hγ : ∃ γ, blockSucc D Λ i h₃ γ = ε
  · obtain ⟨γ, rfl⟩ := hγ
    have hz : Limits.IsZero ((probeOldEFunctor D Sc m l Λ h₁ ⋙
        (probeOldInductionComponent D Sc m j Λ h₂ γ).toFunctor).obj M) :=
      probeOldEFunctor_comp₂_isZero D Sc m j l Λ h₁ h₂ γ
        (fun ⟨β, hβ⟩ => hε ⟨β, by rw [probeOldBlockSucc₃, hβ]⟩) M
    exact Limits.IsZero.of_iso
      ((probeOldBlockInd D Sc m i Λ h₃ γ).toFunctor.map_isZero hz)
      (eqToIso (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₃ γ _))
  · exact probeOldInductionComponent_isZero D Sc m i Λ h₃ ε hγ _

end OddMath.QuiverHecke
