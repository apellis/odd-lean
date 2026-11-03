/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightCrossCoordinates

/-! # Chosen OLD weight paths through common intermediate blocks

Brundan–Ellis (1.9): retain every selected intermediate and final content
in the product coordinates. The pair and triple identifications allow
the two braid paths to use the same stored vertices independently of the
order of induction.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
attribute [local irreducible] ELVOld.BalancedInduction.induced
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

/-- The selected block dot is the prescribed signed dot on the stored append. -/
theorem probeOldBlockDot_stored_total (i : I) (Λ : X) {a b : X}
    (h : a + D.α i = b) (β : WeightBlocks D Λ a) (N : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockDot D Sc m i Λ h β).total N =
      probeAppendToDotComponent D Sc m β.1.toList i (blockSucc D Λ i h β).1.toList
        (probeOldBlockTarget_perm D i Λ h β _ rfl) N :=
  probeAppendToInductionDot_total D Sc m β.1.toList i (blockSucc D Λ i h β).1.toList _ N

/-- The selected weight dot retains the full component at any supported stored target. -/
theorem probeOldActionDot_via_total (i : I) (Λ : X) {a b : X} (h : a + D.α i = b)
    (β : WeightBlocks D Λ a) (δ : WeightBlocks D Λ b) (hδ : blockSucc D Λ i h β = δ)
    (M : ProbeOldWeightProduct D Sc m Λ a) :
    (probeOldActionDot D Sc m i Λ h).total M δ =
      eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h β δ hδ M) ≫
        probeAppendToDotComponent D Sc m β.1.toList i δ.1.toList
          (probeOldBlockTarget_perm D i Λ h β δ hδ) (M β) ≫
      eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h β δ hδ M).symm := by
  subst δ
  change probeOldWeightDotComponent D Sc m i Λ h 0 M _ +
    probeOldWeightDotComponent D Sc m i Λ h 1 M _ = _
  rw [probeOldWeightDotComponent_blockSucc, probeOldWeightDotComponent_blockSucc]
  rw [← Preadditive.comp_add, ← Preadditive.add_comp]
  exact congrArg (fun f : End ((probeOldBlockInd D Sc m i Λ h β).obj (M β)) =>
    eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M) ≫ f ≫
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm)
    (probeOldBlockDot_stored_total D Sc m i Λ h β (M β))

section Pair
variable (i j : I) (Λ : X) {a b c : X}
  (h₁ : a + D.α j = b) (h₂ : b + D.α i = c)
  (β : WeightBlocks D Λ a) (δ : WeightBlocks D Λ b) (ε : WeightBlocks D Λ c)
  (hδ : blockSucc D Λ j h₁ β = δ) (hε : blockSucc D Λ i h₂ δ = ε)

/-- The two append-to functors along the specified supported intermediate block. -/
abbrev probeOldBlockPairVia :=
  (probeOldBlockIndTo D Sc m j Λ h₁ β δ hδ).comp
    (probeOldBlockIndTo D Sc m i Λ h₂ δ ε hε)

/-- The entire pair coordinate retains its specified intermediate and final blocks. -/
theorem probeOldEFunctor_comp₂_via :
    probeOldEFunctor D Sc m j Λ h₁ ⋙ (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor =
      (probeOldBlockEval D Sc m Λ β).toFunctor ⋙
        (probeOldBlockPairVia D Sc m i j Λ h₁ h₂ β δ ε hδ hε).toFunctor := by
  subst ε
  subst δ
  exact probeOldEFunctor_comp₂_blockSucc D Sc m i j Λ h₁ h₂ β

theorem probeOldWeightPairVia_obj_eq (M : ProbeOldWeightProduct D Sc m Λ a) :
    (probeOldEFunctor D Sc m j Λ h₁ ⋙ (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor).obj M =
      (probeOldBlockPairVia D Sc m i j Λ h₁ h₂ β δ ε hδ hε).obj (M β) :=
  congrArg (fun F => F.obj M) (probeOldEFunctor_comp₂_via D Sc m i j Λ h₁ h₂ β δ ε hδ hε)
end Pair

section Triple
variable (i j l : I) (Λ : X) {a b c d : X}
  (h₁ : a + D.α l = b) (h₂ : b + D.α j = c) (h₃ : c + D.α i = d)
  (β : WeightBlocks D Λ a) (δ₁ : WeightBlocks D Λ b)
  (δ₂ : WeightBlocks D Λ c) (ε : WeightBlocks D Λ d)
  (hδ₁ : blockSucc D Λ l h₁ β = δ₁) (hδ₂ : blockSucc D Λ j h₂ δ₁ = δ₂)
  (hε : blockSucc D Λ i h₃ δ₂ = ε)

/-- Three chosen append-to functors through the specified stored vertices. -/
abbrev probeOldBlockTripleVia :=
  (probeOldBlockPairVia D Sc m j l Λ h₁ h₂ β δ₁ δ₂ hδ₁ hδ₂).comp
    (probeOldBlockIndTo D Sc m i Λ h₃ δ₂ ε hε)

/-- The entire triple coordinate retains both specified intermediate blocks. -/
theorem probeOldEFunctor_comp₃_via :
    (probeOldEFunctor D Sc m l Λ h₁ ⋙ probeOldEFunctor D Sc m j Λ h₂) ⋙
        (probeOldInductionComponent D Sc m i Λ h₃ ε).toFunctor =
      (probeOldBlockEval D Sc m Λ β).toFunctor ⋙
        (probeOldBlockTripleVia D Sc m i j l Λ h₁ h₂ h₃ β δ₁ δ₂ ε hδ₁ hδ₂ hε).toFunctor := by
  subst ε
  subst δ₂
  subst δ₁
  exact probeOldEFunctor_comp₃_blockSucc D Sc m i j l Λ h₁ h₂ h₃ β

theorem probeOldWeightTripleVia_obj_eq (M : ProbeOldWeightProduct D Sc m Λ a) :
    ((probeOldEFunctor D Sc m l Λ h₁ ⋙ probeOldEFunctor D Sc m j Λ h₂) ⋙
      (probeOldInductionComponent D Sc m i Λ h₃ ε).toFunctor).obj M =
      (probeOldBlockTripleVia D Sc m i j l Λ h₁ h₂ h₃ β δ₁ δ₂ ε hδ₁ hδ₂ hε).obj (M β) :=
  congrArg (fun F => F.obj M)
    (probeOldEFunctor_comp₃_via D Sc m i j l Λ h₁ h₂ h₃ β δ₁ δ₂ ε hδ₁ hδ₂ hε)
end Triple

private theorem path_total_smul {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (a : k) (f : F ⟶ G) (N : C) :
    (a • f).total N = a • f.total N := by
  change a • f.app 0 N + a • f.app 1 N = a • (f.app 0 N + f.app 1 N)
  exact (smul_add _ _ _).symm

attribute [local irreducible] probeAppendToCrossComponent
section Crossing
variable (i j : I) (Λ : X) {a bj bi d : X}
  (h₁ : a + D.α j = bj) (h₂ : bj + D.α i = d)
  (h₃ : a + D.α i = bi) (h₄ : bi + D.α j = d)
  (β : WeightBlocks D Λ a) (δj : WeightBlocks D Λ bj)
  (δi : WeightBlocks D Λ bi) (ε : WeightBlocks D Λ d)
  (hj : blockSucc D Λ j h₁ β = δj) (hi : blockSucc D Λ i h₃ β = δi)
  (hU : blockSucc D Λ i h₂ δj = ε) (hL : blockSucc D Λ j h₄ δi = ε)

/-- The selected crossing has its prescribed component at all four specified stored vertices. -/
theorem probeOldActionCross_via_total (M : ProbeOldWeightProduct D Sc m Λ a) :
    (probeOldActionCross D Sc m Λ i j h₁ h₂ h₃ h₄).total M ε =
      eqToHom (probeOldWeightPairVia_obj_eq D Sc m i j Λ h₁ h₂ β δj ε hj hU M) ≫
        ((if i = j then (-1 : k) else 1) • probeAppendToCrossComponent D Sc m β.1.toList j i
          (probeOldBlockTarget_perm D i Λ h₃ β δi hi)
          (probeOldBlockTarget_perm D j Λ h₁ β δj hj)
          (probeOldBlockTarget_perm D j Λ h₄ δi ε hL)
          (probeOldBlockTarget_perm D i Λ h₂ δj ε hU) (M β)) ≫
      eqToHom (probeOldWeightPairVia_obj_eq D Sc m j i Λ h₃ h₄ β δi ε hi hL M).symm := by
  subst δj
  subst δi
  rw [probeOldActionCross_eq_normalized_distinct, path_total_smul]
  change (if i = j then (-1 : k) else 1) •
    (probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).total M ε = _
  rw [probeOldActionDistinctCross_total_of D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hU M,
    probeOldBlockDistinctCross_stored_total]
  rw [Linear.smul_comp, Linear.comp_smul]
end Crossing
end OddMath.QuiverHecke
