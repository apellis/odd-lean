/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightTripleInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDistinctCrossing

/-! # Common stored targets for three OLD probe inductions

Brundan–Ellis (1.9): identify each supported product coordinate with its
three chosen append-to inductions at a specified final stored target.
This retains both intermediate canonical blocks and permits comparison
of different orders of three inductions in the same output category.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)

/-- The last append reaches the specified stored output list. -/
theorem probeOldTripleUpper_perm (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₃)
    (hε : probeOldBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε) :
    (i :: (blockSucc₂ D j l Λ h₁ h₂ β).1.toList).Perm ε.1.toList := by
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.coe_toList]
  change {i} + ((blockSucc₂ D j l Λ h₁ h₂ β).1.toList : Multiset I) = ε.1
  rw [Multiset.coe_toList]
  exact congrArg Subtype.val hε

/-- The last coefficient append retains the common final stored target. -/
abbrev probeOldTripleUpperAppend (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₃)
    (hε : probeOldBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε) :=
  oldContentAppendTo D Sc (probeCutoff D m) (blockSucc₂ D j l Λ h₁ h₂ β).1.toList i ε.1.toList
    (probeOldTripleUpper_perm D i j l Λ h₁ h₂ h₃ β ε hε)

/-- Three selected block inductions, with the specified common final stored target. -/
abbrev probeOldBlockTripleIndTo (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₃)
    (hε : probeOldBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε) :=
  (probeOldBlockPairInd D Sc m j l Λ h₁ h₂ β).comp
    (⟨probeEvaluatedAppendTo D Sc m (blockSucc₂ D j l Λ h₁ h₂ β).1.toList i ε.1.toList
      (probeOldTripleUpper_perm D i j l Λ h₁ h₂ h₃ β ε hε)⟩ :
      Superfunctor k (ProbeCanonicalModules D Sc m (blockSucc₂ D j l Λ h₁ h₂ β).1)
        (ProbeCanonicalModules D Sc m ε.1))

/-- The global triple coordinate is the three selected stored-target inductions. -/
theorem probeOldEFunctor_comp₃_to (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₃)
    (hε : probeOldBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε) :
    (probeOldEFunctor D Sc m l Λ h₁ ⋙ probeOldEFunctor D Sc m j Λ h₂) ⋙
      (probeOldInductionComponent D Sc m i Λ h₃ ε).toFunctor =
    (probeOldBlockEval D Sc m Λ β).toFunctor ⋙
      (probeOldBlockTripleIndTo D Sc m i j l Λ h₁ h₂ h₃ β ε hε).toFunctor := by
  subst ε
  exact probeOldEFunctor_comp₃_blockSucc D Sc m i j l Λ h₁ h₂ h₃ β

/-- The entire supported output object uses the same selected triple coordinate. -/
theorem probeOldWeightTripleTo_obj_eq (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₃)
    (hε : probeOldBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldEFunctor D Sc m l Λ h₁ ⋙ probeOldEFunctor D Sc m j Λ h₂) ⋙
      (probeOldInductionComponent D Sc m i Λ h₃ ε).toFunctor).obj M =
      (probeOldBlockTripleIndTo D Sc m i j l Λ h₁ h₂ h₃ β ε hε).obj (M β) :=
  congrArg (fun H => H.obj M) (probeOldEFunctor_comp₃_to D Sc m i j l Λ h₁ h₂ h₃ β ε hε)

end OddMath.QuiverHecke
