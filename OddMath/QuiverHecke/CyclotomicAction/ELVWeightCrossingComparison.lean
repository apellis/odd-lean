/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossing

/-! # Canonical content comparison for weight pair induction

The intermediate-content transport needed by `DeformedActionAssembly.md` §6
identifies the actual two-successor induction with the canonical successive
single-letter content induction. Its comparison with direct word induction
is coherent with the independently chosen content pair comparison.
-/

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

private theorem crossing_eqIso_whiskerLeft
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (K : C ⥤ B) {F G : B ⥤ E} (h : F = G) :
    Functor.isoWhiskerLeft K (eqToIso h) =
      eqToIso (congrArg (fun F => K ⋙ F) h) := by
  cases h
  rfl

section Content
variable (β : Multiset I) (i j : I) (δ γ : Multiset I)
  (hδ : β + ([i] : Multiset I) = δ)
  (hγ : δ + ([j] : Multiset I) = γ)
  (h : β + ([i,j] : Multiset I) = γ)

/-- Replacing the intermediate content by its prescribed value identifies the
whole composite, without changing the chosen final content. -/
theorem contentPairInductionTo_eq :
    contentInductionTo D Sc cutoff bound β [i] δ hδ ⋙
        contentInductionTo D Sc cutoff bound δ [j] γ hγ =
      contentEPairTo D Sc cutoff bound β i j γ h := by
  subst δ
  rfl

/-- The direct-word comparison commutes with the literal intermediate-content
equality, rather than choosing a second associativity comparison. -/
theorem contentPairComparisonTo_hom :
    (contentInductionCompTo D Sc cutoff bound β [i] δ hδ [j] γ hγ h).hom =
      eqToHom (contentPairInductionTo_eq D Sc cutoff bound β i j δ γ hδ hγ h) ≫
        (contentEPairToComparison D Sc cutoff bound β i j γ h).hom := by
  subst δ
  change _ = 𝟙 _ ≫ _
  simp only [Category.id_comp]
  rfl

end Content

section Weight
variable (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- The actual block pair, with its stored intermediate successor, is the
canonical pair at the same final content. -/
theorem elvBlockPairCanonical_eq (β : WeightBlocks D Λ x₀) :
    (elvBlockPairInd D Sc cutoff bound i j Λ h₁ h₂ β).toFunctor =
      contentEPairTo D Sc cutoff bound β.1 j i
        (blockSucc₂ D i j Λ h₁ h₂ β).1
        (elvBlockPair_content_eq D i j Λ h₁ h₂ β) :=
  contentPairInductionTo_eq D Sc cutoff bound β.1 j i
    (blockSucc D Λ j h₁ β).1 (blockSucc₂ D i j Λ h₁ h₂ β).1
    (elvBlockSucc_content_eq D j Λ h₁ β)
    (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β))
    (elvBlockPair_content_eq D i j Λ h₁ h₂ β)

theorem elvBlockPairComparison_hom (β : WeightBlocks D Λ x₀) :
    (elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β).hom =
      eqToHom (elvBlockPairCanonical_eq D Sc cutoff bound i j Λ h₁ h₂ β) ≫
        (contentEPairToComparison D Sc cutoff bound β.1 j i
          (blockSucc₂ D i j Λ h₁ h₂ β).1
          (elvBlockPair_content_eq D i j Λ h₁ h₂ β)).hom :=
  contentPairComparisonTo_hom D Sc cutoff bound β.1 j i
    (blockSucc D Λ j h₁ β).1 (blockSucc₂ D i j Λ h₁ h₂ β).1
    (elvBlockSucc_content_eq D j Λ h₁ β)
    (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β))
    (elvBlockPair_content_eq D i j Λ h₁ h₂ β)

theorem elvBlockPairComparison_eq (β : WeightBlocks D Λ x₀) :
    elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β =
      eqToIso (elvBlockPairCanonical_eq D Sc cutoff bound i j Λ h₁ h₂ β) ≪≫
        contentEPairToComparison D Sc cutoff bound β.1 j i
          (blockSucc₂ D i j Λ h₁ h₂ β).1
          (elvBlockPair_content_eq D i j Λ h₁ h₂ β) := by
  apply Iso.ext
  exact elvBlockPairComparison_hom D Sc cutoff bound i j Λ h₁ h₂ β

/-- The actual weight-product coordinate is the independent canonical content
pair, preceded by evaluation at the unique source block. -/
theorem elvEFunctor_comp₂_contentPair_eq (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    elvEFunctor D Sc cutoff bound j Λ h₁ ⋙
        (elvInductionComponent D Sc cutoff bound i Λ h₂ ε).toFunctor =
      (elvBlockEval D Sc cutoff bound Λ β).toFunctor ⋙
        contentEPairTo D Sc cutoff bound β.1 j i ε.1
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε) := by
  subst ε
  exact (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β).trans
    (congrArg (fun F => (elvBlockEval D Sc cutoff bound Λ β).toFunctor ⋙ F)
      (elvBlockPairCanonical_eq D Sc cutoff bound i j Λ h₁ h₂ β))

/-- Comparison coherence is first proved on whole functors, before evaluating
the large product-induction objects. -/
theorem elvWeightPairComparison_eq (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε =
      eqToIso (elvEFunctor_comp₂_contentPair_eq D Sc cutoff bound i j Λ h₁ h₂ β ε hε) ≪≫
        Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
          (contentEPairToComparison D Sc cutoff bound β.1 j i ε.1
            (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)) := by
  subst ε
  change eqToIso (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) ≪≫
      Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
        (elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β) = _
  rw [elvBlockPairComparison_eq, Functor.isoWhiskerLeft_trans,
    crossing_eqIso_whiskerLeft, ← Iso.trans_assoc, eqToIso_trans]

end Weight
end OddMath.QuiverHecke.ELVOld
