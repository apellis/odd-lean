/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairInduction

/-! # The normalized crossing on full-ELV weight induction

Advances `DeformedActionAssembly.md` §6. The crossing acts on the existing
weight-product induction functors. On a supported block it is the normalized
content crossing transported by the canonical even two-successor induction
comparison. On an absent double predecessor its source is zero. Naturality
retains the Koszul sign for arbitrary homogeneous input-module maps, without
a finite weight-fibre or finite-colour premise.

The chosen affine representative retains the equal-colour minus sign. Pair
and triple whiskering relations on these weight functors are separate.
-/

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

private theorem crossingComparison_eq_mem
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} (h : F = G) (M : C) :
    EvenComparisonAt (k := k) (eqToIso h) M := by
  cases h
  exact ⟨id_mem _, id_mem _⟩

private theorem crossingComparison_trans_mem
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G H : C ⥤ B} (e : F ≅ G) (f : G ≅ H) (M : C)
    (he : EvenComparisonAt (k := k) e M) (hf : EvenComparisonAt (k := k) f M) :
    EvenComparisonAt (k := k) (e ≪≫ f) M :=
  ⟨comp_mem he.1 hf.1, comp_mem hf.2 he.2⟩

section Pair
variable (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- The literal source-content equality for a supported double successor. -/
theorem elvWeightPair_content_eq (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    β.1 + ([j,i] : Multiset I) = ε.1 :=
  (elvBlockPair_content_eq D i j Λ h₁ h₂ β).trans (congrArg Subtype.val hε)

/-- The comparison on an actual product-induction coordinate; its intermediate
content is the true first successor, not an unrelated supported model. -/
def elvWeightPairComparison (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    elvEFunctor D Sc cutoff bound j Λ h₁ ⋙
        (elvInductionComponent D Sc cutoff bound i Λ h₂ ε).toFunctor ≅
      (elvBlockEval D Sc cutoff bound Λ β).toFunctor ⋙
        contentInductionTo D Sc cutoff bound β.1 [j,i] ε.1
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε) := by
  subst ε
  exact eqToIso (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) ≪≫
    Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
      (elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β)

theorem elvWeightPairComparison_mem (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    EvenComparisonAt (k := k)
      (elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε) M := by
  subst ε
  exact crossingComparison_trans_mem _ _ M
    (crossingComparison_eq_mem _ M)
    (elvBlockPairComparison_mem D Sc cutoff bound i j Λ h₁ h₂ β (M β))

/-- At a chosen predecessor, the normalized content crossing acts on the
actual two weight-induction coordinates. -/
def elvWeightCrossVia (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    SuperNatTrans k
      (elvEFunctor D Sc cutoff bound j Λ h₁ ⋙
        (elvInductionComponent D Sc cutoff bound i Λ h₂ ε).toFunctor)
      (elvEFunctor D Sc cutoff bound i Λ h₃ ⋙
        (elvInductionComponent D Sc cutoff bound j Λ h₄ ε).toFunctor) :=
  (evenComparison_supernatural
    (elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε)
    (elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
    (elvWeightPairComparison_mem D Sc cutoff bound i j Λ h₁ h₂ β ε hε)
    (elvWeightPairComparison_mem D Sc cutoff bound j i Λ h₃ h₄ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
    (((contentInductionTransform D Sc cutoff bound
      (elvWeightPair_content_eq D j i Λ h₃ h₄ β ε
        (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
      (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
      (contentCrossAffine_mem D Sc i j)).isSupernatural
        (D.parity i * D.parity j)).whiskerLeft
          (elvBlockEval D Sc cutoff bound Λ β).toFunctor)).toSuperNatTrans

theorem elvWeightCrossVia_homogeneous (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    (elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε).IsHomogeneous
      (D.parity i * D.parity j) :=
  IsSupernatural.toSuperNatTrans_isHomogeneous _

/-- The crossing is the prescribed content map in the chosen two-successor
coordinates, including the normalized equal-colour representative. -/
theorem elvWeightCrossVia_component (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε).app
        (D.parity i * D.parity j) M =
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound
          (elvWeightPair_content_eq D j i Λ h₃ h₄ β ε
            (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (contentCrossAffine_mem D Sc i j)).app (D.parity i * D.parity j) (M β)) ≫
        (elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε
          (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε)).inv.app M :=
  congrFun (IsSupernatural.toSuperNatTrans_app _) M

theorem elvWeightCrossVia_eq (β β' : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (hε' : blockSucc₂ D i j Λ h₁ h₂ β' = ε) :
    elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε =
      elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β' ε hε' := by
  obtain rfl := blockSucc₂_injective D i j Λ h₁ h₂ (hε.trans hε'.symm)
  rfl

/-- The crossing component is zero where no double predecessor exists. -/
def elvWeightCrossComponent (p : ZMod 2)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (ε : WeightBlocks D Λ x₃) :
    (elvEFunctor D Sc cutoff bound j Λ h₁ ⋙
        (elvInductionComponent D Sc cutoff bound i Λ h₂ ε).toFunctor).obj M ⟶
      (elvEFunctor D Sc cutoff bound i Λ h₃ ⋙
        (elvInductionComponent D Sc cutoff bound j Λ h₄ ε).toFunctor).obj M :=
  if hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε then
    (elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄
      hε.choose ε hε.choose_spec).app p M
  else 0

theorem elvWeightCrossComponent_of (p : ZMod 2)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M ε =
      (elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε).app p M := by
  unfold elvWeightCrossComponent
  split
  · rename_i hc
    rw [elvWeightCrossVia_eq D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄
      hc.choose β ε hc.choose_spec hε]
  · rename_i hc
    exact absurd ⟨β, hε⟩ hc

theorem elvWeightCrossComponent_absent (p : ZMod 2)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (ε : WeightBlocks D Λ x₃)
    (hε : ¬ ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M ε = 0 := by
  simp only [elvWeightCrossComponent, dite_eq_right hε]

theorem elvWeightCrossComponent_mem (p : ZMod 2)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (ε : WeightBlocks D Λ x₃) :
    elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M ε ∈
      parity (R := k) _ _ p := by
  unfold elvWeightCrossComponent
  split
  · exact SuperNatTrans.app_mem _ p M
  · exact Submodule.zero_mem _

theorem elvWeightCrossComponent_naturality (p : ZMod 2) (ε : WeightBlocks D Λ x₃)
    {M M' : ELVWeightProduct D Sc cutoff bound Λ x₀} {q : ZMod 2} (f : M ⟶ M')
    (hf : f ∈ parity (R := k) M M' q) :
    (elvEFunctor D Sc cutoff bound j Λ h₁ ⋙
        (elvInductionComponent D Sc cutoff bound i Λ h₂ ε).toFunctor).map f ≫
        elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M' ε =
      koszulSign p q •
        (elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M ε ≫
          (elvEFunctor D Sc cutoff bound i Λ h₃ ⋙
            (elvInductionComponent D Sc cutoff bound j Λ h₄ ε).toFunctor).map f) := by
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [elvWeightCrossComponent_of D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M β ε hβ,
      elvWeightCrossComponent_of D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M' β ε hβ]
    exact (elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hβ).naturality p f hf
  · exact (elvEFunctor_comp₂_isZero D Sc cutoff bound i j Λ h₁ h₂ ε hε M).eq_of_src _ _

/-- The normalized crossing on the existing full-ELV product categories. -/
def elvWeightCross :
    SuperNatTrans k
      (elvEFunctor D Sc cutoff bound j Λ h₁ ⋙ elvEFunctor D Sc cutoff bound i Λ h₂)
      (elvEFunctor D Sc cutoff bound i Λ h₃ ⋙ elvEFunctor D Sc cutoff bound j Λ h₄) where
  app p M ε := elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M ε
  app_mem p M ε := elvWeightCrossComponent_mem D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M ε
  naturality p _ _ _ f hf := funext fun ε =>
    elvWeightCrossComponent_naturality D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p ε f hf

theorem elvWeightCross_supported (p : ZMod 2)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    (elvWeightCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app p M ε =
      (elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε).app p M :=
  elvWeightCrossComponent_of D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M β ε hε

theorem elvWeightCross_homogeneous :
    (elvWeightCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).IsHomogeneous
      (D.parity i * D.parity j) := by
  intro q hq
  funext M ε
  change elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ q M ε = 0
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [elvWeightCrossComponent_of D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ q M β ε hβ]
    exact congrFun (elvWeightCrossVia_homogeneous D Sc cutoff bound i j Λ
      h₁ h₂ h₃ h₄ β ε hβ q hq) M
  · exact elvWeightCrossComponent_absent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ q M ε hε

/-- The crossing as a two-morphism of the actual action target. -/
def elvActionCross :
    elvE D Sc cutoff bound j Λ h₁ ≫ elvE D Sc cutoff bound i Λ h₂ ⟶
      elvE D Sc cutoff bound i Λ h₃ ≫ elvE D Sc cutoff bound j Λ h₄ :=
  elvWeightCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄

theorem elvActionCross_mem :
    elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  Superfunctor.mem_parity_iff_isHomogeneous.2
    (elvWeightCross_homogeneous D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄)

end Pair
end OddMath.QuiverHecke.ELVOld
