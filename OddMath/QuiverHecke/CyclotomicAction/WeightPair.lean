import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import OddMath.QuiverHecke.CyclotomicAction.ContentModule
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockExtension

/-!
# Weight pair

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
namespace OddMath.QuiverHecke.ELV
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
end OddMath.QuiverHecke.ELV
end

end

section

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
namespace OddMath.QuiverHecke.ELV
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
end OddMath.QuiverHecke.ELV
end

end

section

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
namespace OddMath.QuiverHecke.ELV
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
end OddMath.QuiverHecke.ELV
end

end

section

/-! # The normalized full-ELV dot on original-weight induction

The existing contentInductionDot is transported to the actual common successor
content, then assembled on the existing product of content module categories.
This construction asserts no uniform nilpotence exponent over a weight fibre.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open OddMath.QuiverHecke.CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The existing normalized content dot, with a specified common target. -/
abbrev elvContentDotTo (β γ : Multiset I) (hγ : β + ([i] : Multiset I) = γ) :=
  contentInductionTransform D Sc cutoff bound hγ hγ (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The normalized content dot between a block and its successor. -/
abbrev elvBlockDot (β : WeightBlocks D Λ x) :=
  elvContentDotTo D Sc cutoff bound i β.1 (blockSucc D Λ i h β).1
    (by rw [blockSucc_val, add_comm]; rfl)

theorem elvBlockDot_homogeneous (β : WeightBlocks D Λ x) :
    (elvBlockDot D Sc cutoff bound i Λ h β).IsHomogeneous (D.parity i) := by
  exact (BalancedInduction.transformComponent_supernatural
    (contentAppendTo_supernatural D Sc cutoff bound
      (by rw [blockSucc_val, add_comm]; rfl)
      (by rw [blockSucc_val, add_comm]; rfl)
      (by simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1))).toSuperNatTrans_isHomogeneous

/-- Fixed-content nilpotence of the exact normalized dot. Its exponent may
depend on the source content, and is uniform in the arbitrary input module. -/
theorem elvContentDotTo_isNilpotent [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (β γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β) :
    IsNilpotent (show End ((contentInductionTo D Sc cutoff bound β [i] γ hγ).obj M) from
      (elvContentDotTo D Sc cutoff bound i β γ hγ).app (D.parity i) M) := by
  classical
  subst γ
  change IsNilpotent (show End ((contentE D Sc cutoff bound β i).obj M) from
    (contentInductionDot D Sc cutoff bound β i).app (D.parity i) M)
  have hp := contentInductionDot_module_pow_zero D Sc cutoff bound hdot β.toList i
  rw [Multiset.coe_toList] at hp
  obtain ⟨e, _, hp⟩ := hp
  exact ⟨e, hp M⟩

theorem elvBlockDot_isNilpotent [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (β : WeightBlocks D Λ x)
    (M : ContentModules D Sc cutoff bound β.1) :
    IsNilpotent (show End ((elvBlockInd D Sc cutoff bound i Λ h β).obj M) from
      (elvBlockDot D Sc cutoff bound i Λ h β).app (D.parity i) M) :=
  elvContentDotTo_isNilpotent D Sc cutoff bound i hdot β.1
    (blockSucc D Λ i h β).1 (by rw [blockSucc_val, add_comm]; rfl) M

/-- The dot component at a block with a chosen predecessor. -/
def elvWeightDotVia (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ x) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (elvInductionComponent D Sc cutoff bound i Λ h δ).obj M ⟶ (elvInductionComponent D Sc cutoff bound i Λ h δ).obj M := by
  subst hβ
  exact eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M) ≫
    (elvBlockDot D Sc cutoff bound i Λ h β).app p (M β) ≫
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M).symm

theorem elvWeightDotVia_eq (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ x)
    (β β' : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    (hβ' : blockSucc D Λ i h β' = δ) :
    elvWeightDotVia D Sc cutoff bound i Λ h p M β δ hβ =
      elvWeightDotVia D Sc cutoff bound i Λ h p M β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The dot component at a block: through the predecessor, or zero. -/
def elvWeightDotComponent (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ x)
    (δ : WeightBlocks D Λ y) :
    (elvInductionComponent D Sc cutoff bound i Λ h δ).obj M ⟶ (elvInductionComponent D Sc cutoff bound i Λ h δ).obj M :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    elvWeightDotVia D Sc cutoff bound i Λ h p M hδ.choose δ hδ.choose_spec
  else 0

theorem elvWeightDotComponent_blockSucc (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ x)
    (β : WeightBlocks D Λ x) :
    elvWeightDotComponent D Sc cutoff bound i Λ h p M (blockSucc D Λ i h β) =
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M) ≫
        (elvBlockDot D Sc cutoff bound i Λ h β).app p (M β) ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M).symm := by
  unfold elvWeightDotComponent
  split
  · rename_i hc
    exact elvWeightDotVia_eq D Sc cutoff bound i Λ h p M _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem elvWeightDotComponent_mem (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ x)
    (δ : WeightBlocks D Λ y) :
    elvWeightDotComponent D Sc cutoff bound i Λ h p M δ ∈ parity (R := k) _ _ p := by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    rw [elvWeightDotComponent_blockSucc]
    have hm := comp_mem (eqToHom_mem_parity_zero
        (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M))
      (comp_mem ((elvBlockDot D Sc cutoff bound i Λ h β).app_mem p (M β))
        (eqToHom_mem_parity_zero (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M).symm))
    simpa only [zero_add, add_zero] using hm
  · rw [(elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ M).eq_of_src
      (elvWeightDotComponent D Sc cutoff bound i Λ h p M δ) 0]
    exact Submodule.zero_mem _

theorem elvWeightDotComponent_naturality (p : ZMod 2) (β : WeightBlocks D Λ x)
    {M M' : ELVWeightProduct D Sc cutoff bound Λ x} {q : ZMod 2} (f : M ⟶ M')
    (hf : f ∈ parity (R := k) M M' q) :
    (elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).map f ≫
        elvWeightDotComponent D Sc cutoff bound i Λ h p M' (blockSucc D Λ i h β) =
      koszulSign p q • (elvWeightDotComponent D Sc cutoff bound i Λ h p M (blockSucc D Λ i h β) ≫
        (elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [elvInductionComponent_map_blockSucc, elvWeightDotComponent_blockSucc,
    elvWeightDotComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hn := (elvBlockDot D Sc cutoff bound i Λ h β).naturality p (f β) (hf β)
  rw [← Category.assoc ((elvBlockInd D Sc cutoff bound i Λ h β).map (f β)), Superfunctor.map, hn,
    Linear.smul_comp, Linear.comp_smul, Category.assoc]

/-- **The dot on weight-space induction.** -/
def elvWeightDot :
    SuperNatTrans k (elvEFunctor D Sc cutoff bound i Λ h) (elvEFunctor D Sc cutoff bound i Λ h) where
  app p M δ := elvWeightDotComponent D Sc cutoff bound i Λ h p M δ
  app_mem p M δ := elvWeightDotComponent_mem D Sc cutoff bound i Λ h p M δ
  naturality p M M' q f hf := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact elvWeightDotComponent_naturality D Sc cutoff bound i Λ h p β f hf
    · exact (elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ _).eq_of_src _ _

private theorem end_isNilpotent_eqToHom_conj
    {C : Type*} [Category C] [Preadditive C]
    {M N : C} (e : M = N) (d : End N) (hd : IsNilpotent d) :
    IsNilpotent (show End M from eqToHom e ≫ d ≫ eqToHom e.symm) := by
  subst e
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hd

/-- The actual dot is nilpotent at each original target-weight content block.
There is deliberately no common exponent over the weight fibre. -/
theorem elvWeightDotComponent_isNilpotent [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (M : ELVWeightProduct D Sc cutoff bound Λ x)
    (δ : WeightBlocks D Λ y) :
    IsNilpotent (show End ((elvInductionComponent D Sc cutoff bound i Λ h δ).obj M) from
      elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M δ) := by
  classical
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    rw [elvWeightDotComponent_blockSucc]
    exact end_isNilpotent_eqToHom_conj
      (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M) _
      (elvBlockDot_isNilpotent D Sc cutoff bound i Λ h hdot β (M β))
  · rw [(elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ M).eq_of_src
      (elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M δ) 0]
    exact ⟨1, by simp⟩

/-- Only the component of the colour parity is nonzero. -/
theorem elvWeightDot_homogeneous :
    (elvWeightDot D Sc cutoff bound i Λ h).IsHomogeneous (D.parity i) := by
  intro q hq
  funext M
  funext δ
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change elvWeightDotComponent D Sc cutoff bound i Λ h q M (blockSucc D Λ i h β) = 0
    rw [elvWeightDotComponent_blockSucc,
      congrFun (elvBlockDot_homogeneous D Sc cutoff bound i Λ h β q hq)
        (M β)]
    simp
  · exact (elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ M).eq_of_src _ _

/-- The dot as a 2-endomorphism of weight-space induction in the action target. -/
def elvActionDot : elvE D Sc cutoff bound i Λ h ⟶ elvE D Sc cutoff bound i Λ h :=
  elvWeightDot D Sc cutoff bound i Λ h

/-- The dot has the parity of its colour, including for odd colours. -/
theorem elvActionDot_mem :
    elvActionDot D Sc cutoff bound i Λ h ∈
      parity (R := k) (elvE D Sc cutoff bound i Λ h) (elvE D Sc cutoff bound i Λ h)
        (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.2 (elvWeightDot_homogeneous D Sc cutoff bound i Λ h)

end Weight

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Single-letter dots on two original-weight induction steps

Advances `DeformedActionAssembly.md` §6: identify the independently
assembled weight dots at a supported double successor with the actual
single-letter content dots. These comparisons are inputs to the pair
whiskering relations; they do not assume any matrix inverse.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem map_conjugate_eqToHom
    {C B : Type*} [Category C] [Category B] (F : C ⥤ B)
    {a a' : C} {z : B} (h : a = a') (e : z = F.obj a) (e' : z = F.obj a')
    (f : a' ⟶ a') :
    eqToHom e ≫ F.map (eqToHom h ≫ f ≫ eqToHom h.symm) ≫ eqToHom e.symm =
      eqToHom e' ≫ F.map f ≫ eqToHom e'.symm := by
  subst h e
  simp

private theorem family_conjugate_eqToHom
    {C B : Type*} [Category C] [Category B] (F : C ⥤ B)
    (f : ∀ a, F.obj a ⟶ F.obj a) {a a' : C} {z : B}
    (h : a = a') (e : z = F.obj a) (e' : z = F.obj a') :
    eqToHom e ≫ f a ≫ eqToHom e.symm =
      eqToHom e' ≫ f a' ≫ eqToHom e'.symm := by
  subst h e
  simp

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)

/-- The inner weight dot is the induced single-letter content dot, through
the exact supported two-step object equality. -/
theorem elvWeightInnerDot_blockSucc (p : ZMod 2)
    (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvInductionComponent D Sc cutoff bound i Λ h₂
      (blockSucc₂ D i j Λ h₁ h₂ β)).map
        ((elvWeightDot D Sc cutoff bound j Λ h₁).app p M) =
      eqToHom (Functor.congr_obj
        (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) M) ≫
        (elvBlockInd D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).map
          ((elvBlockDot D Sc cutoff bound j Λ h₁ β).app p (M β)) ≫
      eqToHom (Functor.congr_obj
        (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) M).symm := by
  rw [elvInductionComponent_map_blockSucc]
  change _ ≫ (elvBlockInd D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).map
    (elvWeightDotComponent D Sc cutoff bound j Λ h₁ p M (blockSucc D Λ j h₁ β)) ≫ _ = _
  rw [elvWeightDotComponent_blockSucc]
  exact map_conjugate_eqToHom
    (elvBlockInd D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).toFunctor
    (elvInductionComponent_obj_blockSucc D Sc cutoff bound j Λ h₁ β M) _ _ _

/-- The outer weight dot is the dot on the second actual content step,
through the same supported two-step object equality. -/
theorem elvWeightOuterDot_blockSucc (p : ZMod 2)
    (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    elvWeightDotComponent D Sc cutoff bound i Λ h₂ p
      ((elvEFunctor D Sc cutoff bound j Λ h₁).obj M)
      (blockSucc₂ D i j Λ h₁ h₂ β) =
      eqToHom (Functor.congr_obj
        (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) M) ≫
        (elvBlockDot D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).app p
          ((elvBlockInd D Sc cutoff bound j Λ h₁ β).obj (M β)) ≫
      eqToHom (Functor.congr_obj
        (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) M).symm := by
  rw [elvWeightDotComponent_blockSucc]
  exact family_conjugate_eqToHom
    (elvBlockInd D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).toFunctor
    (fun L => (elvBlockDot D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).app p L)
    (elvInductionComponent_obj_blockSucc D Sc cutoff bound j Λ h₁ β M) _ _

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Linear components of the original-weight pair crossing

DeformedActionAssembly §6 uses the original weight crossing and the
canonical pair coordinates in pointwise linear quadratic relations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u

private theorem crossing_total_of_component
    {k : Type u} [CommRing k] {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A B E F : Superfunctor k C (SVec k)}
    (e : A ≅ B) (f : E ≅ F) (x : B ⟶ F) (y : A ⟶ E)
    (h : y = (e.hom ≫ x) ≫ f.inv) (w : C) :
    y.total w = (moduleIsoLinearEquiv f w).symm.toLinearMap.comp
      ((x.total w).comp (moduleIsoLinearEquiv e w).toLinearMap) := by
  subst y
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  rfl

private theorem cross_composite_of_linear_squares
    {k : Type u} [CommRing k]
    {A B C E : Type u}
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    [AddCommMonoid C] [Module k C] [AddCommMonoid E] [Module k E]
    (e : A ≃ₗ[k] B) (f : C ≃ₗ[k] E)
    (x : E →ₗ[k] B) (y : B →ₗ[k] E) (q : C →ₗ[k] A) (r : A →ₗ[k] C)
    (hq : q = e.symm.toLinearMap.comp (x.comp f.toLinearMap))
    (hr : r = f.symm.toLinearMap.comp (y.comp e.toLinearMap)) :
    q.comp r = e.symm.conjAlgEquiv k (x.comp y) := by
  subst q r
  apply LinearMap.ext
  intro z
  change e.symm (x (f (f.symm (y (e z))))) = e.symm (x (y (e z)))
  rw [f.apply_symm_apply]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- Evaluation of the independently assembled weight crossing uses exactly
the selected two-successor comparisons and the prescribed affine crossing. -/
theorem elvWeightCrossVia_total (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    ((elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε).app
      (D.parity i * D.parity j) M).total w =
      (moduleIsoLinearEquiv
        ((elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε
          (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε)).app M) w).symm.toLinearMap.comp
        ((((contentInductionTransform D Sc cutoff bound
          (elvWeightPair_content_eq D j i Λ h₃ h₄ β ε
            (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (contentCrossAffine_mem D Sc i j)).app (D.parity i * D.parity j) (M β)).total w).comp
          (moduleIsoLinearEquiv
            ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M) w).toLinearMap) :=
  crossing_total_of_component
    ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M)
    ((elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε)).app M)
    _ _ (elvWeightCrossVia_component D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε M) w

/-- The two actual weight crossings compose to the affine two-crossing
operator in their selected source coordinates. -/
theorem elvWeightCrossVia_composite_total (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    let hε' := blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε
    let hs := elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε
    let ht := elvWeightPair_content_eq D j i Λ h₃ h₄ β ε hε'
    let e := moduleIsoLinearEquiv
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M) w
    (((elvWeightCrossVia D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂ β ε hε').app
        (D.parity j * D.parity i) M).total w).comp
      (((elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε).app
        (D.parity i * D.parity j) M).total w) =
      e.symm.conjAlgEquiv k
        ((((contentInductionTransform D Sc cutoff bound hs ht
          (contentCrossAffine_mem D Sc j i)).app (D.parity j * D.parity i) (M β)).total w).comp
          (((contentInductionTransform D Sc cutoff bound ht hs
            (contentCrossAffine_mem D Sc i j)).app (D.parity i * D.parity j) (M β)).total w)) := by
  dsimp only
  exact cross_composite_of_linear_squares
    (moduleIsoLinearEquiv
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M) w)
    (moduleIsoLinearEquiv
      ((elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε
        (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε)).app M) w)
    _ _ _ _
    (elvWeightCrossVia_total D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε) M w)
    (elvWeightCrossVia_total D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε M w)

/-- The globally chosen crossing has the same total formula at every
supported output block. -/
theorem elvWeightCrossComponent_total (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    (elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄
      (D.parity i * D.parity j) M ε).total w =
      (moduleIsoLinearEquiv
        ((elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε
          (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε)).app M) w).symm.toLinearMap.comp
        ((((contentInductionTransform D Sc cutoff bound
          (elvWeightPair_content_eq D j i Λ h₃ h₄ β ε
            (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (contentCrossAffine_mem D Sc i j)).app (D.parity i * D.parity j) (M β)).total w).comp
          (moduleIsoLinearEquiv
            ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M) w).toLinearMap) := by
  have h := congrArg (fun a => a.total w)
    (elvWeightCrossComponent_of D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄
      (D.parity i * D.parity j) M β ε hε)
  exact h.trans (elvWeightCrossVia_total D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε M w)

/-- Where the double predecessor is absent, the given global crossing has
zero total at every target word. -/
theorem elvWeightCrossComponent_total_absent (p : ZMod 2)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (ε : WeightBlocks D Λ x₃)
    (hε : ¬ ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    (elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M ε).total w = 0 := by
  rw [elvWeightCrossComponent_absent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M ε hε]
  change (0 : _ →ₗ[k] _) + (0 : _ →ₗ[k] _) = 0
  exact add_zero _

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The weight crossing square in the selected pair coordinates

DeformedActionAssembly §6 (9) requires the original parameter polynomial
at the actual output content, before attaching the two independent weight
dots. The content endpoint is arbitrary, with its specified equality.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The independent weight dots in selected pair coordinates

DeformedActionAssembly §6 (9) requires identifying the two given weight-dot
operators under exactly the pair comparison used for the crossing square.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u

/-- The literal component square, kept as a named proposition while
specializing deep module objects. Unfolding gives equality of whole maps. -/
def ModuleCoordinateSquare
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A E : Superfunctor k C (SVec k)} (e : A ≅ E)
    (x : A ⟶ A) (w : C) (z : E.obj w →ₗ[k] E.obj w) : Prop :=
  (e.hom.total w).comp (x.total w) = z.comp (e.hom.total w)

/-- Evaluation of the whole component square on any input vector. -/
theorem ModuleCoordinateSquare_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A E : Superfunctor k C (SVec k)} {e : A ≅ E}
    {x : A ⟶ A} {w : C} {z : E.obj w →ₗ[k] E.obj w}
    (h : ModuleCoordinateSquare e x w z) (v : A.obj w) :
    e.hom.total w (x.total w v) = z (e.hom.total w v) :=
  congrArg (fun a : A.obj w →ₗ[k] E.obj w => a v) h

private theorem module_coordinate_square_eq
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {P : Type*} [Category* P]
    {F G H : P ⥤ Superfunctor k C (SVec k)}
    (h : F = G) (f : G ≅ H) (M : P)
    (x : F.obj M ⟶ F.obj M) (y : G.obj M ⟶ G.obj M) (w : C)
    (z : (H.obj M).obj w →ₗ[k] (H.obj M).obj w)
    (hx : x = eqToHom (Functor.congr_obj h M) ≫ y ≫
      eqToHom (Functor.congr_obj h M).symm)
    (hy : ((f.hom.app M).total w).comp (y.total w) =
      z.comp ((f.hom.app M).total w)) :
    ModuleCoordinateSquare ((eqToIso h ≪≫ f).app M) x w z := by
  subst G
  have hxy : x = y := by simpa using hx
  rw [hxy]
  simpa only [ModuleCoordinateSquare, eqToIso_refl, Iso.refl_trans, Iso.app_hom] using hy

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The selected pair comparison intertwines induction on the given first
single-letter dot with its right-whiskered source operator. -/
theorem contentEPairComparison_inner_square (β : Multiset I) (i j : I)
    (γ : Multiset I) (hγ : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    let e := moduleIsoLinearEquiv ((contentEPairToComparison D Sc cutoff bound β i j γ hγ).app M) w
    e.toLinearMap.comp
      (((contentInductionTo D Sc cutoff bound (β + ([i] : Multiset I)) [j] γ
        ((contentPair_sum β i j).symm.trans hγ)).map
        ((contentInductionDot D Sc cutoff bound β i).app (D.parity i) M)).total w) =
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound hγ hγ
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [j]))
          (firstDot_parity D Sc i []))) M w).comp e.toLinearMap := by
  dsimp only
  rw [contentInductionDot_component,
    contentInductionMap_total_of_mem _ (BalancedInduction.transformComponent_mem _ M)]
  exact contentInductionComp_inner D Sc cutoff bound β [i] [j] γ _ hγ
    (firstDot_parity D Sc i []) M w

/-- The preceding square with the actual intermediate content retained. -/
theorem contentInductionCompTo_inner_square (β : Multiset I) (i j : I)
    (δ γ : Multiset I) (hδ : β + ([i] : Multiset I) = δ)
    (hγ : δ + ([j] : Multiset I) = γ) (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    let e := moduleIsoLinearEquiv
      ((contentInductionCompTo D Sc cutoff bound β [i] δ hδ [j] γ hγ h).app M) w
    e.toLinearMap.comp
      (((contentInductionTo D Sc cutoff bound δ [j] γ hγ).map
        ((elvContentDotTo D Sc cutoff bound i β δ hδ).app (D.parity i) M)).total w) =
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [j]))
          (firstDot_parity D Sc i []))) M w).comp e.toLinearMap := by
  subst δ
  exact contentEPairComparison_inner_square D Sc cutoff bound β i j γ h M w

/-- The selected comparison retains the actual second single-letter dot at
the specified intermediate and output contents. -/
theorem contentInductionCompTo_outer_square (β : Multiset I) (i j : I)
    (δ γ : Multiset I) (hδ : β + ([i] : Multiset I) = δ)
    (hγ : δ + ([j] : Multiset I) = γ) (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    let e := moduleIsoLinearEquiv
      ((contentInductionCompTo D Sc cutoff bound β [i] δ hδ [j] γ hγ h).app M) w
    e.toLinearMap.comp
      (((elvContentDotTo D Sc cutoff bound j δ γ hγ).app (D.parity j)
        ((contentInductionTo D Sc cutoff bound β [i] δ hδ).obj M)).total w) =
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h
        (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
          (firstDot_parity D Sc j []))) M w).comp e.toLinearMap := by
  subst δ
  dsimp only
  rw [contentInductionTransform_total]
  exact contentInductionComp_outer D Sc cutoff bound β [i] [j] γ _ h
    (firstDot_parity D Sc j []) M w

variable (i j : I) (Λ : X) {x₀ x₁ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)

/-- The independently assembled inner weight dot commutes with the same
selected pair comparison used for the weight crossing square. -/
theorem elvWeightPairComparison_inner_total
    (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound (blockSucc₂ D i j Λ h₁ h₂ β).1) :
    ModuleCoordinateSquare
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β _ rfl).app M)
      ((elvInductionComponent D Sc cutoff bound i Λ h₂ (blockSucc₂ D i j Λ h₁ h₂ β)).map
        ((elvWeightDot D Sc cutoff bound j Λ h₁).app (D.parity j) M)) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β _ rfl)
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β _ rfl)
          (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [i]))
            (firstDot_parity D Sc j []))) (M β) w) := by
  change ModuleCoordinateSquare
    ((eqToIso (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) ≪≫
      Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
        (elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β)).app M) _ w _
  exact module_coordinate_square_eq
    (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β)
    (Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
      (elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β)) M _ _ w _
    (elvWeightInnerDot_blockSucc D Sc cutoff bound i j Λ h₁ h₂ (D.parity j) β M)
    (contentInductionCompTo_inner_square D Sc cutoff bound β.1 j i
      (blockSucc D Λ j h₁ β).1 (blockSucc₂ D i j Λ h₁ h₂ β).1
      (elvBlockSucc_content_eq D j Λ h₁ β)
      (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β))
      (elvBlockPair_content_eq D i j Λ h₁ h₂ β) (M β) w)

/-- The outer weight dot uses the identical selected pair comparison. -/
theorem elvWeightPairComparison_outer_total
    (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound (blockSucc₂ D i j Λ h₁ h₂ β).1) :
    ModuleCoordinateSquare
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β _ rfl).app M)
      (elvWeightDotComponent D Sc cutoff bound i Λ h₂ (D.parity i)
        ((elvEFunctor D Sc cutoff bound j Λ h₁).obj M)
        (blockSucc₂ D i j Λ h₁ h₂ β)) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β _ rfl)
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β _ rfl)
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [j]))
            (firstDot_parity D Sc i []))) (M β) w) := by
  change ModuleCoordinateSquare
    ((eqToIso (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) ≪≫
      Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
        (elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β)).app M) _ w _
  exact module_coordinate_square_eq
    (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β)
    (Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
      (elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β)) M _ _ w _
    (elvWeightOuterDot_blockSucc D Sc cutoff bound i j Λ h₁ h₂ (D.parity i) β M)
    (contentInductionCompTo_outer_square D Sc cutoff bound β.1 j i
      (blockSucc D Λ j h₁ β).1 (blockSucc₂ D i j Λ h₁ h₂ β).1
      (elvBlockSucc_content_eq D j Λ h₁ β)
      (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β))
      (elvBlockPair_content_eq D i j Λ h₁ h₂ β) (M β) w)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The supported quadratic in independent weight dots

DeformedActionAssembly §6 (9): normalize the two source whiskerings and
transport the original-parameter ordered polynomial through the selected
pair comparison, retaining the independently assembled weight operators.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The original parameter polynomial in operator order; the first-position
power acts before the second-position power. No operators are commuted. -/
def orderedPairOperatorPolynomial {R : Type*} [Ring R] [Algebra k R]
    (i j : I) (A B : R) : R :=
  if D.d i j = 0 then (Sc.t i j : k) • 1 else
    ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
      Sc.s i j r s • (B ^ s * A ^ r) +
    ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

theorem orderedPairOperatorPolynomial_map
    {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]
    (e : R ≃ₐ[k] S) (i j : I) (A B : R) :
    e (orderedPairOperatorPolynomial D Sc i j A B) =
      orderedPairOperatorPolynomial D Sc i j (e A) (e B) := by
  unfold orderedPairOperatorPolynomial
  split_ifs <;> simp only [map_smul, map_one, map_add, map_sum, map_mul, map_pow]

theorem ModuleCoordinateSquare_conj
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A E : Superfunctor k C (SVec k)} {e : A ≅ E}
    {x : A ⟶ A} {w : C} {z : E.obj w →ₗ[k] E.obj w}
    (h : ModuleCoordinateSquare e x w z) :
    (moduleIsoLinearEquiv e w).symm.conjAlgEquiv k z = x.total w := by
  apply LinearMap.ext
  intro v
  apply (moduleIsoLinearEquiv e w).injective
  change (moduleIsoLinearEquiv e w)
      ((moduleIsoLinearEquiv e w).symm (z ((moduleIsoLinearEquiv e w) v))) =
    (moduleIsoLinearEquiv e w) (x.total w v)
  rw [LinearEquiv.apply_symm_apply]
  exact (ModuleCoordinateSquare_apply h v).symm

variable (cutoff : I → ℕ) (bound : ℕ)

private theorem induction_transform_source_congr
    {β γ : Multiset I} {σ : List I} (h : β + (σ : Multiset I) = γ)
    {p : ZMod 2} {a b : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ p)
    (hab : a = b) (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h ha) M w =
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h hb) M w := by
  cases hab
  rfl

theorem contentInduction_inner_positioned (β : Multiset I) (i j : I)
    (γ : Multiset I) (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [j]))
          (firstDot_parity D Sc i []))) M w =
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h
        (firstDot_parity D Sc i [j])) M w :=
  induction_transform_source_congr D Sc cutoff bound h
    (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [j]))
      (firstDot_parity D Sc i [])) (firstDot_parity D Sc i [j])
    (dotE_whiskerRight D Sc [i] [j] 0 (by simp)) M w

theorem contentInduction_outer_positioned (β : Multiset I) (i j : I)
    (γ : Multiset I) (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h
        (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
          (firstDot_parity D Sc j []))) M w =
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h
        (contentPairDot_one_parity D Sc i j)) M w :=
  induction_transform_source_congr D Sc cutoff bound h
    (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
      (firstDot_parity D Sc j [])) (contentPairDot_one_parity D Sc i j)
    (whiskerLeft_letter_dotE D Sc i [j] 0) M w

theorem contentInductionPairPolynomialTo_eq_ordered (β : Multiset I) (i j : I)
    (γ : Multiset I) (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D (parameterTwist D Sc) cutoff bound β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff bound γ) :
    contentInductionPairPolynomialTo D Sc cutoff bound β i j γ h M w =
    orderedPairOperatorPolynomial D Sc i j
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff bound h h
          (firstDot_parity D (parameterTwist D Sc) i [j])) M w)
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff bound h h
          (contentPairDot_one_parity D (parameterTwist D Sc) i j)) M w) := rfl

variable (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- The prescribed supported weight crossing square is the original
parameter polynomial in the independently defined inner and outer dots.
The source word is `[j,i]`, so the polynomial uses that same order. -/
theorem elvWeightCrossVia_quadratic_independent (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀)
    (M : ELVWeightProduct D (parameterTwist D Sc) cutoff bound Λ x₀)
    (w : ContentCategory D (parameterTwist D Sc) cutoff bound
      (blockSucc₂ D i j Λ h₁ h₂ β).1) :
    let ε := blockSucc₂ D i j Λ h₁ h₂ β
    let hε' := blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ (β := β) (ε := ε) rfl
    let x := (elvInductionComponent D (parameterTwist D Sc) cutoff bound i Λ h₂ ε).map
      ((elvWeightDot D (parameterTwist D Sc) cutoff bound j Λ h₁).app (D.parity j) M)
    let y := elvWeightDotComponent D (parameterTwist D Sc) cutoff bound i Λ h₂ (D.parity i)
      ((elvEFunctor D (parameterTwist D Sc) cutoff bound j Λ h₁).obj M) ε
    (((elvWeightCrossVia D (parameterTwist D Sc) cutoff bound
        j i Λ h₃ h₄ h₁ h₂ β ε hε').app
        (D.parity j * D.parity i) M).total w).comp
      (((elvWeightCrossVia D (parameterTwist D Sc) cutoff bound
        i j Λ h₁ h₂ h₃ h₄ β ε rfl).app
        (D.parity i * D.parity j) M).total w) =
      orderedPairOperatorPolynomial (R := Module.End k _) D Sc j i (x.total w) (y.total w) := by
  dsimp only
  let ε := blockSucc₂ D i j Λ h₁ h₂ β
  let hs := elvWeightPair_content_eq D i j Λ h₁ h₂ β ε rfl
  let e := moduleIsoLinearEquiv
    ((elvWeightPairComparison D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ β ε rfl).app M) w
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff bound hs hs
      (firstDot_parity D (parameterTwist D Sc) j [i])) (M β) w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff bound hs hs
      (contentPairDot_one_parity D (parameterTwist D Sc) j i)) (M β) w
  have hi := elvWeightPairComparison_inner_total D (parameterTwist D Sc) cutoff bound
    i j Λ h₁ h₂ β M w
  rw [contentInduction_inner_positioned] at hi
  have ho := elvWeightPairComparison_outer_total D (parameterTwist D Sc) cutoff bound
    i j Λ h₁ h₂ β M w
  rw [contentInduction_outer_positioned] at ho
  have hx : e.symm.conjAlgEquiv k A =
      (((elvInductionComponent D (parameterTwist D Sc) cutoff bound i Λ h₂ ε).map
        ((elvWeightDot D (parameterTwist D Sc) cutoff bound j Λ h₁).app
          (D.parity j) M)).total w) := ModuleCoordinateSquare_conj hi
  have hy : e.symm.conjAlgEquiv k B =
      (elvWeightDotComponent D (parameterTwist D Sc) cutoff bound i Λ h₂ (D.parity i)
        ((elvEFunctor D (parameterTwist D Sc) cutoff bound j Λ h₁).obj M) ε).total w :=
    ModuleCoordinateSquare_conj ho
  have hq := elvWeightCrossVia_quadratic_total D Sc cutoff bound i j Λ
    h₁ h₂ h₃ h₄ hij β ε rfl M w
  dsimp only at hq
  rw [contentInductionPairPolynomialTo_eq_ordered] at hq
  have hp := orderedPairOperatorPolynomial_map D Sc (e.symm.conjAlgEquiv k) j i A B
  rw [hx, hy] at hp
  exact hq.trans hp

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Quadratic components on every original weight block

DeformedActionAssembly §6 (9): the independently assembled global
crossings have the original-parameter quadratic in the actual weight dots,
including the absent-double-predecessor branch.
-/

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u

/-- A zero supermodule has zero value at every object, before specializing
any induction coends. -/
theorem moduleValue_subsingleton_of_isZero
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Superfunctor k C (SVec k)} (hA : Limits.IsZero A) (w : C) :
    Subsingleton (A.obj w) := by
  have hh := congrArg (fun f : A ⟶ A => f.total w)
    (hA.eq_of_src (𝟙 A) 0)
  change (LinearMap.id : A.obj w →ₗ[k] A.obj w) + 0 = 0 + 0 at hh
  have hv (v : A.obj w) : v = 0 := by
    have h := congrArg (fun f : A.obj w →ₗ[k] A.obj w => f v) hh
    simpa only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.zero_apply, add_zero] using h
  exact ⟨fun v z => (hv v).trans (hv z).symm⟩

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- The global crossing components obey the original-Sc quadratic in the
independently given inner and outer weight dots at every output block.
No support or predecessor hypothesis is added. -/
theorem elvWeightCrossComponent_quadratic_total (hij : i ≠ j)
    (M : ELVWeightProduct D (parameterTwist D Sc) cutoff bound Λ x₀)
    (ε : WeightBlocks D Λ x₃)
    (w : ContentCategory D (parameterTwist D Sc) cutoff bound ε.1) :
    let x := (elvInductionComponent D (parameterTwist D Sc) cutoff bound i Λ h₂ ε).map
      ((elvWeightDot D (parameterTwist D Sc) cutoff bound j Λ h₁).app (D.parity j) M)
    let y := elvWeightDotComponent D (parameterTwist D Sc) cutoff bound i Λ h₂ (D.parity i)
      ((elvEFunctor D (parameterTwist D Sc) cutoff bound j Λ h₁).obj M) ε
    ((elvWeightCrossComponent D (parameterTwist D Sc) cutoff bound j i Λ h₃ h₄ h₁ h₂
        (D.parity j * D.parity i) M ε).total w).comp
      ((elvWeightCrossComponent D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ h₃ h₄
        (D.parity i * D.parity j) M ε).total w) =
      orderedPairOperatorPolynomial (R := Module.End k _) D Sc j i (x.total w) (y.total w) := by
  dsimp only
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    rw [elvWeightCrossComponent_of D (parameterTwist D Sc) cutoff bound j i Λ h₃ h₄ h₁ h₂
      (D.parity j * D.parity i) M β _ (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ rfl)]
    rw [elvWeightCrossComponent_of D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ h₃ h₄
      (D.parity i * D.parity j) M β _ rfl]
    exact elvWeightCrossVia_quadratic_independent D Sc cutoff bound i j Λ
      h₁ h₂ h₃ h₄ hij β M w
  · let := moduleValue_subsingleton_of_isZero
      (elvEFunctor_comp₂_isZero D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ ε hε M) w
    apply LinearMap.ext
    intro v
    exact Subsingleton.elim _ _

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Same-colour crossing squares on every weight block

DeformedActionAssembly §6 and Brundan--Ellis (1.9): the prescribed weight
crossing has square zero, including absent double predecessors.
-/

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The prescribed mixed mate on original weight products

For Brundan–Ellis (1.12), bend the selected weight crossing by the lower
and upper j-adjunctions. The positive distinct crossing has reversed
indices in `elvActionCross`, because induction is contravariant in the
affine crossing. At an output without an i-predecessor, both actual
mixed-functor coordinates vanish, including the target after adding j.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem isIso_between_zero
    {C : Type*} [Category C] [Limits.HasZeroMorphisms C] {M P : C} (f : M ⟶ P)
    (hM : Limits.IsZero M) (hP : Limits.IsZero P) : IsIso f := by
  let : Limits.HasZeroObject C := ⟨⟨M, hM⟩⟩
  rw [hM.eq_of_src f 0]
  exact (Limits.isIsoZero_iff_source_target_isZero M P).mpr ⟨hM, hP⟩

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Ei₀" => elvE D Sc cutoff bound i Λ h₃
local notation "Ei₁" => elvE D Sc cutoff bound i Λ h₂
local notation "Fj₀" => elvF D Sc cutoff bound j Λ h₁
local notation "Fj₁" => elvF D Sc cutoff bound j Λ h₄
local notation "Adj₀" => elvActionAdjunction D Sc cutoff bound j Λ h₁
local notation "Adj₁" => elvActionAdjunction D Sc cutoff bound j Λ h₄
local notation "Cross" => elvActionCross D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂

/-- The actual weight-space cup, selected crossing, and cap. -/
def elvWeightMixedMate : Fj₀ ≫ Ei₀ ⟶ Ei₁ ≫ Fj₁ :=
  SKM.rectangularMate Adj₀ Adj₁ Ei₀ Ei₁ Cross

/-- The given weight mate retains the selected crossing degree. -/
theorem elvWeightMixedMate_mem :
    elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  have h := SKM.rectangularMate_piscat_mem Adj₀ Adj₁ Ei₀ Ei₁ Cross
    (elvActionCross_mem D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂)
  simpa only [elvWeightMixedMate, mul_comm] using h

/-- Both j-adjunctions remain at their actual, different weight corners. -/
theorem elvWeightMixedMate_app (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app p M =
      (elvActionUnit D Sc cutoff bound j Λ h₄).app 0 ((Ei₀).obj ((Fj₀).obj M)) ≫
        (Fj₁).map ((Cross).app p ((Fj₀).obj M)) ≫
          (Fj₁).map ((Ei₁).map ((elvActionCounit D Sc cutoff bound j Λ h₁).app 0 M)) :=
  SKM.rectangularMate_piscat_app Adj₀ Adj₁ Ei₀ Ei₁ Cross
    (fun W => Superfunctor.app_eq_zero_of_mem (Adj₁).unit_mem (by decide) W)
    (fun W => Superfunctor.app_eq_zero_of_mem (Adj₀).counit_mem (by decide) W) p M

/-- Adding j preserves the existence of an i-predecessor when the colours differ. -/
theorem elvMixedPredecessor_iff (hij : i ≠ j) (δ : WeightBlocks D Λ xi) :
    (∃ γ, blockSucc D Λ i h₂ γ = blockSucc D Λ j h₄ δ) ↔
      ∃ β, blockSucc D Λ i h₃ β = δ := by
  rw [exists_blockSucc_iff, exists_blockSucc_iff]
  simp only [blockSucc_val, Multiset.mem_add, Multiset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact (hij h).elim
    · exact h
  · exact Or.inr

/-- The actual source coordinate is zero at an absent i-predecessor. -/
theorem elvWeightMixedSource_isZero (δ : WeightBlocks D Λ xi)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₃ β = δ)
    (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    Limits.IsZero (((Fj₀ ≫ Ei₀).obj M) δ) :=
  elvInductionComponent_isZero D Sc cutoff bound i Λ h₃ δ hδ ((Fj₀).obj M)

/-- The actual target coordinate also vanishes; adding j does not create i. -/
theorem elvWeightMixedTarget_isZero (hij : i ≠ j) (δ : WeightBlocks D Λ xi)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₃ β = δ)
    (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    Limits.IsZero (((Ei₁ ≫ Fj₁).obj M) δ) := by
  have hUpper : ¬ ∃ γ, blockSucc D Λ i h₂ γ = blockSucc D Λ j h₄ δ :=
    fun h => hδ ((elvMixedPredecessor_iff D i j Λ h₂ h₃ h₄ hij δ).mp h)
  have hZero := elvInductionComponent_isZero D Sc cutoff bound i Λ h₂
    (blockSucc D Λ j h₄ δ) hUpper M
  exact (elvBlockRes D Sc cutoff bound j Λ h₄ δ).toFunctor.map_isZero hZero

/-- The prescribed mate is already invertible on every genuine absent output sector. -/
theorem elvWeightMixedMate_absent_isIso (hij : i ≠ j) (δ : WeightBlocks D Λ xi)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₃ β = δ)
    (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    IsIso ((elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app p M δ) :=
  isIso_between_zero _
    (elvWeightMixedSource_isZero D Sc cutoff bound i j Λ h₁ h₃ δ hδ M)
    (elvWeightMixedTarget_isZero D Sc cutoff bound i j Λ h₂ h₃ h₄ hij δ hδ M)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Supported weight coordinates for the distinct mate

The source and target of the weight mate of Brundan–Ellis (1.12) are
identified with their literal four-corner content induction/restriction
coordinates. The common upper content is the actual j-successor of the
output block, with the i-successor comparison kept explicit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- A chosen predecessor determines induction at an arbitrary literal target block. -/
theorem elvInductionComponent_obj_of (i : I) (Λ : X) {x y : X}
    (h : x + D.α i = y) (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y)
    (hβ : blockSucc D Λ i h β = δ) (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    (elvInductionComponent D Sc cutoff bound i Λ h δ).obj M =
      BalancedInduction.induced
        (contentAppendTo D Sc cutoff bound β.1 [i] δ.1
          ((elvBlockSucc_content_eq D i Λ h β).trans (congrArg Subtype.val hβ))) (M β) := by
  subst δ
  exact elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M

variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
  (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "J" => elvBlockAppend D Sc cutoff bound j Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff bound i Λ h₃ β
local notation "U" => elvBlockAppend D Sc cutoff bound j Λ h₄ (blockSucc D Λ i h₃ β)

include h₂ in
/-- The two successor orders have this same literal upper content. -/
theorem elvMixedUpper_content_eq :
    (blockSucc D Λ j h₁ β).1 + ([i] : Multiset I) =
      (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)).1 :=
  (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β)).trans
    (congrArg Subtype.val (blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β))

local notation "L" => contentAppendTo D Sc cutoff bound (Subtype.val (blockSucc D Λ j h₁ β)) [i]
  (Subtype.val (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β))) (elvMixedUpper_content_eq D i j Λ h₁ h₂ h₃ h₄ β)

/-- The actual supported source is induction of the restricted input at its predecessor. -/
theorem elvWeightMixedSource_obj (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (((elvF D Sc cutoff bound j Λ h₁ ≫ elvE D Sc cutoff bound i Λ h₃).obj M) δi) =
      BalancedInduction.induced K ((BalancedInduction.restriction J).obj (M δj)) :=
  elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₃ β
    ((elvF D Sc cutoff bound j Λ h₁).obj M)

/-- The actual supported target is restriction of induction to the same upper content. -/
theorem elvWeightMixedTarget_obj (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (((elvE D Sc cutoff bound i Λ h₂ ≫ elvF D Sc cutoff bound j Λ h₄).obj M) δi) =
      (BalancedInduction.restriction U).obj (BalancedInduction.induced L (M δj)) := by
  exact congrArg (fun P => (BalancedInduction.restriction U).obj P)
    (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε
      (blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β) M)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Weight pair comparison in rectangular content coordinates

The supported crossing comparison required by Brundan–Ellis (1.12)
retains the actual first successor and the prescribed upper block.
The chosen word comparison factors through the two literal append
inductions at these contents.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem transform_app_regrade
    {k C E : Type u} [CommRing k] [Category.{u} C] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (F G : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p q : ZMod 2} {α : ∀ s, F.obj s ⟶ G.obj s} (hpq : p = q)
    (hαp : IsSupernatural k p α) (hαq : IsSupernatural k q α)
    (P : Superfunctor k C (SVec k)) :
    (BalancedInduction.transform hαp).app p P = (BalancedInduction.transform hαq).app q P := by
  subst q
  rfl

private theorem comparison_cross_paste
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (Q : C ⥤ B) {S T : C ⥤ E} {S' T' U' V' : B ⥤ E}
    (eS : S ≅ Q ⋙ S') (eT : T ≅ Q ⋙ T') (fS : S' ≅ U') (fT : T' ≅ V')
    (χ : ∀ b, U'.obj b ⟶ V'.obj b) (M : C) :
    (((eS ≪≫ Functor.isoWhiskerLeft Q fS).hom.app M ≫ χ (Q.obj M)) ≫
      (eT ≪≫ Functor.isoWhiskerLeft Q fT).inv.app M) =
      (eS.hom.app M ≫ ((fS.hom.app (Q.obj M) ≫ χ (Q.obj M)) ≫ fT.inv.app (Q.obj M))) ≫
        eT.inv.app M := by
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.assoc]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

private theorem rectangular_eqIso_whiskerLeft
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (Q : C ⥤ B) {F G : B ⥤ E} (h : F = G) :
    Functor.isoWhiskerLeft Q (eqToIso h) = eqToIso (congrArg (fun F => Q ⋙ F) h) := by
  cases h
  rfl

private theorem contentPairComparisonTo_eq
    (β : Multiset I) (i j : I) (δ γ : Multiset I)
    (hδ : β + ([i] : Multiset I) = δ) (hγ : δ + ([j] : Multiset I) = γ)
    (h : β + ([i,j] : Multiset I) = γ) :
    contentInductionCompTo D Sc cutoff bound β [i] δ hδ [j] γ hγ h =
      eqToIso (contentPairInductionTo_eq D Sc cutoff bound β i j δ γ hδ hγ h) ≪≫
        contentEPairToComparison D Sc cutoff bound β i j γ h := by
  apply Iso.ext
  exact contentPairComparisonTo_hom D Sc cutoff bound β i j δ γ hδ hγ h

private theorem contentWordCross_app_reverse
    (β γ : Multiset I) (i j : I)
    (hσ : β + ([i,j] : Multiset I) = γ) (hτ : β + ([j,i] : Multiset I) = γ)
    (P : ContentModules D Sc cutoff bound β) :
    (contentInductionTransform D Sc cutoff bound hσ hτ (contentCrossAffine_mem D Sc i j)).app
      (D.parity i * D.parity j) P =
    (contentInductionTransform D Sc cutoff bound (σ := [i] ++ [j]) (τ := [j] ++ [i])
      hσ hτ (contentCrossAffine_reverse_mem D Sc j i)).app (D.parity j * D.parity i) P := by
  exact transform_app_regrade _ _ (mul_comm (D.parity i) (D.parity j)) _ _ P

variable (i j : I) (Λ : X) {x₀ xj xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
  (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)

include h₂ hε in
/-- The final-content certificate keeps the first successor. -/
theorem elvWeightPairUpper_content_eq :
    (blockSucc D Λ j h₁ β).1 + ([i] : Multiset I) = ε.1 :=
  (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β)).trans
    (congrArg Subtype.val hε)

local notation "hj" => elvBlockSucc_content_eq D j Λ h₁ β
local notation "hUpper" => elvWeightPairUpper_content_eq D i j Λ h₁ h₂ β ε hε
local notation "hWord" => elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε
local notation "Pair" => contentInductionTo D Sc cutoff bound (Subtype.val β) [j]
  (Subtype.val (blockSucc D Λ j h₁ β)) hj ⋙
    contentInductionTo D Sc cutoff bound (Subtype.val (blockSucc D Λ j h₁ β)) [i]
      (Subtype.val ε) hUpper
local notation "Eval" => Superfunctor.toFunctor (elvBlockEval D Sc cutoff bound Λ β)

/-- The supported product coordinate is the literal two-append induction through its first block. -/
theorem elvEFunctor_comp₂_rectangular_eq :
    elvEFunctor D Sc cutoff bound j Λ h₁ ⋙
      (elvInductionComponent D Sc cutoff bound i Λ h₂ ε).toFunctor = Eval ⋙ Pair := by
  exact (elvEFunctor_comp₂_contentPair_eq D Sc cutoff bound i j Λ h₁ h₂ β ε hε).trans
    (congrArg (fun F => Eval ⋙ F)
      (contentPairInductionTo_eq D Sc cutoff bound β.1 j i
        (blockSucc D Λ j h₁ β).1 ε.1 hj hUpper hWord)).symm

/-- The independently selected weight comparison is exactly the rectangular-coordinate comparison. -/
theorem elvWeightPairComparison_rectangular_eq :
    elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε =
      eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound i j Λ h₁ h₂ β ε hε) ≪≫
        Functor.isoWhiskerLeft Eval
          (contentInductionCompTo D Sc cutoff bound β.1 [j]
            (blockSucc D Λ j h₁ β).1 hj [i] ε.1 hUpper hWord) := by
  rw [contentPairComparisonTo_eq, Functor.isoWhiskerLeft_trans,
    rectangular_eqIso_whiskerLeft, ← Iso.trans_assoc, eqToIso_trans]
  exact elvWeightPairComparison_eq D Sc cutoff bound i j Λ h₁ h₂ β ε hε

variable {xi : X} (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "hSwap" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε
local notation "hi" => elvBlockSucc_content_eq D i Λ h₃ β
local notation "hUpperSwap" => elvWeightPairUpper_content_eq D j i Λ h₃ h₄ β ε hSwap
local notation "J" => elvBlockAppend D Sc cutoff bound i Λ h₃ β
local notation "K" => elvBlockAppend D Sc cutoff bound j Λ h₁ β
local notation "L" => contentAppendTo D Sc cutoff bound
  (Subtype.val (blockSucc D Λ i h₃ β)) [j] (Subtype.val ε) hUpperSwap
local notation "U" => contentAppendTo D Sc cutoff bound
  (Subtype.val (blockSucc D Λ j h₁ β)) [i] (Subtype.val ε) hUpper
local notation "hα" => contentDistinctTargetsCross_supernatural D Sc cutoff bound
  (Subtype.val β) j i (Subtype.val (blockSucc D Λ i h₃ β))
  (Subtype.val (blockSucc D Λ j h₁ β)) (Subtype.val ε) hi hj hUpperSwap hUpper

/-- The selected supported weight crossing is the rectangular content crossing
in the independently chosen product-induction coordinates. -/
theorem elvWeightCrossVia_rectangular (hne : i ≠ j)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε).app
      (D.parity i * D.parity j) M =
      ((eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound i j Λ h₁ h₂ β ε hε)).hom.app M ≫
        BalancedInduction.rectangularCrossComponent J K L U hα (M β)) ≫
        (eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound j i Λ h₃ h₄ β ε hSwap)).inv.app M := by
  rw [elvWeightCrossVia_component, elvWeightPairComparison_rectangular_eq,
    elvWeightPairComparison_rectangular_eq]
  dsimp only [elvBlockEval, Pi.eval, Functor.comp_obj]
  rw [comparison_cross_paste]
  rw [contentWordCross_app_reverse]
  rw [contentDistinctTargetsCross_comparison D Sc cutoff bound β.1 j i
    (blockSucc D Λ i h₃ β).1 (blockSucc D Λ j h₁ β).1 ε.1 hi hj hUpperSwap hUpper
    (elvWeightPair_content_eq D j i Λ h₃ h₄ β ε hSwap) hWord hne.symm (M β)]

end OddMath.QuiverHecke.ELV
end

end

section

/-! The existing chosen weight crossing in normalized rectangular coordinates,
including equal colours and their prescribed extra minus. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem normalized_transform_app_regrade
    {k C E : Type u} [CommRing k] [Category.{u} C] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (F G : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p q : ZMod 2} {α : ∀ s, F.obj s ⟶ G.obj s} (hpq : p = q)
    (hαp : IsSupernatural k p α) (hαq : IsSupernatural k q α)
    (P : Superfunctor k C (SVec k)) :
    (BalancedInduction.transform hαp).app p P = (BalancedInduction.transform hαq).app q P := by
  subst q
  rfl

private theorem normalized_comparison_cross_paste
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (Q : C ⥤ B) {S T : C ⥤ E} {S' T' U' V' : B ⥤ E}
    (eS : S ≅ Q ⋙ S') (eT : T ≅ Q ⋙ T') (fS : S' ≅ U') (fT : T' ≅ V')
    (χ : ∀ b, U'.obj b ⟶ V'.obj b) (M : C) :
    (((eS ≪≫ Functor.isoWhiskerLeft Q fS).hom.app M ≫ χ (Q.obj M)) ≫
      (eT ≪≫ Functor.isoWhiskerLeft Q fT).inv.app M) =
      (eS.hom.app M ≫ ((fS.hom.app (Q.obj M) ≫ χ (Q.obj M)) ≫ fT.inv.app (Q.obj M))) ≫
        eT.inv.app M := by
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.assoc]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
private theorem normalized_contentWordCross_app_reverse
    (β γ : Multiset I) (i j : I)
    (hσ : β + ([i,j] : Multiset I) = γ) (hτ : β + ([j,i] : Multiset I) = γ)
    (P : ContentModules D Sc cutoff bound β) :
    (contentInductionTransform D Sc cutoff bound hσ hτ (contentCrossAffine_mem D Sc i j)).app
      (D.parity i * D.parity j) P =
    (contentInductionTransform D Sc cutoff bound (σ := [i] ++ [j]) (τ := [j] ++ [i])
      hσ hτ (contentCrossAffine_reverse_mem D Sc j i)).app (D.parity j * D.parity i) P := by
  exact normalized_transform_app_regrade _ _ (mul_comm (D.parity i) (D.parity j)) _ _ P

variable (i j : I) (Λ : X) {x₀ xj xu xi : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
  (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "hj" => elvBlockSucc_content_eq D j Λ h₁ β
local notation "hi" => elvBlockSucc_content_eq D i Λ h₃ β
local notation "hUpper" => elvWeightPairUpper_content_eq D i j Λ h₁ h₂ β ε hε
local notation "hWord" => elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε
local notation "hSwap" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε
local notation "hUpperSwap" => elvWeightPairUpper_content_eq D j i Λ h₃ h₄ β ε hSwap
local notation "J" => elvBlockAppend D Sc cutoff bound i Λ h₃ β
local notation "K" => elvBlockAppend D Sc cutoff bound j Λ h₁ β
local notation "L" => contentAppendTo D Sc cutoff bound
  (Subtype.val (blockSucc D Λ i h₃ β)) [j] (Subtype.val ε) hUpperSwap
local notation "U" => contentAppendTo D Sc cutoff bound
  (Subtype.val (blockSucc D Λ j h₁ β)) [i] (Subtype.val ε) hUpper
local notation "hα" => normalizedContentTargetsCross_supernatural D Sc cutoff bound
  (Subtype.val β) j i (Subtype.val (blockSucc D Λ i h₃ β))
  (Subtype.val (blockSucc D Λ j h₁ β)) (Subtype.val ε) hi hj hUpperSwap hUpper

/-- The selected supported weight crossing is the rectangular content crossing
in the independently chosen product-induction coordinates. -/
theorem elvWeightCrossVia_normalized_rectangular
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε).app
      (D.parity i * D.parity j) M =
      ((eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound i j Λ h₁ h₂ β ε hε)).hom.app M ≫
        BalancedInduction.rectangularCrossComponent J K L U hα (M β)) ≫
        (eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound j i Λ h₃ h₄ β ε hSwap)).inv.app M := by
  rw [elvWeightCrossVia_component, elvWeightPairComparison_rectangular_eq,
    elvWeightPairComparison_rectangular_eq]
  dsimp only [elvBlockEval, Pi.eval, Functor.comp_obj]
  rw [normalized_comparison_cross_paste]
  rw [normalized_contentWordCross_app_reverse]
  rw [normalizedContentTargetsCross_comparison D Sc cutoff bound β.1 j i
    (blockSucc D Λ i h₃ β).1 (blockSucc D Λ j h₁ β).1 ε.1 hi hj hUpperSwap hUpper
    (elvWeightPair_content_eq D j i Λ h₃ h₄ β ε hSwap) hWord (M β)]

end OddMath.QuiverHecke.ELV
end

end
