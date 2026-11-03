/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightTripleCrossCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightTriplePolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierMixedBraidEquation

/-! # The corrected braid for the selected OLD probe weight generators

Brundan–Ellis (1.9): attach the evaluated stored-target corrected braid
to the independently chosen weight crossings and signed dots. The
coefficients are Sc, while the acting scalar family is parameterTwist Sc.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u

private theorem conjugate_three_paths {C : Type*} [Category* C]
    {A B E T A' B' E' T' : C} (eA : A = A') (eB : B = B') (eE : E = E') (eT : T = T')
    (f₀ : A' ⟶ B') (f₁ : B' ⟶ E') (f₂ : E' ⟶ T') :
    (eqToHom eA ≫ f₀ ≫ eqToHom eB.symm) ≫
        (eqToHom eB ≫ f₁ ≫ eqToHom eE.symm) ≫ (eqToHom eE ≫ f₂ ≫ eqToHom eT.symm) =
    eqToHom eA ≫ (f₀ ≫ f₁ ≫ f₂) ≫ eqToHom eT.symm := by
  cases eA
  cases eB
  cases eE
  cases eT
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem correction_conjugate {C : Type*} [Category* C]
    {A S T : C} (hST : S = T) (p : A = S) (q : A = T)
    (f : End S) (g : End T) (h : HEq f g) :
    eqToHom p ≫ f ≫ eqToHom p.symm = eqToHom q ≫ g ≫ eqToHom q.symm := by
  cases hST
  have hf : f = g := eq_of_heq h
  cases hf
  rfl

section Evaluation
variable {k : Type u} [CommRing k]
    {C : Type*} [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    {J : Type*} {A : J → Type*}
    [∀ t, Category (A t)] [∀ t, Preadditive (A t)]
    [∀ t, Linear k (A t)] [∀ t, Supercategory k (A t)]
    {F G H : Superfunctor k C (∀ t, A t)}
private theorem family_correction_of_components
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (i j : I) (a₀ : F ⟶ G) (a₁ : End G) (a₂ : G ⟶ F)
    (b₀ : F ⟶ H) (b₁ : End H) (b₂ : H ⟶ F) (x₀ x₁ x₂ : End F)
    (h : ∀ M t,
      a₀.total M t ≫ a₁.total M t ≫ a₂.total M t -
        b₀.total M t ≫ b₁.total M t ≫ b₂.total M t =
      tripleDotCorrectionPolynomial (R := End (F.obj M t)) D Sc i j
        (x₀.total M t) (x₁.total M t) (x₂.total M t)) :
    a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial (R := End F) D Sc i j x₀ x₁ x₂ := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro M
  funext t
  let ev := (piEndEvaluation (F.obj M) t).comp (supernaturalEndEvaluation F M)
  have hp := tripleDotCorrectionPolynomial_map D Sc ev i j x₀ x₁ x₂
  have he : (a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂).total M t =
      a₀.total M t ≫ a₁.total M t ≫ a₂.total M t -
        b₀.total M t ≫ b₁.total M t ≫ b₂.total M t := by
    have hs := (supernaturalTotalLinearMap F F M).map_sub
      (a₀ ≫ a₁ ≫ a₂) (b₀ ≫ b₁ ≫ b₂)
    change (a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂).total M =
      (a₀ ≫ a₁ ≫ a₂).total M - (b₀ ≫ b₁ ≫ b₂).total M at hs
    rw [Superfunctor.comp_total, Superfunctor.comp_total,
      Superfunctor.comp_total, Superfunctor.comp_total] at hs
    exact congrFun hs t
  exact he.trans ((h M t).trans hp.symm)
end Evaluation

private theorem pi_component_polynomial
    {k I X : Type u} {C₀ C₁ C₂ : Type*} [CommRing k] [AddCommGroup X]
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
    {J : Type*} {A : J → Type*}
    [∀ t, Category (A t)] [∀ t, Preadditive (A t)]
    [∀ t, Linear k (A t)] [∀ t, Supercategory k (A t)]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (i j : I)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (K : ∀ t, Superfunctor k C₂ (A t))
    (M : C₀) (t : J)
    (l x₀ x₁ x₂ : End (((F ⋙ G ⋙ Functor.pi' (fun t => (K t).toFunctor)).obj M) t))
    (h : @Eq (End (((F ⋙ G ⋙ Functor.pi' (fun t => (K t).toFunctor)).obj M) t))
      l (tripleDotCorrectionPolynomial (R := End (((F ⋙ G) ⋙ (K t).toFunctor).obj M))
        D Sc i j x₀ x₁ x₂)) :
    @Eq (End (((F ⋙ G ⋙ Functor.pi' (fun t => (K t).toFunctor)).obj M) t))
      l (tripleDotCorrectionPolynomial
        (R := End (((F ⋙ G ⋙ Functor.pi' (fun t => (K t).toFunctor)).obj M) t))
        D Sc i j x₀ x₁ x₂) := by
  exact h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "Sc'" => parameterTwist D Sc
local notation "F₀" => probeOldE D Sc' m i Λ hab ≫ probeOldE D Sc' m j Λ hbc ≫ probeOldE D Sc' m i Λ hcd
local notation "a₀" => probeOldWeightCrossSuffix D Sc' m i j i Λ hab hbc hbe hcd hed
local notation "a₁" => probeOldWeightCrossPrefix D Sc' m j i i Λ hab hab hbe hbe hed
local notation "a₂" => probeOldWeightCrossSuffix D Sc' m j i i Λ hab hbe hbc hed hcd
local notation "b₀" => probeOldWeightCrossPrefix D Sc' m i j i Λ hab haf hbc hfc hcd
local notation "b₁" => probeOldWeightCrossSuffix D Sc' m i i j Λ haf hfc hfc hcd hcd
local notation "b₂" => probeOldWeightCrossPrefix D Sc' m i i j Λ haf hab hfc hbc hcd
local notation "x₀" => probeOldWeightTripleFirstDot D Sc' m i j i Λ hab hbc hcd
local notation "x₁" => probeOldWeightTripleMiddleDot D Sc' m i j i Λ hab hbc hcd
local notation "x₂" => probeOldWeightTripleLastDot D Sc' m i j i Λ hab hbc hcd

variable (β : WeightBlocks D Λ a)
local notation "δi" => blockSucc D Λ i hab β
local notation "δj" => blockSucc D Λ j haf β
local notation "δii" => blockSucc D Λ i hbe δi
local notation "δij" => blockSucc₂ D j i Λ hab hbc β
local notation "ε" => probeOldBlockSucc₃ D i j i Λ hab hbc hcd β

private theorem mixed_middle_support : blockSucc D Λ i hfc δj = δij :=
  (blockSucc_comm D Λ j i hab hbc haf hfc β).symm

private theorem mixed_top_support : blockSucc D Λ j hed δii = ε := by
  apply Subtype.ext
  change {j} + ({i} + ({i} + β.1)) = {i} + ({j} + ({i} + β.1))
  ac_rfl

local notation "hI" => probeOldBlockTarget_perm D i Λ hab β δi rfl
local notation "hIJ" => probeOldBlockTarget_perm D j Λ hbc δi δij rfl
local notation "hTopI" => probeOldBlockTarget_perm D i Λ hcd δij ε rfl
local notation "T₃" => (fun N : ProbeCanonicalModules D Sc' m (Subtype.val β) =>
  Functor.obj (probeEvaluatedAppendTo D Sc' m (Multiset.toList (Subtype.val δij)) i
    (Multiset.toList (Subtype.val ε)) hTopI)
      (Functor.obj (probeEvaluatedAppendTo D Sc' m (Multiset.toList (Subtype.val δi)) j
        (Multiset.toList (Subtype.val δij)) hIJ)
          (Functor.obj (probeEvaluatedAppendTo D Sc' m (Multiset.toList (Subtype.val β)) i
            (Multiset.toList (Subtype.val δi)) hI) N)))

private theorem mixedStored_obj_eq (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (F₀).obj M ε = T₃ (M β) :=
  probeOldWeightTriple_obj_eq D Sc' m i j i Λ hab hbc hcd β M

private theorem mixedPolynomial_component (M : ProbeOldWeightProduct D Sc' m Λ a) :
    tripleDotCorrectionPolynomial D Sc (R := End ((F₀).obj M ε)) i j
      ((x₀).total M ε) ((x₁).total M ε) ((x₂).total M ε) =
    eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M) ≫
      tripleDotCorrectionPolynomial D Sc (R := End (T₃ (M β))) i j
        (probeStoredFirstDot D Sc m (Multiset.toList β.1) i j hI hIJ hTopI (M β))
        (probeStoredMiddleDot D Sc m (Multiset.toList β.1) i j hI hIJ hTopI (M β))
        (probeStoredLastDot D Sc m (Multiset.toList β.1) i j hI hIJ hTopI (M β)) ≫
      eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M).symm := by
  rw [probeOldWeightTripleFirstDot_component, probeOldWeightTripleMiddleDot_component,
    probeOldWeightTripleLastDot_component]
  exact (tripleDotCorrectionPolynomial_map D Sc
    (ELVOld.BalancedInduction.inductionEndConjugation
      (eqToIso (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M))) i j _ _ _).symm

/-- The supported corrected braid is the polynomial in the three prescribed global dots. -/
theorem probeOldWeightMixedBraid_component (hne : i ≠ j)
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (show End ((F₀).obj M ε) from (a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε) -
      (show End ((F₀).obj M ε) from (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε) =
      tripleDotCorrectionPolynomial D Sc (R := End ((F₀).obj M ε)) i j
        ((x₀).total M ε) ((x₁).total M ε) ((x₂).total M ε) := by
  have hJI := mixed_middle_support D i j Λ hab haf hbc hfc β
  have hTop := mixed_top_support D i j Λ hab hbc hbe hcd hed β
  have hR₀ := probeOldWeightCrossSuffix_via_total D Sc' m i j i Λ hab hbc hbe hcd hed
    β δi δij δii ε rfl rfl rfl rfl hTop M
  have hR₁ := probeOldWeightCrossPrefix_via_total D Sc' m j i i Λ hab hab hbe hbe hed
    β δi δi δii ε rfl rfl rfl rfl hTop M
  have hR₂ := probeOldWeightCrossSuffix_via_total D Sc' m j i i Λ hab hbe hbc hed hcd
    β δi δii δij ε rfl rfl rfl hTop rfl M
  have hL₀ := probeOldWeightCrossPrefix_via_total D Sc' m i j i Λ hab haf hbc hfc hcd
    β δi δj δij ε rfl rfl rfl hJI rfl M
  have hL₁ := probeOldWeightCrossSuffix_via_total D Sc' m i i j Λ haf hfc hfc hcd hcd
    β δj δij δij ε rfl hJI hJI rfl rfl M
  have hL₂ := probeOldWeightCrossPrefix_via_total D Sc' m i i j Λ haf hab hfc hbc hcd
    β δj δi δij ε rfl rfl hJI rfl rfl M
  simp only [ite_eq_right hne, ite_eq_right hne.symm, ite_true, one_smul, neg_one_smul,
    Functor.map_neg] at hR₀ hR₁ hR₂ hL₀ hL₁ hL₂
  rw [hR₀, hR₁, hR₂, hL₀, hL₁, hL₂,
    mixedPolynomial_component D Sc m i j Λ hab hbc hcd β M]
  have hB := probeStoredMixedBraid_polynomial D Sc m (Multiset.toList β.1) i j
    (probeOldBlockTarget_perm D i Λ hab β δi rfl)
    (probeOldBlockTarget_perm D j Λ haf β δj rfl)
    (probeOldBlockTarget_perm D i Λ hbe δi δii rfl)
    (probeOldBlockTarget_perm D j Λ hbc δi δij rfl)
    (probeOldBlockTarget_perm D i Λ hfc δj δij hJI)
    (probeOldBlockTarget_perm D j Λ hed δii ε hTop)
    (probeOldBlockTarget_perm D i Λ hcd δij ε rfl) hne (M β)
  rw [conjugate_three_paths, conjugate_three_paths]
  rw [← Preadditive.comp_sub, ← Preadditive.sub_comp]
  apply correction_conjugate (C := ProbeCanonicalModules D Sc' m ε.1) rfl
  simpa only [probeStoredMixedBraid] using heq_of_eq hB

/-- The chosen whole-weight corrected braid includes every absent predecessor coordinate. -/
theorem probeOldActionCross_mixedBraid (hne : i ≠ j) :
    a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial D Sc (R := End F₀) i j x₀ x₁ x₂ := by
  apply family_correction_of_components D Sc i j a₀ a₁ a₂ b₀ b₁ b₂ x₀ x₁ x₂
  intro M η
  by_cases hs : ∃ γ, probeOldBlockSucc₃ D i j i Λ hab hbc hcd γ = η
  · obtain ⟨γ, rfl⟩ := hs
    apply pi_component_polynomial D Sc i j
      (probeOldEFunctor D Sc' m i Λ hab) (probeOldEFunctor D Sc' m j Λ hbc)
      (probeOldInductionComponent D Sc' m i Λ hcd) M _ _ _ _ _
    have h := probeOldWeightMixedBraid_component D Sc m i j Λ hab haf hbc hbe hfc hcd hed γ hne M
    set_option backward.dsimp.instances true in
      dsimp only at h ⊢
    convert h using 1
  · exact (probeOldEFunctor_comp₃_isZero D Sc' m i j i Λ hab hbc hcd η hs M).eq_of_src _ _

/-- The exact dotted corrected-braid field on the selected OLD probe generator data. -/
theorem probeOldRouquierData_braidEq (hne : i ≠ j) :
    rouquierMixedBraidEquation D Sc (probeOldRouquierData D Sc' m Λ) i j
      hab haf hbc hbe hfc hcd hed := by
  apply rouquierMixedBraidEquation_of_polynomial
  change a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
    tripleDotCorrectionPolynomial D Sc (R := End F₀) i j x₀ x₁ x₂
  exact probeOldActionCross_mixedBraid D Sc m i j Λ hab haf hbc hbe hfc hcd hed hne

end OddMath.QuiverHecke
