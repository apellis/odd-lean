import OddMath.QuiverHecke.CyclotomicAction.ContentTriple.TriplePolynomial
import OddMath.QuiverHecke.CyclotomicAction.InductionTripleBraid.InductionBraidCube
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexMate.ProbeWeightMixedMate
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightPairDots

/-!
# Probe weight braid

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Stored-target coordinates of the selected OLD weight crossings

Brundan–Ellis (1.9): retain the prescribed positive distinct and negative
equal crossings in common stored-target coordinates, before composing the
three-strand paths. No comparison or relation premise is required.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u

/-- The positive crossing component of `probeAppendToCrossComponent`, with its source and
target written as iterated objects `G.obj (F.obj N)` rather than `(F ⋙ G).obj N`, so that
every composite built from it carries one form of each object. -/
abbrev probeAppendToCrossIterated
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
    (ν : List I) (i j : I) {νj νi ν₂ : List I}
    (hj : (j :: ν).Perm νj) (hi : (i :: ν).Perm νi)
    (hL : (i :: νj).Perm ν₂) (hM : (j :: νi).Perm ν₂)
    (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedAppendTo D Sc m νi j ν₂ hM).obj
        ((probeEvaluatedAppendTo D Sc m ν i νi hi).obj N) ⟶
      (probeEvaluatedAppendTo D Sc m νj i ν₂ hL).obj
        ((probeEvaluatedAppendTo D Sc m ν j νj hj).obj N) :=
  probeAppendToCrossComponent D Sc m ν i j hj hi hL hM N

private theorem equal_rectangle_grid
    {k C A E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p q : ZMod 2} (hp : p = q) {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hγ : IsSupernatural k p γ) (hδ : IsSupernatural k q γ)
    (N : Superfunctor k C (SVec k)) :
    gridDoubleCrossComponent J K hγ N = rectangularCrossComponent J J K K hδ N := by
  cases hp
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

/-- The negative equal crossing retains the prescribed positive stored component with its sign. -/
theorem probeOldBlockEqualCross_stored_total (i : I) (Λ : X) {a b c : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) (β : WeightBlocks D Λ a)
    (N : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total N =
      -probeAppendToCrossIterated D Sc m β.1.toList i i
        (probeOldBlockTarget_perm D i Λ h₁ β _ rfl)
        (probeOldBlockTarget_perm D i Λ h₁ β _ rfl)
        (probeOldPairUpper_perm D i i Λ h₁ h₂ β _ rfl)
        (probeOldPairUpper_perm D i i Λ h₁ h₂ β _ rfl) N := by
  apply InducedCategory.hom_ext
  rw [probeOldBlockEqualCross_total, inductionModuleCross_total]
  apply congrArg Neg.neg
  exact equal_rectangle_grid
    (probeOldBlockAppend D Sc m i Λ h₁ β)
    (probeOldBlockAppend D Sc m i Λ h₂ (blockSucc D Λ i h₁ β))
    (SKM.zmod2_mul_self (D.parity i)).symm
    (probeOldBlockEqualCrossArrow_supernatural D Sc m i Λ h₁ h₂ β)
    (oldAppendToCross_supernatural D Sc (probeCutoff D m) β.1.toList i i _ _ _ _) N.obj

section Pair
variable (i j : I) (Λ : X) {a bj bi d : X}
  (h₁ : a + D.α j = bj) (h₂ : bj + D.α i = d)
  (h₃ : a + D.α i = bi) (h₄ : bi + D.α j = d)
local notation "sw" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄
local notation "hi" => probeOldBlockTarget_perm D i Λ h₃
local notation "hj" => probeOldBlockTarget_perm D j Λ h₁
local notation "hU" => probeOldPairUpper_perm D i j Λ h₁ h₂
local notation "hL" => probeOldPairUpper_perm D j i Λ h₃ h₄

/-- The selected positive block crossing is the prescribed stored-target crossing at any output. -/
theorem probeOldBlockDistinctCross_stored_total (β : WeightBlocks D Λ a)
    (ε : WeightBlocks D Λ d) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N =
      probeAppendToCrossIterated D Sc m β.1.toList j i
        (hi β _ rfl) (hj β _ rfl) (hL β ε (sw hε)) (hU β ε hε) N := by
  subst ε
  rw [probeOldBlockDistinctCross_mixed_eq D Sc m j i Λ h₃ h₄ h₁ h₂ β]
  exact probeAppendToCross_total D Sc m β.1.toList j i _ _ _ _ N

private theorem total_smul {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (a : k) (f : F ⟶ G) (N : C) :
    (a • f).total N = a • f.total N := by
  change a • f.app 0 N + a • f.app 1 N = a • (f.app 0 N + f.app 1 N)
  exact (smul_add _ _ _).symm

private theorem total_neg {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (f : F ⟶ G) (N : C) :
    (-f).total N = -f.total N := by
  change -f.app 0 N + -f.app 1 N = -(f.app 0 N + f.app 1 N)
  exact (neg_add _ _).symm

/-- On equal colours the positive rectangular weight map is the negative of the chosen crossing. -/
theorem probeOldActionEqualCross_eq_neg_distinct (i : I) (Λ : X) {a b c : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) :
    probeOldActionEqualCross D Sc m i Λ h₁ h₂ =
      -probeOldActionDistinctCross D Sc m i i Λ h₁ h₂ h₁ h₂ := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [total_neg]
  funext ε
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    change (probeOldWeightEqualCross D Sc m i Λ h₁ h₂).total M _ =
      -((probeOldActionDistinctCross D Sc m i i Λ h₁ h₂ h₁ h₂).total M (blockSucc₂ D i i Λ h₁ h₂ β))
    rw [probeOldWeightEqualCross_total_of D Sc m i Λ h₁ h₂ M β _ rfl,
      probeOldWeightEqualCrossVia_total,
      probeOldActionDistinctCross_total_of D Sc m i i Λ h₁ h₂ h₁ h₂ β _ rfl M]
    have hb := (probeOldBlockEqualCross_stored_total D Sc m i Λ h₁ h₂ β (M β)).trans
      (congrArg Neg.neg (probeOldBlockDistinctCross_stored_total D Sc m i i Λ h₁ h₂ h₁ h₂ β _ rfl (M β)).symm)
    rw [hb]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp]
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i i Λ h₁ h₂ ε hε M).eq_of_src _ _

/-- The selected equal/distinct convention is the normalization of the same positive rectangle. -/
theorem probeOldActionCross_eq_normalized_distinct :
    probeOldActionCross D Sc m Λ i j h₁ h₂ h₃ h₄ =
      (if i = j then (-1 : k) else 1) • probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ := by
  by_cases hij : i = j
  · subst j
    have he : bj = bi := h₁.symm.trans h₃
    cases he
    rw [ite_eq_left rfl, neg_one_smul, probeOldActionCross_equal,
      probeOldActionEqualCross_eq_neg_distinct]
  · rw [ite_eq_right hij, one_smul, probeOldActionCross_distinct D Sc m Λ i j hij]

/-- Every supported selected weight crossing retains its component and the equal-colour sign. -/
theorem probeOldActionCross_stored_total (β : WeightBlocks D Λ a)
    (ε : WeightBlocks D Λ d) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ProbeOldWeightProduct D Sc m Λ a) :
    (probeOldActionCross D Sc m Λ i j h₁ h₂ h₃ h₄).total M ε =
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) M) ≫
        ((if i = j then (-1 : k) else 1) • probeAppendToCrossIterated D Sc m β.1.toList j i
          (hi β _ rfl) (hj β _ rfl) (hL β ε (sw hε)) (hU β ε hε) (M β)) ≫
      eqToHom (Functor.congr_obj
        (probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε (sw hε)) M).symm := by
  rw [probeOldActionCross_eq_normalized_distinct, total_smul]
  change (if i = j then (-1 : k) else 1) •
    (probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).total M ε = _
  rw [probeOldActionDistinctCross_total_of D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε M,
    probeOldBlockDistinctCross_stored_total]
  rw [Linear.smul_comp, Linear.comp_smul]
end Pair
end OddMath.QuiverHecke
end

end

section

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
open ELV CyclotomicAction
attribute [local irreducible] ELV.BalancedInduction.induced
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

end OddMath.QuiverHecke
end

end

section

/-! # Crossing coordinates through specified intermediate OLD blocks

Brundan–Ellis (1.9): the selected crossing retains its prescribed stored-target
component through specified intermediate OLD blocks. The coordinate identity
supplies the crossing attachment needed by the two whole-weight braid paths.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

private theorem conjugation_rechart {k C : Type*} [CommRing k]
    [Category* C] [Preadditive C] [Linear k C] (c : k)
    {A B S T S' T' : C} (eS : S = S') (eT : T = T')
    (p : A = S) (q : B = T) (p' : A = S') (q' : B = T')
    (f : S ⟶ T) (f' : S' ⟶ T') (hf : HEq f f') :
    eqToHom p ≫ (c • f) ≫ eqToHom q.symm = eqToHom p' ≫ (c • f') ≫ eqToHom q'.symm := by
  cases eS
  cases eT
  have h : f = f' := eq_of_heq hf
  cases h
  rfl

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
    @Eq ((probeOldEFunctor D Sc m j Λ h₁ ⋙
        (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor).obj M ⟶
      (probeOldEFunctor D Sc m i Λ h₃ ⋙
        (probeOldInductionComponent D Sc m j Λ h₄ ε).toFunctor).obj M)
      ((probeOldActionCross D Sc m Λ i j h₁ h₂ h₃ h₄).total M ε)
      (eqToHom (probeOldWeightPairVia_obj_eq D Sc m i j Λ h₁ h₂ β δj ε hj hU M) ≫
        ((if i = j then (-1 : k) else 1) • probeAppendToCrossIterated D Sc m β.1.toList j i
          (probeOldBlockTarget_perm D i Λ h₃ β δi hi)
          (probeOldBlockTarget_perm D j Λ h₁ β δj hj)
          (probeOldBlockTarget_perm D j Λ h₄ δi ε hL)
          (probeOldBlockTarget_perm D i Λ h₂ δj ε hU) (M β)) ≫
      eqToHom (probeOldWeightPairVia_obj_eq D Sc m j i Λ h₃ h₄ β δi ε hi hL M).symm) := by
  subst δj
  subst δi
  have H := probeOldActionCross_stored_total D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hU M
  apply Eq.trans H
  apply conjugation_rechart (C := ProbeCanonicalModules D Sc m ε.1)
    (if i = j then (-1 : k) else 1)
    (S := (probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hU).obj (M β))
    (T := (probeOldBlockPairIndTo D Sc m j i Λ h₃ h₄ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hU)).obj (M β))
    (S' := (probeOldBlockPairVia D Sc m i j Λ h₁ h₂ β (blockSucc D Λ j h₁ β) ε rfl hU).obj (M β))
    (T' := (probeOldBlockPairVia D Sc m j i Λ h₃ h₄ β (blockSucc D Λ i h₃ β) ε rfl hL).obj (M β))
    rfl rfl
    (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hU) M)
    (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hU)) M)
    (probeOldWeightPairVia_obj_eq D Sc m i j Λ h₁ h₂ β (blockSucc D Λ j h₁ β) ε rfl hU M)
    (probeOldWeightPairVia_obj_eq D Sc m j i Λ h₃ h₄ β (blockSucc D Λ i h₃ β) ε rfl hL M)
  exact HEq.rfl

end Crossing
end OddMath.QuiverHecke
end

end

section

/-! # The independently whiskered OLD weight crossings in triple coordinates

Brundan–Ellis (1.9): retain the chosen prefix and suffix crossings, their
bicategorical associators, and every intermediate stored content. Each
component is compared with its prescribed evaluated append-to map.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u v w z

private theorem prefix_conjugate {C A : Type v} [Category.{w} C] [Category.{z} A]
    (G : C ⥤ A) {M₀ M₁ N₀ N₁ : C} (hM : M₀ = M₁) (hN : N₀ = N₁)
    {V W : A} (hV : V = G.obj M₀) (hW : W = G.obj N₀)
    (hV' : V = G.obj M₁) (hW' : W = G.obj N₁) (f : M₁ ⟶ N₁) :
    eqToHom hV ≫ G.map (eqToHom hM ≫ f ≫ eqToHom hN.symm) ≫ eqToHom hW.symm =
      eqToHom hV' ≫ G.map f ≫ eqToHom hW'.symm := by
  cases hM
  cases hN
  cases hV
  cases hW
  cases hV'
  cases hW'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem suffix_conjugate {k : Type u} [CommRing k]
    {C A : Type v} [Category.{w} C] [Category.{z} A] [Preadditive A] [Linear k A]
    (c : k) (F G : C ⥤ A) {M₀ M₁ : C} (hM : M₀ = M₁) {V W : A}
    (hV : V = F.obj M₀) (hW : W = G.obj M₀)
    (hV' : V = F.obj M₁) (hW' : W = G.obj M₁)
    (f : F.obj M₀ ⟶ G.obj M₀) (f' : F.obj M₁ ⟶ G.obj M₁) (hf : HEq f f') :
    eqToHom hV ≫ (c • f) ≫ eqToHom hW.symm =
      eqToHom hV' ≫ (c • f') ≫ eqToHom hW'.symm := by
  cases hM
  have h : f = f' := eq_of_heq hf
  cases h
  rfl

private theorem dependent_apply_heq {A : Sort*} {B : A → Sort*}
    (f : ∀ a, B a) {a b : A} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

private theorem reassociated_prefix_total
    {k : Type u} [CommRing k] {A B B' C E : PiSCat.{u,u,u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (F' : A ⟶ B') (G' : B' ⟶ C)
    (H : C ⟶ E) (t : F ≫ G ⟶ F' ≫ G') (M : A) :
    ((associator F G H).inv ≫ t ▷ H ≫ (associator F' G' H).hom).total M =
      H.map (t.total M) := by
  erw [PiSCat.associator_inv, PiSCat.associator_hom, Category.id_comp, Category.comp_id]
  change H.map (t.app 0 M) + H.map (t.app 1 M) = H.map (t.app 0 M + t.app 1 M)
  exact H.toFunctor.map_add.symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
section Prefix
variable (i j l : I) (Λ : X) {a bl bj c d : X}
  (hal : a + D.α l = bl) (haj : a + D.α j = bj)
  (hlj : bl + D.α j = c) (hjl : bj + D.α l = c) (hd : c + D.α i = d)
local notation "El" => probeOldE D Sc m l Λ hal
local notation "Ej" => probeOldE D Sc m j Λ haj
local notation "Uj" => probeOldE D Sc m j Λ hlj
local notation "Ul" => probeOldE D Sc m l Λ hjl
local notation "Ei" => probeOldE D Sc m i Λ hd

/-- The chosen first-pair crossing with its source and target associators retained. -/
abbrev probeOldWeightCrossPrefix : El ≫ Uj ≫ Ei ⟶ Ej ≫ Ul ≫ Ei :=
  (associator El Uj Ei).inv ≫
    probeOldActionCross D Sc m Λ j l hal hlj haj hjl ▷ Ei ≫ (associator Ej Ul Ei).hom

theorem probeOldWeightCrossPrefix_total (M : ProbeOldWeightProduct D Sc m Λ a)
    (ε : WeightBlocks D Λ d) :
    (probeOldWeightCrossPrefix D Sc m i j l Λ hal haj hlj hjl hd).total M ε =
      (probeOldInductionComponent D Sc m i Λ hd ε).map
        ((probeOldActionCross D Sc m Λ j l hal hlj haj hjl).total M) :=
  congrFun (reassociated_prefix_total El Uj Ej Ul Ei
    (probeOldActionCross D Sc m Λ j l hal hlj haj hjl) M) ε

/-- The independent first-pair crossing uses the same two prescribed triple coordinates. -/
theorem probeOldWeightCrossPrefix_via_total (β : WeightBlocks D Λ a)
    (δl : WeightBlocks D Λ bl) (δj : WeightBlocks D Λ bj)
    (δ : WeightBlocks D Λ c) (ε : WeightBlocks D Λ d)
    (hδl : blockSucc D Λ l hal β = δl) (hδj : blockSucc D Λ j haj β = δj)
    (hδs : blockSucc D Λ j hlj δl = δ) (hδt : blockSucc D Λ l hjl δj = δ)
    (hε : blockSucc D Λ i hd δ = ε) (M : ProbeOldWeightProduct D Sc m Λ a) :
    (probeOldWeightCrossPrefix D Sc m i j l Λ hal haj hlj hjl hd).total M ε =
      eqToHom (probeOldWeightTripleVia_obj_eq D Sc m i j l Λ hal hlj hd β δl δ ε hδl hδs hε M) ≫
        (probeEvaluatedAppendTo D Sc m δ.1.toList i ε.1.toList
            (probeOldBlockTarget_perm D i Λ hd δ ε hε)).map
          ((if j = l then (-1 : k) else 1) • probeAppendToCrossIterated D Sc m β.1.toList l j
            (probeOldBlockTarget_perm D j Λ haj β δj hδj)
            (probeOldBlockTarget_perm D l Λ hal β δl hδl)
            (probeOldBlockTarget_perm D l Λ hjl δj δ hδt)
            (probeOldBlockTarget_perm D j Λ hlj δl δ hδs) (M β)) ≫
      eqToHom (probeOldWeightTripleVia_obj_eq D Sc m i l j Λ haj hjl hd β δj δ ε hδj hδt hε M).symm := by
  rw [probeOldWeightCrossPrefix_total, probeOldInductionComponent_map_of D Sc m i Λ hd δ ε hε,
    probeOldActionCross_via_total D Sc m j l Λ hal hlj haj hjl β δl δj δ hδl hδj hδs hδt]
  exact prefix_conjugate (probeOldBlockIndTo D Sc m i Λ hd δ ε hε).toFunctor
    (probeOldWeightPairVia_obj_eq D Sc m j l Λ hal hlj β δl δ hδl hδs M)
    (probeOldWeightPairVia_obj_eq D Sc m l j Λ haj hjl β δj δ hδj hδt M)
    (probeOldInductionComponent_obj_of D Sc m i Λ hd δ ε hε ((El ≫ Uj).obj M))
    (probeOldInductionComponent_obj_of D Sc m i Λ hd δ ε hε ((Ej ≫ Ul).obj M))
    (probeOldWeightTripleVia_obj_eq D Sc m i j l Λ hal hlj hd β δl δ ε hδl hδs hε M)
    (probeOldWeightTripleVia_obj_eq D Sc m i l j Λ haj hjl hd β δj δ ε hδj hδt hε M) _
end Prefix

section Suffix
variable (i j l : I) (Λ : X) {a b cj ci d : X}
  (hal : a + D.α l = b) (hlj : b + D.α j = cj) (hli : b + D.α i = ci)
  (hji : cj + D.α i = d) (hij : ci + D.α j = d)
local notation "El" => probeOldE D Sc m l Λ hal
local notation "Ej" => probeOldE D Sc m j Λ hlj
local notation "Ei" => probeOldE D Sc m i Λ hli
local notation "Ui" => probeOldE D Sc m i Λ hji
local notation "Uj" => probeOldE D Sc m j Λ hij

/-- The chosen last-pair crossing after the independently chosen first induction. -/
abbrev probeOldWeightCrossSuffix : El ≫ Ej ≫ Ui ⟶ El ≫ Ei ≫ Uj :=
  El ◁ probeOldActionCross D Sc m Λ i j hlj hji hli hij

theorem probeOldWeightCrossSuffix_total (M : ProbeOldWeightProduct D Sc m Λ a)
    (ε : WeightBlocks D Λ d) :
    (probeOldWeightCrossSuffix D Sc m i j l Λ hal hlj hli hji hij).total M ε =
      (probeOldActionCross D Sc m Λ i j hlj hji hli hij).total ((El).obj M) ε := rfl

/-- The independent last-pair crossing uses the same two prescribed triple coordinates. -/
theorem probeOldWeightCrossSuffix_via_total (β : WeightBlocks D Λ a)
    (δl : WeightBlocks D Λ b) (δj : WeightBlocks D Λ cj) (δi : WeightBlocks D Λ ci)
    (ε : WeightBlocks D Λ d) (hδl : blockSucc D Λ l hal β = δl)
    (hδj : blockSucc D Λ j hlj δl = δj) (hδi : blockSucc D Λ i hli δl = δi)
    (hεs : blockSucc D Λ i hji δj = ε) (hεt : blockSucc D Λ j hij δi = ε)
    (M : ProbeOldWeightProduct D Sc m Λ a) :
    (probeOldWeightCrossSuffix D Sc m i j l Λ hal hlj hli hji hij).total M ε =
      eqToHom (probeOldWeightTripleVia_obj_eq D Sc m i j l Λ hal hlj hji β δl δj ε hδl hδj hεs M) ≫
        ((if i = j then (-1 : k) else 1) • probeAppendToCrossIterated D Sc m δl.1.toList j i
          (probeOldBlockTarget_perm D i Λ hli δl δi hδi)
          (probeOldBlockTarget_perm D j Λ hlj δl δj hδj)
          (probeOldBlockTarget_perm D j Λ hij δi ε hεt)
          (probeOldBlockTarget_perm D i Λ hji δj ε hεs)
          ((probeEvaluatedAppendTo D Sc m β.1.toList l δl.1.toList
            (probeOldBlockTarget_perm D l Λ hal β δl hδl)).obj (M β))) ≫
      eqToHom (probeOldWeightTripleVia_obj_eq D Sc m j i l Λ hal hli hij β δl δi ε hδl hδi hεt M).symm := by
  rw [probeOldWeightCrossSuffix_total,
    probeOldActionCross_via_total D Sc m i j Λ hlj hji hli hij δl δj δi ε hδj hδi hεs hεt]
  apply suffix_conjugate (if i = j then (-1 : k) else 1)
    (probeOldBlockPairVia D Sc m i j Λ hlj hji δl δj ε hδj hεs).toFunctor
    (probeOldBlockPairVia D Sc m j i Λ hli hij δl δi ε hδi hεt).toFunctor
    (probeOldInductionComponent_obj_of D Sc m l Λ hal β δl hδl M)
    (probeOldWeightPairVia_obj_eq D Sc m i j Λ hlj hji δl δj ε hδj hεs ((El).obj M))
    (probeOldWeightPairVia_obj_eq D Sc m j i Λ hli hij δl δi ε hδi hεt ((El).obj M))
    (probeOldWeightTripleVia_obj_eq D Sc m i j l Λ hal hlj hji β δl δj ε hδl hδj hεs M)
    (probeOldWeightTripleVia_obj_eq D Sc m j i l Λ hal hli hij β δl δi ε hδl hδi hεt M)
  exact dependent_apply_heq
    (probeAppendToCrossIterated D Sc m δl.1.toList j i
      (probeOldBlockTarget_perm D i Λ hli δl δi hδi)
      (probeOldBlockTarget_perm D j Λ hlj δl δj hδj)
      (probeOldBlockTarget_perm D j Λ hij δi ε hεt)
      (probeOldBlockTarget_perm D i Λ hji δj ε hεs))
    (probeOldInductionComponent_obj_of D Sc m l Λ hal β δl hδl M)
end Suffix
end OddMath.QuiverHecke
end

end

section

/-! # The uncorrected probe braid at twelve stored append edges

Brundan–Ellis (1.9): arbitrary representatives at all eight content
vertices retain the literal quotient braid. Each equal pair is negative
and each distinct pair positive. No braid or comparison premise is added.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor
universe u
private theorem cube_degree_congr
    {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ E} {p q : ZMod 2} (hp : p = q)
    {γ : ∀ s, F.obj s ⟶ G.obj s} (hγ : IsSupernatural k p γ) : IsSupernatural k q γ := by
  cases hp
  exact hγ
private theorem cube_scaled_paths {k : Type u} [CommRing k]
    {C : Type*} [Category* C] [Preadditive C] [Linear k C]
    {X₀ X₁ X₂ X₃ X₄ X₅ : C} (a b c : k)
    (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₀ : X₀ ⟶ X₄) (g₁ : X₄ ⟶ X₅) (g₂ : X₅ ⟶ X₃)
    (hb : f₀ ≫ f₁ ≫ f₂ = g₀ ≫ g₁ ≫ g₂) :
    (a • f₀) ≫ (b • f₁) ≫ (c • f₂) = (c • g₀) ≫ (b • g₁) ≫ (a • g₂) := by
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
  rw [hb]
  congr 1
  ring

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i j l : I) {νi νj νl νij νil νjl νt : List I}
  (hI : (i :: ν).Perm νi) (hJ : (j :: ν).Perm νj) (hL : (l :: ν).Perm νl)
  (hIJ : (j :: νi).Perm νij) (hJI : (i :: νj).Perm νij)
  (hIL : (l :: νi).Perm νil) (hLI : (i :: νl).Perm νil)
  (hJL : (l :: νj).Perm νjl) (hLJ : (j :: νl).Perm νjl)
  (hTopL : (l :: νij).Perm νt) (hTopJ : (j :: νil).Perm νt) (hTopI : (i :: νjl).Perm νt)
local notation "Sc'" => parameterTwist D Sc
local notation "cut" => probeCutoff D m
local notation "Ai" => oldContentAppendTo D Sc' cut ν i νi hI
local notation "Aj" => oldContentAppendTo D Sc' cut ν j νj hJ
local notation "Al" => oldContentAppendTo D Sc' cut ν l νl hL
local notation "Bij_i" => oldContentAppendTo D Sc' cut νi j νij hIJ
local notation "Bij_j" => oldContentAppendTo D Sc' cut νj i νij hJI
local notation "Bil_i" => oldContentAppendTo D Sc' cut νi l νil hIL
local notation "Bil_l" => oldContentAppendTo D Sc' cut νl i νil hLI
local notation "Bjl_j" => oldContentAppendTo D Sc' cut νj l νjl hJL
local notation "Bjl_l" => oldContentAppendTo D Sc' cut νl j νjl hLJ
local notation "Cl" => oldContentAppendTo D Sc' cut νij l νt hTopL
local notation "Cj" => oldContentAppendTo D Sc' cut νil j νt hTopJ
local notation "Ci" => oldContentAppendTo D Sc' cut νjl i νt hTopI
local notation "α₀" => oldAppendToCross D Sc' cut ν j i hI hJ hIJ hJI
local notation "hα₀" => cube_degree_congr (mul_comm (D.parity j) (D.parity i))
  (oldAppendToCross_supernatural D Sc' cut ν j i hI hJ hIJ hJI)
local notation "α₁" => oldAppendToCross D Sc' cut νj l i hJI hJL hTopL hTopI
local notation "hα₁" => cube_degree_congr (mul_comm (D.parity l) (D.parity i))
  (oldAppendToCross_supernatural D Sc' cut νj l i hJI hJL hTopL hTopI)
local notation "α₂" => oldAppendToCross D Sc' cut ν l j hJ hL hJL hLJ
local notation "hα₂" => cube_degree_congr (mul_comm (D.parity l) (D.parity j))
  (oldAppendToCross_supernatural D Sc' cut ν l j hJ hL hJL hLJ)
local notation "β₀" => oldAppendToCross D Sc' cut νi l j hIJ hIL hTopL hTopJ
local notation "hβ₀" => cube_degree_congr (mul_comm (D.parity l) (D.parity j))
  (oldAppendToCross_supernatural D Sc' cut νi l j hIJ hIL hTopL hTopJ)
local notation "β₁" => oldAppendToCross D Sc' cut ν l i hI hL hIL hLI
local notation "hβ₁" => cube_degree_congr (mul_comm (D.parity l) (D.parity i))
  (oldAppendToCross_supernatural D Sc' cut ν l i hI hL hIL hLI)
local notation "β₂" => oldAppendToCross D Sc' cut νl j i hLI hLJ hTopJ hTopI
local notation "hβ₂" => cube_degree_congr (mul_comm (D.parity j) (D.parity i))
  (oldAppendToCross_supernatural D Sc' cut νl j i hLI hLJ hTopJ hTopI)

/-- The twelve certificates retain the quotient's literal source equation. -/
theorem probeStoredBraid_source (hb : ¬ (i = l ∧ i ≠ j))
    (s : OldContentCategory D Sc' cut ν) :
    (Cl).map (α₀ s) ≫ α₁ ((Aj).obj s) ≫ (Ci).map (α₂ s) =
      β₀ ((Ai).obj s) ≫ (Cj).map (β₁ s) ≫ β₂ ((Al).obj s) := by
  change triplePrefix D Sc' cut i j l s.obj ≫ tripleSuffix D Sc' cut j i l s.obj ≫
      triplePrefix D Sc' cut j l i s.obj =
    tripleSuffix D Sc' cut i j l s.obj ≫ triplePrefix D Sc' cut i l j s.obj ≫
      tripleSuffix D Sc' cut l i j s.obj
  exact ELV.CyclotomicCrossingTensor.tripleCross_braid D Sc' cut i j l hb s.obj

/-- The first path uses the three separately normalized stored pair crossings. -/
def probeOldStoredBraidLeft (N : Superfunctor k (OldContentCategory D Sc' cut ν) (SVec k)) :
    induced Ci (induced Bjl_l (induced Al N)) ⟶ induced Cl (induced Bij_i (induced Ai N)) :=
  ((if j = l then (-1 : k) else 1) •
    (induction Ci).map (rectangularCrossComponent Aj Al Bjl_j Bjl_l hα₂ N)) ≫
  ((if i = l then (-1 : k) else 1) •
    rectangularCrossComponent Bij_j Bjl_j Cl Ci hα₁ ((induction Aj).obj N)) ≫
  ((if i = j then (-1 : k) else 1) •
    (induction Cl).map (rectangularCrossComponent Ai Aj Bij_i Bij_j hα₀ N))

/-- The reverse three-pair path uses the other intermediate stored vertices. -/
def probeOldStoredBraidRight (N : Superfunctor k (OldContentCategory D Sc' cut ν) (SVec k)) :
    induced Ci (induced Bjl_l (induced Al N)) ⟶ induced Cl (induced Bij_i (induced Ai N)) :=
  ((if i = j then (-1 : k) else 1) •
    rectangularCrossComponent Bil_l Bjl_l Cj Ci hβ₂ ((induction Al).obj N)) ≫
  ((if i = l then (-1 : k) else 1) •
    (induction Cj).map (rectangularCrossComponent Ai Al Bil_i Bil_l hβ₁ N)) ≫
  ((if j = l then (-1 : k) else 1) •
    rectangularCrossComponent Bij_i Bil_i Cl Cj hβ₀ ((induction Ai).obj N))

/-- Arbitrary stored representatives preserve the uncorrected normalized braid. -/
theorem probeOldStoredBraid (hb : ¬ (i = l ∧ i ≠ j))
    (N : Superfunctor k (OldContentCategory D Sc' cut ν) (SVec k)) :
    probeOldStoredBraidLeft D Sc m ν i j l hI hJ hL hIJ hJI hJL hLJ hTopL hTopI N =
      probeOldStoredBraidRight D Sc m ν i j l hI hL hIJ hIL hLI hLJ hTopL hTopJ hTopI N := by
  have hpos := inductionCube_braid Ai Aj Al Bij_i Bij_j Bil_i Bil_l Bjl_j Bjl_l Cl Cj Ci
    hα₀ hα₁ hα₂ hβ₀ hβ₁ hβ₂
    (probeStoredBraid_source D Sc m ν i j l hI hJ hL hIJ hJI hIL hLI hJL hLJ hTopL hTopJ hTopI hb) N
  exact cube_scaled_paths (if j = l then (-1 : k) else 1) (if i = l then (-1 : k) else 1)
    (if i = j then (-1 : k) else 1) _ _ _ _ _ _ hpos

end OddMath.QuiverHecke
end

end

section

/-! # The uncorrected evaluated braid at arbitrary stored representatives

Brundan–Ellis (1.9): the twelve chosen evaluated append edges retain the
normalized OLD braid, with independently negative equal pair crossings.
All maps are the prescribed probe crossing components; no relation premise
is supplied in the final statement.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor
universe u
private theorem rectangle_degree_congr
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (M : B ⥤ E) [M.Additive] [M.Linear k] [IsSuperfunctor k M]
    {p q : ZMod 2} (hp : p = q) {γ : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ M).obj s}
    (hγ : IsSupernatural k p γ) (hδ : IsSupernatural k q γ)
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L M hγ N = rectangularCrossComponent J K L M hδ N := by
  cases hp
  rfl

private theorem appendTo_obj_obj
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
    (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ)
    (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeEvaluatedAppendTo D Sc m ν i μ h).obj N).obj =
      induced (oldContentAppendTo D Sc (probeCutoff D m) ν i μ h) N.obj := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i j l : I) {νi νj νl νij νil νjl νt : List I}
  (hI : (i :: ν).Perm νi) (hJ : (j :: ν).Perm νj) (hL : (l :: ν).Perm νl)
  (hIJ : (j :: νi).Perm νij) (hJI : (i :: νj).Perm νij)
  (hIL : (l :: νi).Perm νil) (hLI : (i :: νl).Perm νil)
  (hJL : (l :: νj).Perm νjl) (hLJ : (j :: νl).Perm νjl)
  (hTopL : (l :: νij).Perm νt) (hTopJ : (j :: νil).Perm νt) (hTopI : (i :: νjl).Perm νt)
local notation "Sc'" => parameterTwist D Sc
local notation "cut" => probeCutoff D m
local notation "Ai" => oldContentAppendTo D Sc' cut ν i νi hI
local notation "Aj" => oldContentAppendTo D Sc' cut ν j νj hJ
local notation "Al" => oldContentAppendTo D Sc' cut ν l νl hL
local notation "Bij_i" => oldContentAppendTo D Sc' cut νi j νij hIJ
local notation "Bij_j" => oldContentAppendTo D Sc' cut νj i νij hJI
local notation "Bil_i" => oldContentAppendTo D Sc' cut νi l νil hIL
local notation "Bil_l" => oldContentAppendTo D Sc' cut νl i νil hLI
local notation "Bjl_j" => oldContentAppendTo D Sc' cut νj l νjl hJL
local notation "Bjl_l" => oldContentAppendTo D Sc' cut νl j νjl hLJ
local notation "Cl" => oldContentAppendTo D Sc' cut νij l νt hTopL
local notation "Cj" => oldContentAppendTo D Sc' cut νil j νt hTopJ
local notation "Ci" => oldContentAppendTo D Sc' cut νjl i νt hTopI
local notation "EAi" => probeEvaluatedAppendTo D Sc' m ν i νi hI
local notation "EAj" => probeEvaluatedAppendTo D Sc' m ν j νj hJ
local notation "EAl" => probeEvaluatedAppendTo D Sc' m ν l νl hL
local notation "EBij_i" => probeEvaluatedAppendTo D Sc' m νi j νij hIJ
local notation "EBij_j" => probeEvaluatedAppendTo D Sc' m νj i νij hJI
local notation "EBil_i" => probeEvaluatedAppendTo D Sc' m νi l νil hIL
local notation "EBil_l" => probeEvaluatedAppendTo D Sc' m νl i νil hLI
local notation "EBjl_j" => probeEvaluatedAppendTo D Sc' m νj l νjl hJL
local notation "EBjl_l" => probeEvaluatedAppendTo D Sc' m νl j νjl hLJ
local notation "ECl" => probeEvaluatedAppendTo D Sc' m νij l νt hTopL
local notation "ECj" => probeEvaluatedAppendTo D Sc' m νil j νt hTopJ
local notation "ECi" => probeEvaluatedAppendTo D Sc' m νjl i νt hTopI

/-- The first literal evaluated three-crossing path. -/
def probeStoredBraidLeft (N : ProbeEvaluatedModules D Sc' m ν) :
    (ECi).obj ((EBjl_l).obj ((EAl).obj N)) ⟶ (ECl).obj ((EBij_i).obj ((EAi).obj N)) :=
  ((if j = l then (-1 : k) else 1) • (ECi).map
    (probeAppendToCrossIterated D Sc' m ν l j hJ hL hJL hLJ N)) ≫
  ((if i = l then (-1 : k) else 1) •
    probeAppendToCrossIterated D Sc' m νj l i hJI hJL hTopL hTopI ((EAj).obj N)) ≫
  ((if i = j then (-1 : k) else 1) • (ECl).map
    (probeAppendToCrossIterated D Sc' m ν j i hI hJ hIJ hJI N))

/-- The second path has independent intermediate representatives at the other cube vertices. -/
def probeStoredBraidRight (N : ProbeEvaluatedModules D Sc' m ν) :
    (ECi).obj ((EBjl_l).obj ((EAl).obj N)) ⟶ (ECl).obj ((EBij_i).obj ((EAi).obj N)) :=
  ((if i = j then (-1 : k) else 1) •
    probeAppendToCrossIterated D Sc' m νl j i hLI hLJ hTopJ hTopI ((EAl).obj N)) ≫
  ((if i = l then (-1 : k) else 1) • (ECj).map
    (probeAppendToCrossIterated D Sc' m ν l i hI hL hIL hLI N)) ≫
  ((if j = l then (-1 : k) else 1) •
    probeAppendToCrossIterated D Sc' m νi l j hIJ hIL hTopL hTopJ ((EAi).obj N))

/-- The first evaluated path retains the entire OLD module map. -/
theorem probeStoredBraidLeft_eq (N : ProbeEvaluatedModules D Sc' m ν) :
    (probeStoredBraidLeft D Sc m ν i j l hI hJ hL hIJ hJI hJL hLJ hTopL hTopI N).hom =
      probeOldStoredBraidLeft D Sc m ν i j l hI hJ hL hIJ hJI hJL hLJ hTopL hTopI N.obj := by
  simp only [probeStoredBraidLeft, appendTo_obj_obj]
  unfold probeOldStoredBraidLeft
  apply congrArg₂ (fun f g => f ≫ g)
  · exact congrArg (fun f => (if j = l then (-1 : k) else 1) • (induction Ci).map f)
      (rectangle_degree_congr Aj Al Bjl_j Bjl_l (mul_comm (D.parity l) (D.parity j)) _ _ _)
  · apply congrArg₂ (fun f g => f ≫ g)
    · exact congrArg (fun f => (if i = l then (-1 : k) else 1) • f)
        (rectangle_degree_congr Bij_j Bjl_j Cl Ci (mul_comm (D.parity l) (D.parity i)) _ _ _)
    · exact congrArg (fun f => (if i = j then (-1 : k) else 1) • (induction Cl).map f)
        (rectangle_degree_congr Ai Aj Bij_i Bij_j (mul_comm (D.parity j) (D.parity i)) _ _ _)

/-- The second evaluated path retains the same independent OLD arrows. -/
theorem probeStoredBraidRight_eq (N : ProbeEvaluatedModules D Sc' m ν) :
    (probeStoredBraidRight D Sc m ν i j l hI hL hIJ hIL hLI hLJ hTopL hTopJ hTopI N).hom =
      probeOldStoredBraidRight D Sc m ν i j l hI hL hIJ hIL hLI hLJ hTopL hTopJ hTopI N.obj := by
  simp only [probeStoredBraidRight, appendTo_obj_obj]
  unfold probeOldStoredBraidRight
  apply congrArg₂ (fun f g => f ≫ g)
  · exact congrArg (fun f => (if i = j then (-1 : k) else 1) • f)
      (rectangle_degree_congr Bil_l Bjl_l Cj Ci (mul_comm (D.parity j) (D.parity i)) _ _ _)
  · apply congrArg₂ (fun f g => f ≫ g)
    · exact congrArg (fun f => (if i = l then (-1 : k) else 1) • (induction Cj).map f)
        (rectangle_degree_congr Ai Al Bil_i Bil_l (mul_comm (D.parity l) (D.parity i)) _ _ _)
    · exact congrArg (fun f => (if j = l then (-1 : k) else 1) • f)
        (rectangle_degree_congr Bij_i Bil_i Cl Cj (mul_comm (D.parity l) (D.parity j)) _ _ _)

/-- The prescribed evaluated crossing components satisfy the uncorrected braid. -/
theorem probeStoredBraid (hb : ¬ (i = l ∧ i ≠ j)) (N : ProbeEvaluatedModules D Sc' m ν) :
    probeStoredBraidLeft D Sc m ν i j l hI hJ hL hIJ hJI hJL hLJ hTopL hTopI N =
      probeStoredBraidRight D Sc m ν i j l hI hL hIJ hIL hLI hLJ hTopL hTopJ hTopI N := by
  apply InducedCategory.hom_ext
  rw [probeStoredBraidLeft_eq, probeStoredBraidRight_eq]
  exact probeOldStoredBraid D Sc m ν i j l hI hJ hL hIJ hJI hIL hLI hJL hLJ hTopL hTopJ hTopI hb N.obj

end OddMath.QuiverHecke
end

end

section

/-! # The three prescribed OLD weight dots in one triple coordinate

Brundan–Ellis (1.9): retain the independently whiskered first, middle
and last signed dots in the same selected triple coordinate. These
identities precede transport of the ordered correction polynomial.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
attribute [local irreducible] ELV.BalancedInduction.induced
universe u v w z
private theorem inner_conjugate {C A : Type v} [Category.{w} C] [Category.{z} A]
    (G : C ⥤ A) {M₀ M₁ : C} (hM : M₀ = M₁) {V : A}
    (hV : V = G.obj M₀) (hW : V = G.obj M₁) (f : End M₁) :
    eqToHom hV ≫ G.map (eqToHom hM ≫ f ≫ eqToHom hM.symm) ≫ eqToHom hV.symm =
      eqToHom hW ≫ G.map f ≫ eqToHom hW.symm := by
  cases hM
  cases hV
  cases hW
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem outer_conjugate {C A : Type v} [Category.{w} C] [Category.{z} A]
    (G : C ⥤ A) {M₀ M₁ : C} (hM : M₀ = M₁) {V : A}
    (hV : V = G.obj M₀) (hW : V = G.obj M₁) (f : ∀ M, End (G.obj M)) :
    eqToHom hV ≫ f M₀ ≫ eqToHom hV.symm =
      eqToHom hW ≫ f M₁ ≫ eqToHom hW.symm := by
  cases hM
  cases hV
  cases hW
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j l : I) (Λ : X) {a b c d : X}
  (h₁ : a + D.α l = b) (h₂ : b + D.α j = c) (h₃ : c + D.α i = d)
local notation "E₁" => probeOldE D Sc m l Λ h₁
local notation "E₂" => probeOldE D Sc m j Λ h₂
local notation "E₃" => probeOldE D Sc m i Λ h₃

/-- The prescribed signed dot in the first induction position. -/
abbrev probeOldWeightTripleFirstDot : End (E₁ ≫ E₂ ≫ E₃) :=
  probeOldActionDot D Sc m l Λ h₁ ▷ (E₂ ≫ E₃)

/-- The independently chosen signed dot in the middle induction position. -/
abbrev probeOldWeightTripleMiddleDot : End (E₁ ≫ E₂ ≫ E₃) :=
  E₁ ◁ (probeOldActionDot D Sc m j Λ h₂ ▷ E₃)

/-- The independently chosen signed dot in the last induction position. -/
abbrev probeOldWeightTripleLastDot : End (E₁ ≫ E₂ ≫ E₃) :=
  E₁ ◁ E₂ ◁ probeOldActionDot D Sc m i Λ h₃

theorem probeOldWeightTripleFirstDot_total (M : ProbeOldWeightProduct D Sc m Λ a)
    (ε : WeightBlocks D Λ d) :
    (probeOldWeightTripleFirstDot D Sc m i j l Λ h₁ h₂ h₃).total M ε =
      (probeOldInductionComponent D Sc m i Λ h₃ ε).map
        ((probeOldActionDot D Sc m l Λ h₁ ▷ E₂).total M) := by
  change (probeOldInductionComponent D Sc m i Λ h₃ ε).map
      ((probeOldActionDot D Sc m l Λ h₁ ▷ E₂).app 0 M) +
    (probeOldInductionComponent D Sc m i Λ h₃ ε).map
      ((probeOldActionDot D Sc m l Λ h₁ ▷ E₂).app 1 M) = _
  exact (probeOldInductionComponent D Sc m i Λ h₃ ε).toFunctor.map_add |>.symm

theorem probeOldWeightTripleMiddleDot_total (M : ProbeOldWeightProduct D Sc m Λ a)
    (ε : WeightBlocks D Λ d) :
    (probeOldWeightTripleMiddleDot D Sc m i j l Λ h₁ h₂ h₃).total M ε =
      (probeOldInductionComponent D Sc m i Λ h₃ ε).map
        ((E₁ ◁ probeOldActionDot D Sc m j Λ h₂).total M) := by
  change (probeOldInductionComponent D Sc m i Λ h₃ ε).map
      ((E₁ ◁ probeOldActionDot D Sc m j Λ h₂).app 0 M) +
    (probeOldInductionComponent D Sc m i Λ h₃ ε).map
      ((E₁ ◁ probeOldActionDot D Sc m j Λ h₂).app 1 M) = _
  exact (probeOldInductionComponent D Sc m i Λ h₃ ε).toFunctor.map_add |>.symm

theorem probeOldWeightTripleLastDot_total (M : ProbeOldWeightProduct D Sc m Λ a)
    (ε : WeightBlocks D Λ d) :
    (probeOldWeightTripleLastDot D Sc m i j l Λ h₁ h₂ h₃).total M ε =
      (probeOldActionDot D Sc m i Λ h₃).total ((E₁ ≫ E₂).obj M) ε := rfl

variable (β : WeightBlocks D Λ a)
local notation "δ₁" => blockSucc D Λ l h₁ β
local notation "δ₂" => blockSucc₂ D j l Λ h₁ h₂ β
local notation "ε" => probeOldBlockSucc₃ D i j l Λ h₁ h₂ h₃ β
local notation "B₁" => probeOldBlockInd D Sc m l Λ h₁ β
local notation "B₂" => probeOldBlockInd D Sc m j Λ h₂ δ₁
local notation "B₃" => probeOldBlockInd D Sc m i Λ h₃ δ₂
local notation "α" => probeAppendToDotComponent D Sc m (Multiset.toList (Subtype.val β)) l (Multiset.toList (Subtype.val δ₁))
  (probeOldBlockTarget_perm D l Λ h₁ β δ₁ rfl)
local notation "βdot" => probeAppendToDotComponent D Sc m (Multiset.toList (Subtype.val δ₁)) j (Multiset.toList (Subtype.val δ₂))
  (probeOldBlockTarget_perm D j Λ h₂ δ₁ δ₂ rfl)
local notation "γ" => probeAppendToDotComponent D Sc m (Multiset.toList (Subtype.val δ₂)) i (Multiset.toList (Subtype.val ε))
  (probeOldBlockTarget_perm D i Λ h₃ δ₂ ε rfl)
local notation "eq₃" => probeOldWeightTriple_obj_eq D Sc m i j l Λ h₁ h₂ h₃ β

/-- The first independently whiskered dot retains the actual first append component. -/
theorem probeOldWeightTripleFirstDot_component (M : ProbeOldWeightProduct D Sc m Λ a) :
    (probeOldWeightTripleFirstDot D Sc m i j l Λ h₁ h₂ h₃).total M ε =
      eqToHom (eq₃ M) ≫ (B₃).map ((B₂).map (α (M β))) ≫ eqToHom (eq₃ M).symm := by
  rw [probeOldWeightTripleFirstDot_total, probeOldInductionComponent_map_blockSucc,
    probeOldPairInnerDotTo_total D Sc m j l Λ h₁ h₂ β δ₂ rfl M]
  have hn : (probeOldBlockPairInnerDotTo D Sc m j l Λ h₁ h₂ β δ₂ rfl).total (M β) =
      (B₂).map (α (M β)) := by
    change (B₂).map ((probeOldBlockDot D Sc m l Λ h₁ β).app 0 (M β)) +
      (B₂).map ((probeOldBlockDot D Sc m l Λ h₁ β).app 1 (M β)) = _
    rw [← Functor.map_add]
    exact congrArg (B₂).map (probeOldBlockDot_stored_total D Sc m l Λ h₁ β (M β))
  rw [hn]
  exact inner_conjugate (B₃).toFunctor (probeOldWeightPair₂_obj_eq D Sc m j l Λ h₁ h₂ β M)
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₃ δ₂ ((E₁ ≫ E₂).obj M))
    (eq₃ M) _

/-- The middle independently whiskered dot retains the actual second append component. -/
theorem probeOldWeightTripleMiddleDot_component (M : ProbeOldWeightProduct D Sc m Λ a) :
    (probeOldWeightTripleMiddleDot D Sc m i j l Λ h₁ h₂ h₃).total M ε =
      eqToHom (eq₃ M) ≫ (B₃).map (βdot ((B₁).obj (M β))) ≫ eqToHom (eq₃ M).symm := by
  rw [probeOldWeightTripleMiddleDot_total, probeOldInductionComponent_map_blockSucc,
    probeOldPairOuterDotTo_total D Sc m j l Λ h₁ h₂ β δ₂ rfl M]
  have hn : (probeOldBlockPairOuterDotTo D Sc m j l Λ h₁ h₂ β δ₂ rfl).total (M β) =
      βdot ((B₁).obj (M β)) :=
    probeAppendToInductionDot_total D Sc m (Multiset.toList (Subtype.val δ₁)) j (Multiset.toList (Subtype.val δ₂)) _ ((B₁).obj (M β))
  rw [hn]
  exact inner_conjugate (B₃).toFunctor (probeOldWeightPair₂_obj_eq D Sc m j l Λ h₁ h₂ β M)
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₃ δ₂ ((E₁ ≫ E₂).obj M))
    (eq₃ M) _

/-- The last independently whiskered dot retains the actual third append component. -/
theorem probeOldWeightTripleLastDot_component (M : ProbeOldWeightProduct D Sc m Λ a) :
    (probeOldWeightTripleLastDot D Sc m i j l Λ h₁ h₂ h₃).total M ε =
      eqToHom (eq₃ M) ≫ γ ((B₂).obj ((B₁).obj (M β))) ≫ eqToHom (eq₃ M).symm := by
  rw [probeOldWeightTripleLastDot_total, probeOldActionDot_via_total D Sc m i Λ h₃ δ₂ ε rfl]
  exact outer_conjugate (B₃).toFunctor (probeOldWeightPair₂_obj_eq D Sc m j l Λ h₁ h₂ β M)
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₃ δ₂ ((E₁ ≫ E₂).obj M))
    (eq₃ M) γ

end OddMath.QuiverHecke
end

end

section

/-! # The corrected probe braid with seven prescribed stored append edges

Brundan–Ellis (1.9): the actual OLD fixed-content induction grid uses
arbitrary stored representatives at all six vertices. The literal OLD
coefficient braid supplies the source equation and the original-Sc
ordered correction uses the three independent chosen append dots.
No braid, naturality, comparison or inverse premise is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor
universe u

private theorem stored_degree_congr
    {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ E} {p q : ZMod 2} (hp : p = q)
    {γ : ∀ s, F.obj s ⟶ G.obj s} (hγ : IsSupernatural k p γ) : IsSupernatural k q γ := by
  cases hp
  exact hγ

private def storedEndForget
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cut : I → ℕ) (ν : List I)
    (v : OldContentCategory D Sc cut ν) : End v →ₐ[k] End v.obj :=
  AlgHom.ofLinearMap
    { toFun := fun f => f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    rfl (fun _ _ => rfl)

private theorem storedEndForget_injective
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cut : I → ℕ) (ν : List I)
    (v : OldContentCategory D Sc cut ν) : Function.Injective (storedEndForget D Sc cut ν v) :=
  fun _ _ h => h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i j : I) {νi νj νii νij νt : List I}
  (hI : (i :: ν).Perm νi) (hJ : (j :: ν).Perm νj)
  (hII : (i :: νi).Perm νii) (hIJ : (j :: νi).Perm νij) (hJI : (i :: νj).Perm νij)
  (hTopJ : (j :: νii).Perm νt) (hTopI : (i :: νij).Perm νt)
local notation "Sc'" => parameterTwist D Sc
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc' cut ν i νi hI
local notation "K" => oldContentAppendTo D Sc' cut ν j νj hJ
local notation "U" => oldContentAppendTo D Sc' cut νi i νii hII
local notation "V" => oldContentAppendTo D Sc' cut νi j νij hIJ
local notation "W" => oldContentAppendTo D Sc' cut νj i νij hJI
local notation "L" => oldContentAppendTo D Sc' cut νii j νt hTopJ
local notation "M" => oldContentAppendTo D Sc' cut νij i νt hTopI
local notation "F₀" => (J ⋙ V) ⋙ M
local notation "σ" => oldAppendToCross D Sc' cut ν j i hI hJ hIJ hJI
local notation "σ'" => oldAppendToCross D Sc' cut ν i j hJ hI hJI hIJ
local notation "τ" => oldAppendToCross D Sc' cut ν i i hI hI hII hII
local notation "ρ" => oldAppendToCross D Sc' cut νi i j hIJ hII hTopI hTopJ
local notation "ρ'" => oldAppendToCross D Sc' cut νi j i hII hIJ hTopJ hTopI
local notation "ξ" => oldAppendToCross D Sc' cut νj i i hJI hJI hTopI hTopI
local notation "hσ" => stored_degree_congr (mul_comm (D.parity j) (D.parity i))
  (oldAppendToCross_supernatural D Sc' cut ν j i hI hJ hIJ hJI)
local notation "hσ'" => stored_degree_congr (mul_comm (D.parity i) (D.parity j))
  (oldAppendToCross_supernatural D Sc' cut ν i j hJ hI hJI hIJ)
local notation "hτ" => oldAppendToCross_supernatural D Sc' cut ν i i hI hI hII hII
local notation "hρ" => stored_degree_congr (mul_comm (D.parity i) (D.parity j))
  (oldAppendToCross_supernatural D Sc' cut νi i j hIJ hII hTopI hTopJ)
local notation "hρ'" => stored_degree_congr (mul_comm (D.parity j) (D.parity i))
  (oldAppendToCross_supernatural D Sc' cut νi j i hII hIJ hTopJ hTopI)
local notation "hξ" => oldAppendToCross_supernatural D Sc' cut νj i i hJI hJI hTopI hTopI
local notation "hα" => probeAppendToDot_supernatural D Sc' m ν i νi hI
local notation "hβ" => probeAppendToDot_supernatural D Sc' m νi j νij hIJ
local notation "hγ" => probeAppendToDot_supernatural D Sc' m νij i νt hTopI

/-- The stored content certificates disappear under the faithful full OLD inclusion. -/
theorem probeStoredMixedBraid_source (hne : i ≠ j) (s : OldContentCategory D Sc' cut ν) :
    (show End ((F₀).obj s) from (M).map (σ s) ≫ ξ ((K).obj s) ≫ (M).map (σ' s)) -
      (show End ((F₀).obj s) from ρ ((J).obj s) ≫ (L).map (τ s) ≫ ρ' ((J).obj s)) =
      tripleDotCorrectionPolynomial D Sc' (R := End ((F₀).obj s)) i j
        (probeAppendToDot D Sc' m νij i νt hTopI ((J ⋙ V).obj s))
        ((M).map (probeAppendToDot D Sc' m νi j νij hIJ ((J).obj s)))
        ((M).map ((V).map (probeAppendToDot D Sc' m ν i νi hI s))) := by
  apply storedEndForget_injective D Sc' cut νt ((F₀).obj s)
  rw [map_sub, tripleDotCorrectionPolynomial_map]
  change (triplePrefix D Sc' cut i j i s.obj ≫ tripleSuffix D Sc' cut j i i s.obj ≫
      triplePrefix D Sc' cut j i i s.obj) -
    (tripleSuffix D Sc' cut i j i s.obj ≫ triplePrefix D Sc' cut i i j s.obj ≫
      tripleSuffix D Sc' cut i i j s.obj) =
    tripleDotCorrectionPolynomial D Sc'
      (R := End ((tripleAppend D Sc' cut i j i).obj s.obj)) i j
      (tripleLastDot D Sc' cut i j s.obj) (tripleMiddleDot D Sc' cut i j s.obj)
      (tripleFirstDot D Sc' cut i j s.obj)
  exact (ELV.CyclotomicCrossingTensor.tripleCross_braid_correction D Sc' cut i j hne s.obj).trans
    (tripleCorrection_tripleDots D Sc' cut i j s.obj)

/-- The actual seven-edge OLD probe grid at its prescribed stored lists. -/
def probeOldStoredMixedBraid
    (N : Superfunctor k (OldContentCategory D Sc' cut ν) (SVec k)) :
    End (induced M (induced V (induced J N))) :=
  gridMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N

/-- The whole stored-target probe braid has the original-Sc correction in its three independent dots. -/
theorem probeOldStoredMixedBraid_polynomial (hne : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc' cut ν) (SVec k)) :
    probeOldStoredMixedBraid D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI N =
      tripleDotCorrectionPolynomial D Sc (R := End (induced M (induced V (induced J N)))) i j
        ((induction M).map ((induction V).map (dotEnd J hα N)))
        ((induction M).map (dotEnd V hβ ((induction J).obj N)))
        (dotEnd M hγ ((induction V).obj ((induction J).obj N))) :=
  gridMixedBraid_polynomial J K U V W L M D Sc i j hσ hσ' hτ hρ hρ' hξ hα hβ hγ hne
    (probeStoredMixedBraid_source D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI hne) N

end OddMath.QuiverHecke
end

end

section

/-! # The corrected braid on the chosen evaluated stored-target generators

Brundan–Ellis (1.9): the seven actual scalar-evaluated append functors,
independent positive pair crossings with the equal crossing negative,
and three independently whiskered signed dots satisfy the original-Sc
corrected braid. Their entire native OLD module maps are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor
universe u

private theorem rectangle_degree_congr_2
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (M : B ⥤ E) [M.Additive] [M.Linear k] [IsSuperfunctor k M]
    {p q : ZMod 2} (hp : p = q) {γ : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ M).obj s}
    (hγ : IsSupernatural k p γ) (hδ : IsSupernatural k q γ)
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L M hγ N = rectangularCrossComponent J K L M hδ N := by
  cases hp
  rfl

private theorem self_rectangle_grid
    {k C A E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hγ : IsSupernatural k p γ) (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J J K K hγ N = gridDoubleCrossComponent J K hγ N := rfl

private def evaluatedEndForget
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
    (N : ProbeEvaluatedModules D Sc m ν) : End N →ₐ[k] End N.obj :=
  AlgHom.ofLinearMap
    { toFun := fun f => f.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    rfl (fun _ _ => rfl)

private theorem evaluatedEndForget_injective
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
    (N : ProbeEvaluatedModules D Sc m ν) : Function.Injective (evaluatedEndForget D Sc m ν N) :=
  fun _ _ h => InducedCategory.hom_ext h

private theorem appendTo_obj_obj_2
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
    (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ)
    (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeEvaluatedAppendTo D Sc m ν i μ h).obj N).obj =
      induced (oldContentAppendTo D Sc (probeCutoff D m) ν i μ h) N.obj := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i j : I) {νi νj νii νij νt : List I}
  (hI : (i :: ν).Perm νi) (hJ : (j :: ν).Perm νj)
  (hII : (i :: νi).Perm νii) (hIJ : (j :: νi).Perm νij) (hJI : (i :: νj).Perm νij)
  (hTopJ : (j :: νii).Perm νt) (hTopI : (i :: νij).Perm νt)
local notation "Sc'" => parameterTwist D Sc
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc' cut ν i νi hI
local notation "K" => oldContentAppendTo D Sc' cut ν j νj hJ
local notation "U" => oldContentAppendTo D Sc' cut νi i νii hII
local notation "V" => oldContentAppendTo D Sc' cut νi j νij hIJ
local notation "W" => oldContentAppendTo D Sc' cut νj i νij hJI
local notation "L" => oldContentAppendTo D Sc' cut νii j νt hTopJ
local notation "M" => oldContentAppendTo D Sc' cut νij i νt hTopI
local notation "EJ" => probeEvaluatedAppendTo D Sc' m ν i νi hI
local notation "EK" => probeEvaluatedAppendTo D Sc' m ν j νj hJ
local notation "EV" => probeEvaluatedAppendTo D Sc' m νi j νij hIJ
local notation "EL" => probeEvaluatedAppendTo D Sc' m νii j νt hTopJ
local notation "EM" => probeEvaluatedAppendTo D Sc' m νij i νt hTopI
local notation "hR₀" => oldAppendToCross_supernatural D Sc' cut νi j i hII hIJ hTopJ hTopI
local notation "hR₂" => oldAppendToCross_supernatural D Sc' cut νi i j hIJ hII hTopI hTopJ
local notation "hL₀" => oldAppendToCross_supernatural D Sc' cut ν i j hJ hI hJI hIJ
local notation "hL₂" => oldAppendToCross_supernatural D Sc' cut ν j i hI hJ hIJ hJI
local notation "hEqP" => oldAppendToCross_supernatural D Sc' cut ν i i hI hI hII hII
local notation "hEqS" => oldAppendToCross_supernatural D Sc' cut νj i i hJI hJI hTopI hTopI
local notation "hα" => probeAppendToDot_supernatural D Sc' m ν i νi hI
local notation "hβ" => probeAppendToDot_supernatural D Sc' m νi j νij hIJ
local notation "hγ" => probeAppendToDot_supernatural D Sc' m νij i νt hTopI

/-- The actual independent evaluated crossing components, with the middle equal crossing negative. -/
def probeStoredMixedBraid (N : ProbeEvaluatedModules D Sc' m ν) :
    End ((EM).obj ((EV).obj ((EJ).obj N))) :=
  (show End ((EM).obj ((EV).obj ((EJ).obj N))) from
    probeAppendToCrossIterated D Sc' m νi j i hII hIJ hTopJ hTopI ((EJ).obj N) ≫
      (-(EL).map (probeAppendToCrossIterated D Sc' m ν i i hI hI hII hII N)) ≫
        probeAppendToCrossIterated D Sc' m νi i j hIJ hII hTopI hTopJ ((EJ).obj N)) -
  (show End ((EM).obj ((EV).obj ((EJ).obj N))) from
    (EM).map (probeAppendToCrossIterated D Sc' m ν i j hJ hI hJI hIJ N) ≫
      (-probeAppendToCrossIterated D Sc' m νj i i hJI hJI hTopI hTopI ((EK).obj N)) ≫
        (EM).map (probeAppendToCrossIterated D Sc' m ν j i hI hJ hIJ hJI N))

/-- The independently whiskered first evaluated dot. -/
def probeStoredFirstDot (N : ProbeEvaluatedModules D Sc' m ν) :
    End ((EM).obj ((EV).obj ((EJ).obj N))) :=
  (EM).map ((EV).map (probeAppendToDotComponent D Sc' m ν i νi hI N))

/-- The independently whiskered middle evaluated dot. -/
def probeStoredMiddleDot (N : ProbeEvaluatedModules D Sc' m ν) :
    End ((EM).obj ((EV).obj ((EJ).obj N))) :=
  (EM).map (probeAppendToDotComponent D Sc' m νi j νij hIJ ((EJ).obj N))

/-- The independent last evaluated dot. -/
def probeStoredLastDot (N : ProbeEvaluatedModules D Sc' m ν) :
    End ((EM).obj ((EV).obj ((EJ).obj N))) :=
  probeAppendToDotComponent D Sc' m νij i νt hTopI ((EV).obj ((EJ).obj N))

/-- Every whole native crossing component agrees with the seven-edge OLD grid. -/
theorem probeStoredMixedBraid_eq (N : ProbeEvaluatedModules D Sc' m ν) :
    (probeStoredMixedBraid D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI N).hom =
      probeOldStoredMixedBraid D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI N.obj := by
  simp only [probeStoredMixedBraid, appendTo_obj_obj_2]
  unfold probeOldStoredMixedBraid gridMixedBraid
  apply congrArg₂ Sub.sub
  · apply congrArg₂ (fun f g => f ≫ g)
    · exact rectangle_degree_congr_2 U V L M (mul_comm (D.parity j) (D.parity i)) _ _ _
    · apply congrArg₂ (fun f g => f ≫ g)
      · exact congrArg (fun f => -(induction L).map f) (self_rectangle_grid J U hEqP N.obj)
      · exact rectangle_degree_congr_2 V U M L (mul_comm (D.parity i) (D.parity j)) _ _ _
  · apply congrArg₂ (fun f g => f ≫ g)
    · exact congrArg (fun f => (induction M).map f)
        (rectangle_degree_congr_2 K J W V (mul_comm (D.parity i) (D.parity j)) _ _ _)
    · apply congrArg₂ (fun f g => f ≫ g)
      · exact congrArg Neg.neg (self_rectangle_grid W M hEqS ((induction K).obj N.obj))
      · exact congrArg (fun f => (induction M).map f)
          (rectangle_degree_congr_2 J K V W (mul_comm (D.parity j) (D.parity i)) _ _ _)

theorem probeStoredFirstDot_eq (N : ProbeEvaluatedModules D Sc' m ν) :
    (probeStoredFirstDot D Sc m ν i j hI hIJ hTopI N).hom =
      (induction M).map ((induction V).map (dotEnd J hα N.obj)) := rfl

theorem probeStoredMiddleDot_eq (N : ProbeEvaluatedModules D Sc' m ν) :
    (probeStoredMiddleDot D Sc m ν i j hI hIJ hTopI N).hom =
      (induction M).map (dotEnd V hβ ((induction J).obj N.obj)) := rfl

theorem probeStoredLastDot_eq (N : ProbeEvaluatedModules D Sc' m ν) :
    (probeStoredLastDot D Sc m ν i j hI hIJ hTopI N).hom =
      dotEnd M hγ ((induction V).obj ((induction J).obj N.obj)) := rfl

/-- The whole evaluated stored-target corrected braid uses the original parameters and chosen dots. -/
theorem probeStoredMixedBraid_polynomial (hne : i ≠ j) (N : ProbeEvaluatedModules D Sc' m ν) :
    probeStoredMixedBraid D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI N =
      tripleDotCorrectionPolynomial D Sc (R := End ((EM).obj ((EV).obj ((EJ).obj N)))) i j
        (probeStoredFirstDot D Sc m ν i j hI hIJ hTopI N)
        (probeStoredMiddleDot D Sc m ν i j hI hIJ hTopI N)
        (probeStoredLastDot D Sc m ν i j hI hIJ hTopI N) := by
  apply evaluatedEndForget_injective D Sc' m νt ((EM).obj ((EV).obj ((EJ).obj N)))
  rw [tripleDotCorrectionPolynomial_map]
  change (probeStoredMixedBraid D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI N).hom =
    tripleDotCorrectionPolynomial D Sc
      (R := End (induced M (induced V (induced J N.obj)))) i j
      (probeStoredFirstDot D Sc m ν i j hI hIJ hTopI N).hom
      (probeStoredMiddleDot D Sc m ν i j hI hIJ hTopI N).hom
      (probeStoredLastDot D Sc m ν i j hI hIJ hTopI N).hom
  rw [probeStoredMixedBraid_eq, probeStoredFirstDot_eq,
    probeStoredMiddleDot_eq, probeStoredLastDot_eq]
  exact probeOldStoredMixedBraid_polynomial D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI hne N.obj

end OddMath.QuiverHecke
end

end

section

/-! # The ordered correction in the selected OLD weight triple coordinate

Brundan–Ellis (1.9): transport the original-parameter correction in the
three independently prescribed weight dots to the same three evaluated
stored-target dot maps. The acting parameters are parameterTwist Sc.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u v w

private theorem conjugation_polynomial
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (i j : I)
    {V W : C} (e : V = W) (x y z : End W) :
    tripleDotCorrectionPolynomial D Sc (R := End V) i j
      (eqToHom e ≫ x ≫ eqToHom e.symm)
      (eqToHom e ≫ y ≫ eqToHom e.symm)
      (eqToHom e ≫ z ≫ eqToHom e.symm) =
    eqToHom e ≫ tripleDotCorrectionPolynomial D Sc (R := End W) i j x y z ≫ eqToHom e.symm := by
  exact (tripleDotCorrectionPolynomial_map D Sc
    (inductionEndConjugation (eqToIso e)) i j x y z).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {a b c d : X}
  (hab : a + D.α i = b) (hbc : b + D.α j = c) (hcd : c + D.α i = d)
  (β : WeightBlocks D Λ a)
local notation "Sc'" => parameterTwist D Sc
local notation "δi" => blockSucc D Λ i hab β
local notation "δij" => blockSucc₂ D j i Λ hab hbc β
local notation "ε" => probeOldBlockSucc₃ D i j i Λ hab hbc hcd β
local notation "hI" => probeOldBlockTarget_perm D i Λ hab β δi rfl
local notation "hIJ" => probeOldBlockTarget_perm D j Λ hbc δi δij rfl
local notation "hTopI" => probeOldBlockTarget_perm D i Λ hcd δij ε rfl
local notation "F₀" => probeOldE D Sc' m i Λ hab ≫ probeOldE D Sc' m j Λ hbc ≫ probeOldE D Sc' m i Λ hcd
local notation "eq₃" => probeOldWeightTriple_obj_eq D Sc' m i j i Λ hab hbc hcd β

/-- The correction in the three chosen global dots is the same ordered stored-target polynomial. -/
theorem probeOldWeightTriplePolynomial_component (M : ProbeOldWeightProduct D Sc' m Λ a) :
    tripleDotCorrectionPolynomial D Sc (R := End ((F₀).obj M ε)) i j
      ((probeOldWeightTripleFirstDot D Sc' m i j i Λ hab hbc hcd).total M ε)
      ((probeOldWeightTripleMiddleDot D Sc' m i j i Λ hab hbc hcd).total M ε)
      ((probeOldWeightTripleLastDot D Sc' m i j i Λ hab hbc hcd).total M ε) =
    eqToHom (eq₃ M) ≫ tripleDotCorrectionPolynomial D Sc
      (R := End ((probeOldBlockTripleInd D Sc' m i j i Λ hab hbc hcd β).obj (M β))) i j
      (probeStoredFirstDot D Sc m (Multiset.toList (Subtype.val β)) i j hI hIJ hTopI (M β))
      (probeStoredMiddleDot D Sc m (Multiset.toList (Subtype.val β)) i j hI hIJ hTopI (M β))
      (probeStoredLastDot D Sc m (Multiset.toList (Subtype.val β)) i j hI hIJ hTopI (M β)) ≫ eqToHom (eq₃ M).symm := by
  rw [probeOldWeightTripleFirstDot_component, probeOldWeightTripleMiddleDot_component,
    probeOldWeightTripleLastDot_component]
  exact conjugation_polynomial D Sc i j (eq₃ M) _ _ _

end OddMath.QuiverHecke
end

end
