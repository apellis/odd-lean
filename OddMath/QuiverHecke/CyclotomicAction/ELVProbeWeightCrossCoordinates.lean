/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightTripleInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDistinctCrossing

/-! # Stored-target coordinates of the selected OLD weight crossings

Brundan–Ellis (1.9): retain the prescribed positive distinct and negative
equal crossings in common stored-target coordinates, before composing the
three-strand paths. No comparison or relation premise is required.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
universe u

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
      -probeAppendToCrossComponent D Sc m β.1.toList i i
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
      probeAppendToCrossComponent D Sc m β.1.toList j i
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
        ((if i = j then (-1 : k) else 1) • probeAppendToCrossComponent D Sc m β.1.toList j i
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
