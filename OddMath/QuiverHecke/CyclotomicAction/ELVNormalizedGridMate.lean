/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSignedMate
import OddMath.QuiverHecke.CyclotomicAction.ELVNormalizedContentRectangularCross
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # The normalized rectangular mate is the prescribed grid mate

BE (1.13)–(1.14): promote the signed coend comparison to the whole module
morphism and retain independently stored successor content certificates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
namespace BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α)

/-- The signed comparison retains the whole prescribed module morphism. -/
theorem rectangularMate_negative_component
    (hNeg : IsSupernatural k p (fun s => -α s))
    (N : Superfunctor k A (SVec k)) :
    orderedRectangularMateComponent J J K K hNeg N = orderedGridMateComponent J K hα N := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro t
  have h := rectangularMate_negative_eq_grid J K hα N t
  dsimp only [orderedRectangularMateLinear, orderedGridMateLinear] at h
  exact h

private theorem rectangularMate_component_eq
    {β : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hβ : IsSupernatural k p β) (hab : α = β) (N : Superfunctor k A (SVec k)) :
    orderedRectangularMateComponent J J K K hα N =
      orderedRectangularMateComponent J J K K hβ N := by
  cases hab
  rfl

/-- Equal degrees give the same given grid mate module morphism. -/
theorem gridMateComponent_degree_eq {q : ZMod 2} (hpq : p = q)
    (hq : IsSupernatural k q α) (N : Superfunctor k A (SVec k)) :
    orderedGridMateComponent J K hα N = orderedGridMateComponent J K hq N := by
  cases hpq
  rfl

end BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β δ γ : Multiset I) (i : I)
  (hδ : β + ([i] : Multiset I) = δ) (hγ : δ + ([i] : Multiset I) = γ)
local notation "J" => contentAppendTo D Sc cutoff N β [i] δ hδ
local notation "K" => contentAppendTo D Sc cutoff N δ [i] γ hγ
local notation "hRaw" => contentDistinctTargetsCross_supernatural D Sc cutoff N β i i δ δ γ hδ hδ hγ hγ
local notation "hNorm" => normalizedContentTargetsCross_supernatural D Sc cutoff N β i i δ δ γ hδ hδ hγ hγ

/-- The prescribed stored-content equal-colour crossing has the matrix parity. -/
theorem contentTargetsGridCross_supernatural :
    IsSupernatural k (D.parity i)
      (contentDistinctTargetsCross D Sc cutoff N β i i δ δ γ hδ hδ hγ hγ) :=
  (SKM.zmod2_mul_self (D.parity i)) ▸ hRaw

/-- The negative normalized rectangular mate is the exact matrix grid mate,
including its rank-one degree and all stored successor contents. -/
theorem normalizedContentTargetsMate_eq_grid
    (M : ContentModules D Sc cutoff N δ) :
    BalancedInduction.orderedRectangularMateComponent J J K K hNorm M =
      BalancedInduction.orderedGridMateComponent J K
        (contentTargetsGridCross_supernatural D Sc cutoff N β δ γ i hδ hγ) M := by
  have hn : normalizedContentTargetsCross D Sc cutoff N β i i δ δ γ hδ hδ hγ hγ =
      fun s => -contentDistinctTargetsCross D Sc cutoff N β i i δ δ γ hδ hδ hγ hγ s := by
    funext s
    simp only [normalizedContentTargetsCross, ite_true]
  have hNeg : IsSupernatural k (D.parity i * D.parity i)
      (fun s => -contentDistinctTargetsCross D Sc cutoff N β i i δ δ γ hδ hδ hγ hγ s) :=
    hn ▸ hNorm
  have h := BalancedInduction.rectangularMate_negative_component J K hRaw hNeg M
  have he := BalancedInduction.gridMateComponent_degree_eq J K hRaw
    (SKM.zmod2_mul_self (D.parity i))
    (contentTargetsGridCross_supernatural D Sc cutoff N β δ γ i hδ hγ) M
  have hc := BalancedInduction.rectangularMate_component_eq J K hNorm hNeg hn M
  exact hc.trans (h.trans he)

end OddMath.QuiverHecke.ELVOld
