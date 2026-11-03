/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightPathCoordinates

/-! # Crossing coordinates through specified intermediate OLD blocks

Brundan–Ellis (1.9): the selected crossing retains its prescribed stored-target
component through specified intermediate OLD blocks. The coordinate identity
supplies the crossing attachment needed by the two whole-weight braid paths.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
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
        ((if i = j then (-1 : k) else 1) • probeAppendToCrossComponent D Sc m β.1.toList j i
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
