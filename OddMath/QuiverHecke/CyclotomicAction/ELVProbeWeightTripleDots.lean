/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightPathCoordinates

/-! # The three prescribed OLD weight dots in one triple coordinate

Brundan–Ellis (1.9): retain the independently whiskered first, middle
and last signed dots in the same selected triple coordinate. These
identities precede transport of the ordered correction polynomial.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
attribute [local irreducible] ELVOld.BalancedInduction.induced
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
  exact (probeOldInductionComponent D Sc m i Λ h₃ ε).toFunctor.map_add _ _ |>.symm

theorem probeOldWeightTripleMiddleDot_total (M : ProbeOldWeightProduct D Sc m Λ a)
    (ε : WeightBlocks D Λ d) :
    (probeOldWeightTripleMiddleDot D Sc m i j l Λ h₁ h₂ h₃).total M ε =
      (probeOldInductionComponent D Sc m i Λ h₃ ε).map
        ((E₁ ◁ probeOldActionDot D Sc m j Λ h₂).total M) := by
  change (probeOldInductionComponent D Sc m i Λ h₃ ε).map
      ((E₁ ◁ probeOldActionDot D Sc m j Λ h₂).app 0 M) +
    (probeOldInductionComponent D Sc m i Λ h₃ ε).map
      ((E₁ ◁ probeOldActionDot D Sc m j Λ h₂).app 1 M) = _
  exact (probeOldInductionComponent D Sc m i Λ h₃ ε).toFunctor.map_add _ _ |>.symm

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
local notation "α" => probeAppendToDotComponent D Sc m β.1.toList l δ₁.1.toList
  (probeOldBlockTarget_perm D l Λ h₁ β δ₁ rfl)
local notation "βdot" => probeAppendToDotComponent D Sc m δ₁.1.toList j δ₂.1.toList
  (probeOldBlockTarget_perm D j Λ h₂ δ₁ δ₂ rfl)
local notation "γ" => probeAppendToDotComponent D Sc m δ₂.1.toList i ε.1.toList
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
    probeAppendToInductionDot_total D Sc m δ₁.1.toList j δ₂.1.toList _ ((B₁).obj (M β))
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
