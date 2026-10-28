/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightBlockCross
import OddMath.QuiverHecke.CyclotomicAction.GlobalBraidAlgebra

/-!
# The equal-colour braid on three inductions at every height

The module half of the same-colour braid relation of
`Categorification/KLR/CyclotomicAction/GlobalBraid.lean` (`globalCross_sameBraid`), at a fixed
height of the extended tower. With `t₁` the crossing of the two inner inductions under the
outer induction and `t₂` the crossing of the two outer inductions,

  `t₂ ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ t₁`

on every module (`heightSuperInduction_braid_same`).

Every element of a balanced tensor `P ⊗ N` with `P` an induction corner is the action of
an algebra element on `e ⊗ N`, with `e` the colour-cut idempotent
(`heightInductionCorner_btmul_eq_lact`), and the idempotent can be moved past the action
of the lower algebra (`heightInductionCorner_btmul_lact`). On `e ⊗ e ⊗ N` the crossing acts
by left multiplication by the last-pair crossing (`heightSuperInductionCrossing_idempotent`);
the braid then follows from `heightLastCrossing_braid_same`, the signs on the two sides
agreeing term by term.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

/-- A homogeneous superbimodule map moves past the action of a homogeneous element with the
Koszul sign. -/
theorem heightModules_hom_lact_apply {m : ℕ} {V W : HeightModules D Sc a ha m} {f : V ⟶ W}
    {q : ZMod 2} (hf : f ∈ Supercategory.parity (R := k) V W q) {p : ZMod 2}
    {b : heightAlgebra D Sc a m} (hb : b ∈ heightParity D Sc a ha m p) (v : V.toSVec) :
    f.1 (V.lact b v) = sign k (p * q) • W.lact b (f.1 v) := by
  have h := ((isHom_iff_of_mem (mem_parity_iff.1 hf)).1 f.2).1 p b hb
  exact congrArg (fun g : V.toSVec ⟶ W.toSVec => g v) h

theorem lact_apply_lact {m : ℕ} (V : HeightModules D Sc a ha m) (b b' : heightAlgebra D Sc a m)
    (v : V.toSVec) : V.lact b (V.lact b' v) = V.lact (b * b') v := by
  rw [V.lact_mul]
  rfl

section Corner
variable (n : ℕ)

local notation "P" => heightInductionCorner D Sc i a ha n
local notation "e" => heightInductionCornerIdempotent D Sc i a ha n
local notation "φ" => heightAppend D Sc a i n

/-- An element of `P ⊗ N` with `P` an induction corner is the action of its first factor on
the idempotent tensor. -/
theorem heightInductionCorner_btmul_eq_lact (N : HeightModules D Sc a ha n) (x : (P).toSVec)
    (w : N.toSVec) :
    btmul P N x w = (tensor P N).lact x.1 (btmul P N e w) := by
  rw [lact_btmul]
  congr 1
  apply Subtype.ext
  exact x.2.symm

/-- The action of the lower algebra passes the idempotent through the strand map. -/
theorem heightInductionCorner_btmul_lact (N : HeightModules D Sc a ha n)
    (r : heightAlgebra D Sc a n) (w : N.toSVec) :
    btmul P N e (N.lact r w) = (tensor P N).lact (φ r) (btmul P N e w) := by
  rw [← btmul_ract_lact, lact_btmul]
  congr 1
  apply Subtype.ext
  change φ 1 * φ r = φ r * φ 1
  rw [← map_mul, ← map_mul, one_mul, mul_one]

/-- Induction on `P ⊗ N` from the idempotent tensors, closed under the homogeneous action. -/
theorem heightInductionCorner_induction (N : HeightModules D Sc a ha n)
    {Q : (tensor P N).toSVec → Prop} (h0 : Q 0) (hadd : ∀ x y, Q x → Q y → Q (x + y))
    (hlact : ∀ (p : ZMod 2) (b : heightAlgebra D Sc a (n + 1)),
      b ∈ heightParity D Sc a ha (n + 1) p → ∀ w, Q w → Q ((tensor P N).lact b w))
    (he : ∀ w, Q (btmul P N e w)) (v : (tensor P N).toSVec) : Q v := by
  refine tensor_induction_on_homogeneous v h0 (fun p q x w hx _ => ?_) hadd
  rw [heightInductionCorner_btmul_eq_lact]
  exact hlact p x.1 ((heightInductionCorner_mem_part_iff D Sc i a ha n).1 hx) _ (he w)

end Corner

section Crossing
variable (n : ℕ)

local notation "P₀" => heightInductionCorner D Sc i a ha n
local notation "P₁" => heightInductionCorner D Sc i a ha (n + 1)
local notation "e₀" => heightInductionCornerIdempotent D Sc i a ha n
local notation "e₁" => heightInductionCornerIdempotent D Sc i a ha (n + 1)
local notation "d" => D.parity i * D.parity i

/-- On the idempotent tensors the same-colour crossing is left multiplication by the
last-pair crossing. -/
theorem heightSuperInductionCrossing_idempotent (N : HeightModules D Sc a ha n)
    (w : N.toSVec) :
    ((heightSuperInductionCrossing D Sc i i a ha n).app d N).1
        (btmul P₁ (tensor P₀ N) e₁ (btmul P₀ N e₀ w)) =
      (tensor P₁ (tensor P₀ N)).lact (heightLastCrossing D Sc a i i n)
        (btmul P₁ (tensor P₀ N) e₁ (btmul P₀ N e₀ w)) := by
  set z := heightCompositionCornerBi D Sc i i a ha n e₁ e₀ with hzdef
  have hz : z ∈ (heightCompositionCorner D Sc i i a ha n).toSVec.part 0 :=
    (heightCompositionCorner_mem_part_iff D Sc i i a ha n).2 (by
      change heightAppend D Sc a i (n + 1) 1 * heightAppend D Sc a i (n + 1)
        (heightAppend D Sc a i n 1) ∈ _
      rw [← map_mul, one_mul]
      exact heightCompositionAppend_parity D Sc i i a ha n (SetLike.one_mem_graded _))
  have h1 : ((heightInductionFunctorComparison D Sc i i a ha n).hom.app N).1
      (btmul P₁ (tensor P₀ N) e₁ (btmul P₀ N e₀ w)) =
      btmul (heightCompositionCorner D Sc i i a ha n) N z w :=
    heightInductionFunctorComparison_hom_btmul D Sc i i a ha n N e₁ e₀ w
  have h3 : ((heightInductionFunctorComparison D Sc i i a ha n).inv.app N).1
      (btmul (heightCompositionCorner D Sc i i a ha n) N
        ((heightCompositionSuperCrossing D Sc i i a ha n).1 z) w) =
      btmul P₁ (tensor P₀ N) (heightCompositionCornerInclusion D Sc i i a ha n
        ((heightCompositionSuperCrossing D Sc i i a ha n).1 z)) (btmul P₀ N e₀ w) := by
    change (assoc P₁ P₀ N).hom.1 ((whiskerRight (heightInductionCompositionIso D Sc i i a ha n).inv
      N).1 (btmul (heightCompositionCorner D Sc i i a ha n) N
        ((heightCompositionSuperCrossing D Sc i i a ha n).1 z) w)) = _
    rw [whiskerRight_btmul, heightInductionCompositionIso_inv_apply, assoc_hom_btmul]
  have h4 : (heightCompositionCornerInclusion D Sc i i a ha n
      ((heightCompositionSuperCrossing D Sc i i a ha n).1 z)).1 =
      heightLastCrossing D Sc a i i n := by
    change ((heightCompositionSuperCrossing D Sc i i a ha n).1 z).val = _
    rw [heightCompositionSuperCrossing_apply D Sc i i a ha n _ hz, koszulSign_zero_left, one_smul]
    change (heightAppend D Sc a i (n + 1) 1 * heightAppend D Sc a i (n + 1)
      (heightAppend D Sc a i n 1)) * heightLastCrossing D Sc a i i n = _
    rw [← map_mul, one_mul]
    exact (heightLastCrossing_corner D Sc a i i n).1
  calc ((heightSuperInductionCrossing D Sc i i a ha n).app d N).1
        (btmul P₁ (tensor P₀ N) e₁ (btmul P₀ N e₀ w))
      = ((heightInductionFunctorComparison D Sc i i a ha n).inv.app N).1
          ((whiskerRight (heightCompositionSuperCrossing D Sc i i a ha n) N).1
            (((heightInductionFunctorComparison D Sc i i a ha n).hom.app N).1
              (btmul P₁ (tensor P₀ N) e₁ (btmul P₀ N e₀ w)))) := by
        rw [heightSuperInductionCrossing_app]; rfl
    _ = btmul P₁ (tensor P₀ N) (heightCompositionCornerInclusion D Sc i i a ha n
          ((heightCompositionSuperCrossing D Sc i i a ha n).1 z)) (btmul P₀ N e₀ w) := by
        rw [h1, whiskerRight_btmul, h3]
    _ = _ := by
        rw [heightInductionCorner_btmul_eq_lact D Sc i a ha (n + 1), h4]

end Crossing

section Braid
variable (n : ℕ)

local notation "P₀" => heightInductionCorner D Sc i a ha n
local notation "P₁" => heightInductionCorner D Sc i a ha (n + 1)
local notation "P₂" => heightInductionCorner D Sc i a ha (n + 1 + 1)
local notation "e₀" => heightInductionCornerIdempotent D Sc i a ha n
local notation "e₁" => heightInductionCornerIdempotent D Sc i a ha (n + 1)
local notation "e₂" => heightInductionCornerIdempotent D Sc i a ha (n + 1 + 1)
local notation "d" => D.parity i * D.parity i
local notation "φ₁" => heightAppend D Sc a i (n + 1)
local notation "φ₂" => heightAppend D Sc a i (n + 1 + 1)

/-- Morphisms of equal parity out of three inductions agree once they agree on the triple
idempotent tensors. -/
theorem heightSuperInduction₃_hom_ext (M : HeightModules D Sc a ha n)
    {W : HeightModules D Sc a ha (n + 1 + 1 + 1)} {f g : tensor P₂ (tensor P₁ (tensor P₀ M)) ⟶ W}
    {q : ZMod 2} (hf : f ∈ Supercategory.parity (R := k) _ _ q)
    (hg : g ∈ Supercategory.parity (R := k) _ _ q)
    (h : ∀ m : M.toSVec, f.1 (btmul P₂ _ e₂ (btmul P₁ _ e₁ (btmul P₀ M e₀ m))) =
      g.1 (btmul P₂ _ e₂ (btmul P₁ _ e₁ (btmul P₀ M e₀ m)))) : f = g := by
  -- innermost layer
  have h₀ : ∀ u : (tensor P₀ M).toSVec, f.1 (btmul P₂ _ e₂ (btmul P₁ _ e₁ u)) =
      g.1 (btmul P₂ _ e₂ (btmul P₁ _ e₁ u)) := by
    intro u
    refine heightInductionCorner_induction D Sc i a ha n M
      (Q := fun u => f.1 (btmul P₂ _ e₂ (btmul P₁ _ e₁ u)) =
        g.1 (btmul P₂ _ e₂ (btmul P₁ _ e₁ u))) ?_ ?_ ?_ h u
    · rw [btmul_zero_right, btmul_zero_right, SVec.hom_map_zero, SVec.hom_map_zero]
    · intro x y hx hy
      rw [btmul_add_right, btmul_add_right, SVec.hom_map_add, SVec.hom_map_add, hx, hy]
    · intro p b hb w hw
      have hb' : φ₂ (φ₁ b) ∈ heightParity D Sc a ha (n + 1 + 1 + 1) p :=
        heightAppend_parity D Sc a ha i (n + 1 + 1) (heightAppend_parity D Sc a ha i (n + 1) hb)
      rw [heightInductionCorner_btmul_lact D Sc i a ha (n + 1),
        heightInductionCorner_btmul_lact D Sc i a ha (n + 1 + 1),
        heightModules_hom_lact_apply D Sc a ha hf hb', heightModules_hom_lact_apply D Sc a ha hg hb', hw]
  -- middle layer
  have h₁ : ∀ v : (tensor P₁ (tensor P₀ M)).toSVec, f.1 (btmul P₂ _ e₂ v) =
      g.1 (btmul P₂ _ e₂ v) := by
    intro v
    refine heightInductionCorner_induction D Sc i a ha (n + 1) _
      (Q := fun v => f.1 (btmul P₂ _ e₂ v) = g.1 (btmul P₂ _ e₂ v)) ?_ ?_ ?_ h₀ v
    · rw [btmul_zero_right, SVec.hom_map_zero, SVec.hom_map_zero]
    · intro x y hx hy
      rw [btmul_add_right, SVec.hom_map_add, SVec.hom_map_add, hx, hy]
    · intro p b hb w hw
      have hb' : φ₂ b ∈ heightParity D Sc a ha (n + 1 + 1 + 1) p :=
        heightAppend_parity D Sc a ha i (n + 1 + 1) hb
      rw [heightInductionCorner_btmul_lact D Sc i a ha (n + 1 + 1),
        heightModules_hom_lact_apply D Sc a ha hf hb', heightModules_hom_lact_apply D Sc a ha hg hb', hw]
  apply SuperBimodule.hom_ext
  apply SVec.hom_ext
  intro v
  refine heightInductionCorner_induction D Sc i a ha (n + 1 + 1) _
    (Q := fun v => f.1 v = g.1 v) ?_ ?_ ?_ h₁ v
  · rw [SVec.hom_map_zero, SVec.hom_map_zero]
  · intro x y hx hy
    rw [SVec.hom_map_add, SVec.hom_map_add, hx, hy]
  · intro p b hb w hw
    rw [heightModules_hom_lact_apply D Sc a ha hf hb, heightModules_hom_lact_apply D Sc a ha hg hb, hw]

/-- The crossing of the two inner inductions under the outer induction. -/
abbrev heightInnerCross (M : HeightModules D Sc a ha n) :
    tensor P₂ (tensor P₁ (tensor P₀ M)) ⟶ tensor P₂ (tensor P₁ (tensor P₀ M)) :=
  (heightSuperInduction D Sc i a ha (n + 1 + 1)).map
    ((heightSuperInductionCrossing D Sc i i a ha n).app d M)

/-- The crossing of the two outer inductions. -/
abbrev heightOuterCross (M : HeightModules D Sc a ha n) :
    tensor P₂ (tensor P₁ (tensor P₀ M)) ⟶ tensor P₂ (tensor P₁ (tensor P₀ M)) :=
  (heightSuperInductionCrossing D Sc i i a ha (n + 1)).app d
    ((heightSuperInduction D Sc i a ha n).obj M)

theorem heightInnerCross_mem (M : HeightModules D Sc a ha n) :
    heightInnerCross D Sc i a ha n M ∈ Supercategory.parity (R := k) _ _ d :=
  SuperBimodule.whiskerLeft_mem _ _ ((heightSuperInductionCrossing D Sc i i a ha n).app_mem d M)

theorem heightOuterCross_mem (M : HeightModules D Sc a ha n) :
    heightOuterCross D Sc i a ha n M ∈ Supercategory.parity (R := k) _ _ d :=
  (heightSuperInductionCrossing D Sc i i a ha (n + 1)).app_mem d _

theorem heightInnerCross_idempotent (M : HeightModules D Sc a ha n) (m : M.toSVec) :
    (heightInnerCross D Sc i a ha n M).1 (btmul P₂ _ e₂ (btmul P₁ _ e₁ (btmul P₀ M e₀ m))) =
      (tensor P₂ (tensor P₁ (tensor P₀ M))).lact (φ₂ (heightLastCrossing D Sc a i i n))
        (btmul P₂ _ e₂ (btmul P₁ _ e₁ (btmul P₀ M e₀ m))) := by
  change (whiskerLeft P₂ ((heightSuperInductionCrossing D Sc i i a ha n).app d M)).1
    (btmul P₂ ((heightSuperInduction D Sc i a ha n ⋙ heightSuperInduction D Sc i a ha (n + 1)).obj M)
      e₂ (btmul P₁ _ e₁ (btmul P₀ M e₀ m))) = _
  erw [whiskerLeft_btmul P₂ _ ((heightSuperInductionCrossing D Sc i i a ha n).app_mem d M)
    (heightInductionCornerIdempotent_mem D Sc i a ha (n + 1 + 1)),
    heightSuperInductionCrossing_idempotent, heightInductionCorner_btmul_lact, zero_mul,
    sign_zero, one_smul]
  rfl

theorem heightOuterCross_idempotent (M : HeightModules D Sc a ha n) (m : M.toSVec) :
    (heightOuterCross D Sc i a ha n M).1 (btmul P₂ _ e₂ (btmul P₁ _ e₁ (btmul P₀ M e₀ m))) =
      (tensor P₂ (tensor P₁ (tensor P₀ M))).lact (heightLastCrossing D Sc a i i (n + 1))
        (btmul P₂ _ e₂ (btmul P₁ _ e₁ (btmul P₀ M e₀ m))) :=
  heightSuperInductionCrossing_idempotent D Sc i a ha (n + 1) _ _

/-- **The equal-colour braid on three inductions at every height.** -/
theorem heightSuperInduction_braid_same (M : HeightModules D Sc a ha n) :
    heightOuterCross D Sc i a ha n M ≫ heightInnerCross D Sc i a ha n M ≫
        heightOuterCross D Sc i a ha n M =
      heightInnerCross D Sc i a ha n M ≫ heightOuterCross D Sc i a ha n M ≫
        heightInnerCross D Sc i a ha n M := by
  have h₁ := heightInnerCross_mem D Sc i a ha n M
  have h₂ := heightOuterCross_mem D Sc i a ha n M
  have hc₁ : φ₂ (heightLastCrossing D Sc a i i n) ∈ heightParity D Sc a ha (n + 1 + 1 + 1) d :=
    heightAppend_parity D Sc a ha i (n + 1 + 1) (heightLastCrossing_parity D Sc a i i ha n)
  have hc₂ := heightLastCrossing_parity D Sc a i i ha (n + 1)
  refine heightSuperInduction₃_hom_ext D Sc i a ha n M
    (Supercategory.comp_mem h₂ (Supercategory.comp_mem h₁ h₂))
    (Supercategory.comp_mem h₁ (Supercategory.comp_mem h₂ h₁)) fun m => ?_
  simp only [SuperBimodule.comp_val, SVec.comp_apply, heightOuterCross_idempotent,
    heightInnerCross_idempotent, heightModules_hom_lact_apply D Sc a ha h₁ hc₁,
    heightModules_hom_lact_apply D Sc a ha h₁ hc₂, heightModules_hom_lact_apply D Sc a ha h₂ hc₁,
    heightModules_hom_lact_apply D Sc a ha h₂ hc₂, SVec.hom_map_smul, smul_smul]
  simp only [lact_apply_lact, mul_assoc]
  rw [heightLastCrossing_braid_same]

end Braid

end OddMath.QuiverHecke.CyclotomicAction
