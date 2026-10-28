/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Tactic.Abel

/-! # Block identities for the slide relations of the swapped action

The slide relations (1.8) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5 (`SKM.Rel.slideL`, `slideLEq`, `slideR`, `slideREq`), evaluated on the swapped
Hom matrices of `docs/Nondegeneracy/SwappedActionAssembly.md`, decompose into one identity for
every pair of summand paths of the two-strand words. The dots are diagonal, so each such
identity only involves the crossing entry between the two paths and the dots at its ends.

This file proves these identities for the equal-colour mixed block (A6) of the crossing. Write
`U = (R, P)` and `V = (P, R)` for the two mixed paths of the word `(i, i)` (a path `(σ₁, σ₂)`
has object `F_{σ₁} (F_{σ₂} Z)`; the dot of the left strand is the one of the outer functor).
With an entry `b : U ⟶ U` and the interchange `J : V ⟶ U`, the block is

  `U ⟶ U : b`,  `U ⟶ V : -(b ≫ b ≫ J⁻¹)`,  `V ⟶ U : J`,  `V ⟶ V : -(J ≫ b ≫ J⁻¹)`

(`docs/Nondegeneracy/CrossingNormalization.md`, (3), in composition order). Given the two
slide identities of `b` on `U` alone, the transport of the dots across `J` with the colour sign
`q`, and the commutation of `b ≫ b` with the two dots of `U`, all eight entries of the two
slide relations hold (`mixedBlock_slideL`, `mixedBlock_slideR`).

The two diagonal identities themselves pin down `b`: in the even case `b` is the inverse of
`l - r` (`slide_of_inv_even`), in the odd case `(l - r) ≫ w` with `w` the inverse of
`l ≫ l - r ≫ r` (`slide_of_inv_odd`), where `l`, `r` are the left and right dots of `U`
(`l` the post dot, `r` the pre dot). Note the sign: in the even case `b = (l - r)⁻¹`, that is
`(y - x)⁻¹` with `y` the post dot and `x` the pre dot, not its negative.
-/

namespace OddMath.QuiverHecke.SwappedAssembly.SlideBlocks

open CategoryTheory Preadditive

variable {C : Type*} [Category C] [Preadditive C]

section MixedBlock

variable {U V : C} (q : ℤ) (lU rU b : U ⟶ U) (lV rV : V ⟶ V) (J : V ⟶ U) (Ji : U ⟶ V)

/-- Moving a dot of `V` across the inverse of the interchange. -/
theorem inv_comp_of_comp {d : V ⟶ V} {e : U ⟶ U} (hJ : J ≫ Ji = 𝟙 _)
    (hJi : Ji ≫ J = 𝟙 _) (h : d ≫ J = q • (J ≫ e)) : Ji ≫ d = q • (e ≫ Ji) := by
  calc Ji ≫ d = Ji ≫ (d ≫ J) ≫ Ji := by rw [Category.assoc, hJ, Category.comp_id]
    _ = q • (e ≫ Ji) := by
      rw [h, zsmul_comp, comp_zsmul, Category.assoc, reassoc_of% hJi]

variable {q lU rU b lV rV J Ji}

/-- **The slide `slideLEq` on the equal-colour mixed block**, entry by entry: for a source path
`src` and a target path `tgt`, `leftDot src ≫ T - q • (T ≫ rightDot tgt)` is the identity on
the diagonal and zero off it. -/
theorem mixedBlock_slideL (hq : q * q = 1) (hJ : J ≫ Ji = 𝟙 _) (hJi : Ji ≫ J = 𝟙 _)
    (hTl : lV ≫ J = q • (J ≫ rU)) (hTr : rV ≫ J = q • (J ≫ lU))
    (hb₁ : lU ≫ b - q • (b ≫ rU) = 𝟙 _) (hb₂ : b ≫ lU - q • (rU ≫ b) = 𝟙 _)
    (hcl : lU ≫ b ≫ b = b ≫ b ≫ lU) :
    (lU ≫ b - q • (b ≫ rU) = 𝟙 _) ∧
    (lU ≫ (-(b ≫ b ≫ Ji)) - q • ((-(b ≫ b ≫ Ji)) ≫ rV) = 0) ∧
    (lV ≫ J - q • (J ≫ rU) = 0) ∧
    (lV ≫ (-(J ≫ b ≫ Ji)) - q • ((-(J ≫ b ≫ Ji)) ≫ rV) = 𝟙 _) := by
  have hir : Ji ≫ rV = q • (lU ≫ Ji) := inv_comp_of_comp q J Ji hJ hJi hTr
  refine ⟨hb₁, ?_, by rw [hTl, sub_self], ?_⟩
  · have e1 : b ≫ b ≫ Ji ≫ rV = q • (lU ≫ b ≫ b ≫ Ji) := by
      rw [hir, comp_zsmul, comp_zsmul, reassoc_of% hcl]
    simp only [comp_neg, neg_comp, Category.assoc, e1, smul_neg, smul_smul, hq, one_smul]
    abel
  · have e1 : J ≫ b ≫ Ji ≫ rV = q • (J ≫ b ≫ lU ≫ Ji) := by
      rw [hir, comp_zsmul, comp_zsmul]
    have e2 : lV ≫ J ≫ b ≫ Ji = q • (J ≫ rU ≫ b ≫ Ji) := by
      rw [reassoc_of% hTl, zsmul_comp]; simp only [Category.assoc]
    have e3 : J ≫ (b ≫ lU - q • (rU ≫ b)) ≫ Ji = 𝟙 _ := by rw [hb₂, Category.id_comp, hJ]
    simp only [comp_neg, neg_comp, Category.assoc, e1, e2, smul_neg, smul_smul, hq, one_smul]
    rw [← e3]
    simp only [sub_comp, comp_sub, zsmul_comp, comp_zsmul, Category.assoc]
    abel

/-- **The slide `slideREq` on the equal-colour mixed block**, entry by entry:
`T ≫ leftDot tgt - q • (rightDot src ≫ T)` is the identity on the diagonal and zero off it. -/
theorem mixedBlock_slideR (hq : q * q = 1) (hJ : J ≫ Ji = 𝟙 _) (hJi : Ji ≫ J = 𝟙 _)
    (hTl : lV ≫ J = q • (J ≫ rU)) (hTr : rV ≫ J = q • (J ≫ lU))
    (hb₁ : lU ≫ b - q • (b ≫ rU) = 𝟙 _) (hb₂ : b ≫ lU - q • (rU ≫ b) = 𝟙 _)
    (hcr : rU ≫ b ≫ b = b ≫ b ≫ rU) :
    (b ≫ lU - q • (rU ≫ b) = 𝟙 _) ∧
    ((-(b ≫ b ≫ Ji)) ≫ lV - q • (rU ≫ (-(b ≫ b ≫ Ji))) = 0) ∧
    (J ≫ lU - q • (rV ≫ J) = 0) ∧
    ((-(J ≫ b ≫ Ji)) ≫ lV - q • (rV ≫ (-(J ≫ b ≫ Ji))) = 𝟙 _) := by
  have hil : Ji ≫ lV = q • (rU ≫ Ji) := inv_comp_of_comp q J Ji hJ hJi hTl
  refine ⟨hb₂, ?_, ?_, ?_⟩
  · have e1 : b ≫ b ≫ Ji ≫ lV = q • (rU ≫ b ≫ b ≫ Ji) := by
      rw [hil, comp_zsmul, comp_zsmul, reassoc_of% hcr]
    simp only [comp_neg, neg_comp, Category.assoc, e1, smul_neg]
    abel
  · rw [hTr, smul_smul, hq, one_smul, sub_self]
  · have e1 : J ≫ b ≫ Ji ≫ lV = q • (J ≫ b ≫ rU ≫ Ji) := by
      rw [hil, comp_zsmul, comp_zsmul]
    have e2 : rV ≫ J ≫ b ≫ Ji = q • (J ≫ lU ≫ b ≫ Ji) := by
      rw [reassoc_of% hTr, zsmul_comp]; simp only [Category.assoc]
    have e3 : J ≫ (lU ≫ b - q • (b ≫ rU)) ≫ Ji = 𝟙 _ := by rw [hb₁, Category.id_comp, hJ]
    simp only [comp_neg, neg_comp, Category.assoc, e1, e2, smul_neg, smul_smul, hq, one_smul]
    rw [← e3]
    simp only [sub_comp, comp_sub, zsmul_comp, comp_zsmul, Category.assoc]
    abel

end MixedBlock

section Diagonal

variable {U : C} {l r b w : U ⟶ U}

/-- **Even diagonal entry.** If the two dots commute and `b` is a two-sided inverse of `l - r`,
then `b` satisfies both diagonal slide identities with `q = 1`, and `b ≫ b` commutes with both
dots. -/
theorem slide_of_inv_even (hlr : l ≫ r = r ≫ l) (hb : b ≫ (l - r) = 𝟙 _)
    (hb' : (l - r) ≫ b = 𝟙 _) :
    (l ≫ b - (1 : ℤ) • (b ≫ r) = 𝟙 _) ∧ (b ≫ l - (1 : ℤ) • (r ≫ b) = 𝟙 _) ∧
    (l ≫ b ≫ b = b ≫ b ≫ l) ∧ (r ≫ b ≫ b = b ≫ b ≫ r) := by
  -- `b` commutes with every endomorphism commuting with `l - r`.
  have hcomm : ∀ e : U ⟶ U, e ≫ (l - r) = (l - r) ≫ e → e ≫ b = b ≫ e := by
    intro e he
    calc e ≫ b = b ≫ (l - r) ≫ e ≫ b := by rw [reassoc_of% hb]
      _ = b ≫ e ≫ (l - r) ≫ b := by rw [reassoc_of% he]
      _ = b ≫ e := by rw [hb', Category.comp_id]
  have hl : l ≫ b = b ≫ l := hcomm l (by simp [hlr])
  have hr : r ≫ b = b ≫ r := hcomm r (by simp [hlr])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [one_smul, hl, ← comp_sub, hb]
  · rw [one_smul, hr, ← comp_sub, hb]
  · rw [reassoc_of% hl, hl]
  · rw [reassoc_of% hr, hr]

/-- **Odd diagonal entry.** If the two dots anticommute, `w` is a two-sided inverse of
`l ≫ l - r ≫ r` commuting with both dots, and `b = (l - r) ≫ w`, then `b` satisfies both
diagonal slide identities with `q = -1`, and `b ≫ b` commutes with both dots. -/
theorem slide_of_inv_odd (hlr : l ≫ r = -(r ≫ l)) (hw : (l ≫ l - r ≫ r) ≫ w = 𝟙 _)
    (hwl : w ≫ l = l ≫ w) (hwr : w ≫ r = r ≫ w) (hbw : b = (l - r) ≫ w) :
    (l ≫ b - (-1 : ℤ) • (b ≫ r) = 𝟙 _) ∧ (b ≫ l - (-1 : ℤ) • (r ≫ b) = 𝟙 _) ∧
    (l ≫ b ≫ b = b ≫ b ≫ l) ∧ (r ≫ b ≫ b = b ≫ b ≫ r) := by
  subst hbw
  -- squares of the dots commute with both dots
  have hl2 : (l ≫ l) ≫ r = r ≫ (l ≫ l) := by
    simp only [Category.assoc, hlr, comp_neg]
    rw [← Category.assoc l r, hlr]; simp
  have hr2 : (r ≫ r) ≫ l = l ≫ (r ≫ r) := by
    rw [Category.assoc, ← neg_neg (r ≫ l), ← hlr, comp_neg, ← Category.assoc, ← neg_neg (r ≫ l),
      ← hlr]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc l ≫ (l - r) ≫ w - (-1 : ℤ) • (((l - r) ≫ w) ≫ r)
        = (l ≫ l - l ≫ r + (l ≫ r - r ≫ r)) ≫ w := by
          rw [neg_one_smul, sub_neg_eq_add, Category.assoc, hwr]
          simp only [comp_sub, sub_comp, add_comp, Category.assoc]
      _ = 𝟙 _ := by rw [← hw]; congr 1; abel
  · calc ((l - r) ≫ w) ≫ l - (-1 : ℤ) • (r ≫ (l - r) ≫ w)
        = (l ≫ l - r ≫ l + (r ≫ l - r ≫ r)) ≫ w := by
          rw [neg_one_smul, sub_neg_eq_add, Category.assoc, hwl]
          simp only [comp_sub, sub_comp, add_comp, Category.assoc]
      _ = 𝟙 _ := by rw [← hw]; congr 1; abel
  all_goals
    have hwm : w ≫ (l - r) = (l - r) ≫ w := by rw [comp_sub, sub_comp, hwl, hwr]
    have hsq : (l - r) ≫ (l - r) = l ≫ l + r ≫ r := by
      rw [comp_sub, sub_comp, sub_comp, hlr]; abel
    have hb : ((l - r) ≫ w) ≫ (l - r) ≫ w = (l ≫ l + r ≫ r) ≫ w ≫ w := by
      rw [← hsq]; simp only [Category.assoc]
      rw [← Category.assoc w (l - r) w, hwm, Category.assoc]
    have hs2l : (l ≫ l + r ≫ r) ≫ l = l ≫ (l ≫ l + r ≫ r) := by
      rw [add_comp, comp_add, hr2]; simp only [Category.assoc]
    have hs2r : (l ≫ l + r ≫ r) ≫ r = r ≫ (l ≫ l + r ≫ r) := by
      rw [add_comp, comp_add, hl2]; simp only [Category.assoc]
    rw [hb]
  · calc l ≫ (l ≫ l + r ≫ r) ≫ w ≫ w = (l ≫ l + r ≫ r) ≫ l ≫ w ≫ w := by
          rw [reassoc_of% hs2l]
      _ = (l ≫ l + r ≫ r) ≫ w ≫ w ≫ l := by rw [← reassoc_of% hwl, ← hwl]
      _ = ((l - r) ≫ w) ≫ ((l - r) ≫ w) ≫ l := by
          rw [← Category.assoc ((l - r) ≫ w) ((l - r) ≫ w) l, hb]; simp only [Category.assoc]
  · calc r ≫ (l ≫ l + r ≫ r) ≫ w ≫ w = (l ≫ l + r ≫ r) ≫ r ≫ w ≫ w := by
          rw [reassoc_of% hs2r]
      _ = (l ≫ l + r ≫ r) ≫ w ≫ w ≫ r := by rw [← reassoc_of% hwr, ← hwr]
      _ = ((l - r) ≫ w) ≫ ((l - r) ≫ w) ≫ r := by
          rw [← Category.assoc ((l - r) ≫ w) ((l - r) ≫ w) r, hb]; simp only [Category.assoc]

end Diagonal

end OddMath.QuiverHecke.SwappedAssembly.SlideBlocks
