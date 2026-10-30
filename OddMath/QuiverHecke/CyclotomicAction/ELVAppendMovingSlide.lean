/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMovingShift
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendBalance
import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyRho

/-!
# Decorated moving-dot deletion in the ELV append presentation

The moving-dot step of `DeformedGlobalQP.md` §4, with the dot decoration
placed before the full ELV relation. No commutation of an odd dot with that
relation is used. The same-colour correction is the right extension of a
shorter old ideal element.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

set_option quotPrecheck false in
local notation "O[" l "]" => (pres D Sc).obj (ob D l)

/-- The decoration is between the moving braid and the ELV relation. -/
def appendDecoratedW (i : I) (s : List I) (d : ℕ) :
    hom D Sc cutoff (s ++ [i]) (i :: s) :=
  affineUnit D Sc cutoff _ _ (lastToFirstHom D Sc i s) ≫
    movingPower D Sc cutoff i s d ≫ relation D Sc cutoff i s

/-- Zero decoration recovers the old-generator morphism. -/
@[simp] theorem appendDecoratedW_zero (i : I) (s : List I) :
    appendDecoratedW D Sc cutoff i s 0 = appendW D Sc cutoff i s := by
  have h : movingPower D Sc cutoff i s 0 = 𝟙 (obj D Sc cutoff (i :: s)) := by
    change affineUnit D Sc cutoff _ _ (dotE D Sc (i :: s) 0 ^ 0) = _
    rw [pow_zero, End.one_def, affineUnit_id]
  rw [appendDecoratedW, h, Category.id_comp, appendW]

/-- The shorter decorated morphism remains in the full old ideal. -/
theorem appendDecoratedW_mem_ideal (i : I) (s : List I) (d : ℕ) :
    appendDecoratedW D Sc cutoff i s d ∈ ideal D Sc cutoff (s ++ [i]) (i :: s) :=
  comp_ideal D Sc cutoff _ (comp_ideal D Sc cutoff _ (relation_mem D Sc cutoff i s))

private theorem movingPower_rightContext (i : I) (s : List I) (x : I) (d : ℕ) :
    rightContext D Sc cutoff [x] _ _ (movingPower D Sc cutoff i s d) =
      movingPower D Sc cutoff i (s ++ [x]) d := by
  change affineUnit D Sc cutoff _ _ ((dotE D Sc (i :: s) 0 ^ d) ▷ O[[x]]) = _
  have h : (dotE D Sc (i :: s) 0 ^ d) ▷ O[[x]] =
      dotE D Sc (i :: (s ++ [x])) 0 ^ d := by
    change whiskerWordRingHom D Sc (i :: s) [x] (_ ^ d) = _
    rw [map_pow, whiskerWordRingHom_apply, dotE_whiskerRight D Sc (i :: s) [x] 0 (by simp)]
    rfl
  rw [h]
  rfl

/-- Peeling a final old letter preserves the order of decoration and relation. -/
theorem appendDecoratedW_append (i : I) (s : List I) (x : I) (d : ℕ) :
    appendDecoratedW D Sc cutoff i (s ++ [x]) d =
      affineUnit D Sc cutoff _ _ (crossLast D Sc s x i) ≫
        rightContext D Sc cutoff [x] _ _ (appendDecoratedW D Sc cutoff i s d) := by
  have ht : lastToFirstHom D Sc i (s ++ [x]) =
      crossLast D Sc s x i ≫ affineRightContext D Sc [x] _ _ (lastToFirstHom D Sc i s) :=
    lastToFirstHom_append_singleton D Sc i x s
  unfold appendDecoratedW
  rw [ht, affineUnit_comp D Sc cutoff (v := s ++ [x] ++ [i])
    (w := s ++ [i] ++ [x]) (z := i :: (s ++ [x])),
    rightContext_comp, rightContext_comp, rightContext_relation,
    movingPower_rightContext, rightContext_affineUnit, Category.assoc]
  rfl

/-- Last-dot deletion with arbitrary moving decoration, before commuting the relation. -/
theorem lastDot_comp_appendDecoratedW_mem (i : I) (s : List I) (d : ℕ) :
    affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length) ≫
        appendDecoratedW D Sc cutoff i s d -
      SKM.zsign k (D.parity i * wordSumParity D s) •
        appendDecoratedW D Sc cutoff i s (d + 1) ∈
      appendRelations D Sc cutoff i s (i :: s) := by
  induction s using List.reverseRecOn with
  | nil =>
    have hz : SKM.zsign k (D.parity i * wordSumParity D ([] : List I)) = 1 := by
      simp [wordSumParity, SKM.zsign]
    rw [hz, one_smul]
    have he : affineUnit D Sc cutoff _ _ (dotE D Sc [i] 0) ≫
        appendDecoratedW D Sc cutoff i [] d = appendDecoratedW D Sc cutoff i [] (d + 1) := by
      change affineUnit D Sc cutoff [i] [i] (dotE D Sc [i] 0) ≫
        (𝟙 _ ≫ affineUnit D Sc cutoff [i] [i] (dotE D Sc [i] 0 ^ d) ≫ _) =
        𝟙 _ ≫ affineUnit D Sc cutoff [i] [i] (dotE D Sc [i] 0 ^ (d + 1)) ≫ _
      rw [Category.id_comp, Category.id_comp, ← Category.assoc,
        ← affineUnit_comp, pow_succ, End.mul_def]
    convert Submodule.zero_mem (appendRelations D Sc cutoff i [] [i]) using 1
    exact sub_eq_zero.mpr he
  | append_singleton s x ih =>
    set c := SKM.zsign k (D.parity i * wordSumParity D s) with hc
    set K := affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length) ≫
      appendDecoratedW D Sc cutoff i s d - c • appendDecoratedW D Sc cutoff i s (d + 1) with hK
    have hdK : affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length) ≫
        appendDecoratedW D Sc cutoff i s d =
        K + c • appendDecoratedW D Sc cutoff i s (d + 1) := by
      rw [hK, sub_add_cancel]
    have e1 : affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i] ++ [x]) s.length) =
        rightContext D Sc cutoff [x] _ _
          (affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length)) := by
      rw [rightContext_affineUnit]
      exact congrArg (affineUnit D Sc cutoff _ _)
        (dotE_whiskerRight D Sc (s ++ [i]) [x] s.length (by simp)).symm
    have main : affineUnit D Sc cutoff _ _ (crossLast D Sc s x i) ≫
        (rightContext D Sc cutoff [x] _ _
          (affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length)) ≫
            rightContext D Sc cutoff [x] _ _ (appendDecoratedW D Sc cutoff i s d)) =
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s x i) ≫
          rightContext D Sc cutoff [x] _ _ K :
            hom D Sc cutoff (s ++ [x] ++ [i]) (i :: (s ++ [x]))) +
          c • appendDecoratedW D Sc cutoff i (s ++ [x]) (d + 1) := by
      rw [← rightContext_comp, hdK, map_add, map_smul, Preadditive.comp_add,
        Linear.comp_smul, appendDecoratedW_append]
    rw [zsign_lastDot_append, show (s ++ [x]).length = s.length + 1 by simp,
      appendDecoratedW_append, ← Category.assoc, ← affineUnit_comp]
    rcases eq_or_ne x i with rfl | hx
    · rw [lastDotE_comp_crossLast_self, map_sub, map_smul, map_smul,
        affineUnit_comp, affineUnit_id, Preadditive.sub_comp, Linear.smul_comp,
        Linear.smul_comp, Category.assoc, e1, main, Category.id_comp,
        smul_add, smul_smul]
      have h1 := crossLast_comp_mem_appendRelations D Sc cutoff x x ih
      have h2 := rightContext_mem_appendRelations D Sc cutoff x
        (appendDecoratedW_mem_ideal D Sc cutoff x s d)
      rw [← hc]
      have key : ∀ A B C : hom D Sc cutoff (s ++ [x] ++ [x]) (x :: (s ++ [x])),
          A + B - C - B = A - C := fun _ _ _ => by abel
      rw [key]
      exact sub_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
    · rw [lastDotE_comp_crossLast_ne D Sc s hx, map_smul, affineUnit_comp,
        Linear.smul_comp, Category.assoc, e1, main, smul_add, smul_smul,
        add_sub_cancel_right]
      exact Submodule.smul_mem _ _ (crossLast_comp_mem_appendRelations D Sc cutoff i x ih)

/-- Even an odd trailing dot preserves the append span: it twists the old factor. -/
theorem lastDot_comp_mem_appendRelations (i : I) {s w : List I}
    {h : hom D Sc cutoff (s ++ [i]) w}
    (hh : h ∈ appendRelations D Sc cutoff i s w) :
    affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length) ≫ h ∈
      appendRelations D Sc cutoff i s w := by
  rw [← whiskerLeft_dotE D Sc s i rfl]
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, f, rfl⟩ := hh
    rw [← Category.assoc, trailing_comp_rightContext D Sc cutoff (firstDot_parity D Sc i []),
      Category.assoc]
    exact appendRelations_mem D Sc cutoff i (twist_ideal D Sc cutoff _ hr) _
  | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c ha

/-- Two decorated slides cancel the sign, still without commuting the ELV relation. -/
theorem lastDotSquare_comp_appendDecoratedW_mem (i : I) (s : List I) (d : ℕ) :
    affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length ^ 2) ≫
        appendDecoratedW D Sc cutoff i s d - appendDecoratedW D Sc cutoff i s (d + 2) ∈
      appendRelations D Sc cutoff i s (i :: s) := by
  let L := affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length)
  let c := SKM.zsign k (D.parity i * wordSumParity D s)
  have h₁ := lastDot_comp_mem_appendRelations D Sc cutoff i
    (lastDot_comp_appendDecoratedW_mem D Sc cutoff i s d)
  have h₂ := Submodule.smul_mem (appendRelations D Sc cutoff i s (i :: s)) c
    (lastDot_comp_appendDecoratedW_mem D Sc cutoff i s (d + 1))
  have hc : c * c = 1 := by
    dsimp [c]
    rw [← zsign_add_eq, CharTwo.add_self_eq_zero]
    simp [SKM.zsign]
  have he : affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length ^ 2) = L ≫ L := by
    rw [pow_two, End.mul_def, affineUnit_comp]
  rw [he]
  have h := Submodule.add_mem _ h₁ h₂
  change L ≫ (L ≫ appendDecoratedW D Sc cutoff i s d -
      c • appendDecoratedW D Sc cutoff i s (d + 1)) +
    c • (L ≫ appendDecoratedW D Sc cutoff i s (d + 1) -
      c • appendDecoratedW D Sc cutoff i s (d + 2)) ∈ _ at h
  simpa only [Preadditive.comp_sub, Linear.comp_smul, smul_sub, smul_smul, hc,
    one_smul, sub_add_sub_cancel, Category.assoc] using h

end OddMath.QuiverHecke.ELVOld
