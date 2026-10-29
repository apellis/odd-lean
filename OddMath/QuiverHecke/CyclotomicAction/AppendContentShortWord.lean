/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentCosets
import Mathlib.Order.Preorder.Finite

/-!
# Canonical short prepend words

The short-shuffle step of `DeformedMackeyBoundary.md` (4): the literal canonical
word of a non-long prepend shuffle omits the last crossing. This is a statement
about the chosen code word, not just its permutation or braid class. It permits
right whiskering of the moving diagram without equal-colour braid corrections.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA Equiv MonoidalCategory
namespace OddMath.QuiverHecke

/-- Fixing the last position makes the top run of the chosen code empty. -/
theorem canWord_eq_short_codeWord (n : ℕ) (w : Perm (Fin (n + 2)))
    (hw : w (Fin.last (n + 1)) = Fin.last (n + 1)) :
    ∃ c : List ℕ, IsCode c ∧ c.length = n ∧ canWord (n + 2) w = codeWord c := by
  have hc := isCode_code (n + 2) w
  have hl := length_code (n + 2) w
  have hp := wordProd_canWord (n + 2) w
  unfold canWord at hp ⊢
  cases he : code (n + 2) w with
  | nil => simp [he] at hl
  | cons b c =>
    rw [he] at hc hl hp
    have hcl : c.length = n := by simp only [List.length_cons] at hl; omega
    have hb := (isCode_cons.mp hc).1
    have ht := wordProd_codeWord_cons_apply (m := n + 2) hb (by omega)
    rw [hp] at ht
    have heq : (⟨c.length + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) :=
      Fin.ext (by simp [hcl])
    rw [heq, ← hw] at ht
    have hbn : b = n + 1 := congrArg Fin.val (w.injective ht)
    subst b
    refine ⟨c, (isCode_cons.mp hc).2, hcl, ?_⟩
    simp only [codeWord_cons, hcl, Nat.sub_self, descRun_zero, List.append_nil]

/-- The only prepend shuffle whose inverse does not fix the last position is the long one. -/
theorem prependShuffle_inv_last_of_ne_long (n : ℕ) (u : PrependShuffle (n + 1))
    (hu : u ≠ longPrependShuffle (n + 1)) :
    u.1⁻¹ (Fin.last (n + 1)) = Fin.last (n + 1) := by
  by_contra hlast
  have hmono : StrictMono (fun x : Fin (n + 1) => u.1⁻¹ x.succ) := by
    intro x y hxy
    have he (z : Fin (n + 1)) :
        blockEquiv (Nat.add_comm 1 (n + 1)) (Sum.inr z) = z.succ := by
      apply Fin.ext
      simp [blockEquiv_inr_val, Nat.add_comm]
    simpa only [he] using u.2.2 hxy
  have hbound (x : Fin (n + 1)) : (u.1⁻¹ x.succ).val < n + 1 := by
    have hm := hmono.monotone (Fin.le_last x)
    have ht := (u.1⁻¹ (Fin.last (n + 1))).isLt
    have hn : (u.1⁻¹ (Fin.last (n + 1))).val ≠ n + 1 := by
      intro h; exact hlast (Fin.ext h)
    change (u.1⁻¹ x.succ).val ≤ (u.1⁻¹ (Fin.last (n + 1))).val at hm
    omega
  let f : Fin (n + 1) → Fin (n + 1) := fun x => ⟨(u.1⁻¹ x.succ).val, hbound x⟩
  have hf : StrictMono f := fun x y hxy => hmono hxy
  have hx (x : Fin (n + 1)) : u.1⁻¹ x.succ = x.castSucc := by
    apply Fin.ext
    exact congrArg (fun z : Fin (n + 1) => z.val) (hf.apply_eq (x := x))
  apply hu
  apply Subtype.ext
  apply inv_injective
  apply Equiv.ext
  intro x
  refine Fin.cases ?_ (fun y => ?_) x
  · have hz : u.1⁻¹ 0 = Fin.last (n + 1) := by
      by_contra h
      have hlt : (u.1⁻¹ 0).val < n + 1 := by
        have := (u.1⁻¹ 0).isLt
        have hn : (u.1⁻¹ 0).val ≠ n + 1 := fun he => h (Fin.ext he)
        omega
      let y : Fin (n + 1) := ⟨(u.1⁻¹ 0).val, hlt⟩
      have hy : u.1⁻¹ y.succ = u.1⁻¹ 0 := (hx y).trans (Fin.ext rfl)
      have he := congrArg Fin.val (u.1⁻¹.injective hy)
      simp at he
    rw [hz]
    change Fin.last (n + 1) = (finRotate (n + 1 + 1)).symm 0
    exact ((finRotate (n + 1 + 1)).symm_apply_eq.mpr (finRotate_last').symm).symm
  · rw [hx]
    change y.castSucc = (finRotate (n + 1 + 1)).symm y.succ
    apply (finRotate (n + 1 + 1)).eq_symm_apply.mpr
    apply Fin.ext
    simp

/-- Shortness bounds the literal canonical crossings, so none meets the final strand. -/
theorem canWord_prependShort_lt (n : ℕ) (u : PrependShuffle (n + 1))
    (hu : u ≠ longPrependShuffle (n + 1)) :
    ∀ x ∈ canWord (n + 2) u.1⁻¹, x < n := by
  obtain ⟨c, -, hl, he⟩ := canWord_eq_short_codeWord n u.1⁻¹
    (prependShuffle_inv_last_of_ne_long n u hu)
  rw [he]
  intro x hx
  simpa only [hl] using lt_of_mem_codeWord hx

/-- Restriction to one fewer strand preserves the chosen word literally. -/
theorem canWord_prependShort_restrict (n : ℕ) (u : PrependShuffle (n + 1))
    (hu : u ≠ longPrependShuffle (n + 1)) :
    canWord (n + 1) (wordProd (n + 1) (canWord (n + 2) u.1⁻¹)) =
      canWord (n + 2) u.1⁻¹ := by
  obtain ⟨c, hc, hl, he⟩ := canWord_eq_short_codeWord n u.1⁻¹
    (prependShuffle_inv_last_of_ne_long n u hu)
  rw [he]
  exact canWord_wordProd_codeWord hc (by omega)

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The short canonical crossing diagram is a right whiskering of the same word.
The equality does not pass through braid equivalence. -/
theorem prependShort_cl_whiskerRight (n : ℕ) (u : PrependShuffle (n + 1))
    (hu : u ≠ longPrependShuffle (n + 1)) (s : List I) (hs : s.length = n + 1)
    (j : I) :
    ∃ h : SChain (s ++ [j]) (pl (s ++ [j]) (cw (canWord (n + 2) u.1⁻¹)))
        (tgt s (cw (canWord (n + 2) u.1⁻¹)) ++ [j]),
      cl D Sc (s ++ [j]) _ (cw (canWord (n + 2) u.1⁻¹)) h =
        cl D Sc s _ (cw (canWord (n + 2) u.1⁻¹)) (sChain_pl _ _) ▷
          (pres D Sc).obj (ob D [j]) := by
  have hf : Fits s.length (cw (canWord (n + 2) u.1⁻¹)) := by
    apply fits_cw
    intro x hx
    have := canWord_prependShort_lt n u hu x hx
    rw [hs]
    omega
  exact ⟨_, (cl_whiskerRight D Sc _ (sChain_pl _ _) [j] hf).symm⟩

end OddMath.QuiverHecke
