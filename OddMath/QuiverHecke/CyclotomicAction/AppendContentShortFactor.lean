/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentShortWord
import OddMath.QuiverHecke.CyclotomicAction.AppendContentCrossingImage

/-!
# Short-word moving-map factorization

The short-shuffle step of `DeformedMackeyBoundary.md` (4): factor the moving
map through the last equal-colour crossing before assembling matrix entries.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Categorification.TypeA
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- Input dot powers commute with adjoining an untouched right strand. -/
theorem firstDotPow_whiskerRight (i j : I) (s : List I) (m : ℕ) :
    (dotE D Sc (i :: s) 0 ^ m) ▷ (pres D Sc).obj (ob D [j]) =
      dotE D Sc ((i :: s) ++ [j]) 0 ^ m := by
  rw [← whiskerListAlgHom_apply, map_pow, whiskerListAlgHom_apply,
    dotE_whiskerRight D Sc (i :: s) [j] 0 (by simp)]

/-- The old moving map, with the input dots retained on its output. -/
def appendDottedMove (a : I → _root_.Polynomial k) (i : I) (s : List I) (m : ℕ) :
    (pres D Sc).obj (ob D (s ++ [i])) ⟶ (pres D Sc).obj (ob D (i :: s)) :=
  appendW D Sc a i s ≫ (dotE D Sc (i :: s) 0 ^ m)

/-- Peeling a final strand also peels the dotted moving map. -/
theorem appendDottedMove_append (a : I → _root_.Polynomial k) (i j : I)
    (s : List I) (m : ℕ) :
    appendDottedMove D Sc a i (s ++ [j]) m =
      crossLast D Sc s j i ≫ (appendDottedMove D Sc a i s m ▷ (pres D Sc).obj (ob D [j])) := by
  unfold appendDottedMove
  rw [appendW_append, MonoidalSupercategory.comp_whiskerRight (R := k),
    firstDotPow_whiskerRight]
  simp only [Category.assoc, List.cons_append]

/-- A canonical crossing word on the old strands. -/
def shortWordHom (s : List I) (l : List ℕ) :
    (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D (tgt s (cw l))) :=
  cl D Sc s _ (cw l) (sChain_pl _ _)

/-- The old dotted moving map followed by the restricted canonical word. -/
def appendShortOldHom (a : I → _root_.Polynomial k) (i : I) (s : List I)
    (m : ℕ) (l : List ℕ) :
    (pres D Sc).obj (ob D (s ++ [i])) ⟶
      (pres D Sc).obj (ob D (tgt (i :: s) (cw l))) :=
  appendDottedMove D Sc a i s m ≫ shortWordHom D Sc (i :: s) l

/-- The literal short word factors the moving map through the final crossing.
No braid replacement and no commutation of right coefficients occurs. -/
theorem appendDottedMove_short_factor (a : I → _root_.Polynomial k)
    (n : ℕ) (u : PrependShuffle (n + 1)) (hu : u ≠ longPrependShuffle (n + 1))
    (i j : I) (s : List I) (hs : s.length = n) (m : ℕ) :
    ∃ h : SChain ((i :: s) ++ [j])
        (pl ((i :: s) ++ [j]) (cw (canWord (n + 2) u.1⁻¹)))
        (tgt (i :: s) (cw (canWord (n + 2) u.1⁻¹)) ++ [j]),
      appendDottedMove D Sc a i (s ++ [j]) m ≫
        cl D Sc ((i :: s) ++ [j]) _ (cw (canWord (n + 2) u.1⁻¹)) h =
      crossLast D Sc s j i ≫
        (appendShortOldHom D Sc a i s m (canWord (n + 2) u.1⁻¹) ▷
          (pres D Sc).obj (ob D [j])) := by
  obtain ⟨h, he⟩ := prependShort_cl_whiskerRight D Sc n u hu (i :: s) (by simp [hs]) j
  refine ⟨h, ?_⟩
  rw [appendDottedMove_append, he]
  simp only [appendShortOldHom, shortWordHom,
    MonoidalSupercategory.comp_whiskerRight (R := k), Category.assoc]

/-- The old target of the literal restricted word. -/
def prependShortOldTarget (i : I) {n : ℕ} (u : PrependShuffle (n + 1))
    (s : Word I n) : Word I (n + 1) :=
  ⟨tgt (i :: s.1) (cw (canWord (n + 2) u.1⁻¹)), by simp [s.2]⟩

/-- Changing only the certified target of a crossing word preserves a composed matrix entry. -/
theorem single_comp_cl_congr {n : ℕ} {r s t t' : Word I n} {gs : List PG}
    (f : wordObj D Sc r ⟶ wordObj D Sc s)
    (h : SChain s.1 (pl s.1 gs) t.1) (h' : SChain s.1 (pl s.1 gs) t'.1) :
    (FiniteHomMatrix.single t r (f ≫ cl D Sc s.1 t.1 gs h) : Hn D Sc n) =
      FiniteHomMatrix.single t' r (f ≫ cl D Sc s.1 t'.1 gs h') := by
  obtain rfl : t = t' := Subtype.ext ((tgt_eq h).symm.trans (tgt_eq h'))
  rfl

/-- The surviving single matrix entry, with the original short prepend diagram. -/
def appendShortEntry (a : I → _root_.Polynomial k) (i : I) {n : ℕ}
    (u : PrependShuffle (n + 1)) (m : ℕ) (s : Word I n) : Hn D Sc (n + 1 + 1) :=
  FiniteHomMatrix.single (prependShuffleTarget i u (appendWord i s))
    (appendWord i (appendWord i s))
    (appendDottedMove D Sc a i (s.1 ++ [i]) m ≫
      prependShuffleHom D Sc i u (appendWord i s))

/-- The restricted morphism in the word-indexed Hom family. -/
def appendShortOldWordHom (a : I → _root_.Polynomial k) (i : I) {n : ℕ}
    (u : PrependShuffle (n + 1)) (m : ℕ) (s : Word I n) :
    wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (prependShortOldTarget i u s) :=
  appendShortOldHom D Sc a i s.1 m (canWord (n + 2) u.1⁻¹)

variable [Fintype I]

/-- A concrete matrix factorization on each surviving final-colour block.
The last crossing is on the right in multiplication order. -/
theorem appendShortEntry_factor (a : I → _root_.Polynomial k) (i : I) {n : ℕ}
    (u : PrependShuffle (n + 1)) (hu : u ≠ longPrependShuffle (n + 1))
    (m : ℕ) (s : Word I n) :
    appendShortEntry D Sc a i u m s =
      appendAlgebra D Sc i (n + 1)
        (FiniteHomMatrix.single (prependShortOldTarget i u s) (appendWord i s)
          (appendShortOldWordHom D Sc a i u m s)) *
        affineLastCrossing D Sc i i n := by
  obtain ⟨h, he⟩ := appendDottedMove_short_factor D Sc a n u hu i i s.1 s.2 m
  change appendShortEntry D Sc a i u m s =
    appendLinear D Sc i (n + 1)
      (FiniteHomMatrix.single (prependShortOldTarget i u s) (appendWord i s)
        (appendShortOldWordHom D Sc a i u m s)) * affineLastCrossing D Sc i i n
  rw [appendLinear_single, single_mul_affineLastCrossing]
  unfold appendShortEntry prependShuffleHom
  calc
    _ = FiniteHomMatrix.single (appendWord i (prependShortOldTarget i u s))
        (appendWord i (appendWord i s))
        (appendDottedMove D Sc a i (s.1 ++ [i]) m ≫
          cl D Sc ((i :: s.1) ++ [i]) _ (cw (canWord (n + 2) u.1⁻¹)) h) :=
      single_comp_cl_congr D Sc (r := appendWord i (appendWord i s))
        (s := prependWord i (appendWord i s))
        (t := prependShuffleTarget i u (appendWord i s))
        (t' := appendWord i (prependShortOldTarget i u s))
        (appendDottedMove D Sc a i (s.1 ++ [i]) m) _ h
    _ = _ := by
      rw [he, inductionLastCrossing_eq_cl]
      simp only [crossLast, s.2]
      rfl

end OddMath.QuiverHecke
