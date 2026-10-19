/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.CapNormalization
import OddMath.SKM.MixedCrossingLocalExamples

/-! Odd cap-class consumers in both orientations, with empty context and
with a nonempty same-colour context shifting the physical weight. -/
namespace OddMath.SKM.CapNormalizationExamples
open StringDiagrams StringDiagrams.Chord
open MixedCrossingLocalExamples (oddDatum oddSymmetrizer)

private def a (k : Bool) : List (Letter Bool) := if k then [(true, false)] else []
private def b (k : Bool) : List (Letter Bool) := if k then [(false, false)] else []
private def A (ε k : Bool) := a k ++ (ε, false) :: (!ε, false) :: b k
private def R (k : Bool) : List (TMove (Letter Bool)) :=
  if k then [.cap 1, .cap 0] else [.cap 0]
private def S (k : Bool) : List (TMove (Letter Bool)) := if k then [.cap 0] else []

private theorem matching (ε k : Bool) : IsMatching₂ (A ε k) [] (R k) := by
  cases ε <;> cases k
  · exact ⟨⟨⟨(2, (false, false)), (0, (true, false)),
      rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩
  · refine ⟨⟨?_, ?_⟩, rfl⟩
    · exact ⟨(4, (false, false)), (2, (true, false)), rfl, rfl, rfl, by decide⟩
    · exact ⟨⟨(6, (true, false)), (0, (false, false)), rfl, rfl, rfl, by decide⟩, trivial⟩
  · exact ⟨⟨⟨(2, (true, false)), (0, (false, false)),
      rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩
  · refine ⟨⟨?_, ?_⟩, rfl⟩
    · exact ⟨(4, (true, false)), (2, (false, false)), rfl, rfl, rfl, by decide⟩
    · exact ⟨⟨(6, (true, false)), (0, (false, false)), rfl, rfl, rfl, by decide⟩, trivial⟩

private theorem shorter_matching (k : Bool) : IsMatching₂ (a k ++ b k) [] (S k) := by
  cases k
  · exact ⟨trivial, rfl⟩
  · exact ⟨⟨⟨(2, (true, false)), (0, (false, false)), rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩

private theorem reduced (ε k : Bool) : Reduced₂ (A ε k) (R k) := by
  cases k <;>
    change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag <;> simp

private theorem shorter_reduced (k : Bool) : Reduced₂ (a k ++ b k) (S k) := by
  cases k <;>
    change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag <;> simp

private theorem cap (ε k : Bool) :
    Same (pairing₂ (A ε k) (R k)) (b k).length ((b k).length + 1) := by
  cases ε <;> cases k <;> unfold Same idAt <;> decide

private theorem deleted (ε k : Bool) : Iso (pairing₂ (a k ++ b k) (S k))
    (rmAt (pairing₂ (A ε k) (R k)) (b k).length) := by
  have pair (u v : ℕ) (x y : Letter Bool) : Iso [(u, x), (u, y)] [(v, x), (v, y)] := by
    refine ⟨rfl, ?_⟩
    intro i j
    obtain _ | _ | i := i <;> obtain _ | _ | j := j <;> simp [Same, idAt]
  cases ε <;> cases k
  · exact Iso.refl _
  · exact pair _ _ _ _
  · exact Iso.refl _
  · exact pair _ _ _ _

/-- Instantiates the representative comparison with every hypothesis proved.
Both odd orientations occur, with and without a nonempty physical suffix. -/
theorem odd_cap_normalization (ε k : Bool) :
    oddDatum.parity false = 1 ∧
    tableDegree oddDatum oddSymmetrizer 0 (tLay (A ε k) (R k)) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay (a k ++ b k) (S k)) +
        (1 + if !ε then oddDatum.h false (wt oddDatum 0 (b k))
          else -oddDatum.h false (wt oddDatum 0 (b k))) ∧
    xpar oddDatum 0 (tLay (A ε k) (R k)) =
      xpar oddDatum 0 (tLay (a k ++ b k) (S k)) +
        cupPar oddDatum (wt oddDatum 0 (b k)) (!ε, false) := by
  refine ⟨rfl, ?_⟩
  simpa only [A, oddSymmetrizer, Bool.false_eq_true, ↓reduceIte, one_mul] using
    reduced₂_cap_degree_parity oddDatum oddSymmetrizer 0 (a k) (b k) ε false
      (matching ε k) (reduced ε k) (shorter_matching k) (shorter_reduced k)
      (cap ε k) (deleted ε k)

/-- The suffix changes the coroot coordinate from zero to minus two. -/
theorem suffix_weight_shift : oddDatum.h false (0 : Bool → ℤ) = 0 ∧
    oddDatum.h false (wt oddDatum 0 (b true)) = -2 := by
  norm_num [b, wt, sh, oddDatum, Datum.h, Datum.α,
    PositivePointGradingExamples.twoColourDatum]

/-- EF has degree increment three and even parity; FE has increment minus one
and odd parity. Using the exterior weight would give the wrong degrees. -/
theorem odd_nonempty_cap_values :
    tableDegree oddDatum oddSymmetrizer 0 (tLay (A true true) (R true)) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay (a true ++ b true) (S true)) + 3 ∧
    xpar oddDatum 0 (tLay (A true true) (R true)) =
      xpar oddDatum 0 (tLay (a true ++ b true) (S true)) ∧
    tableDegree oddDatum oddSymmetrizer 0 (tLay (A false true) (R true)) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay (a true ++ b true) (S true)) - 1 ∧
    xpar oddDatum 0 (tLay (A false true) (R true)) =
      xpar oddDatum 0 (tLay (a true ++ b true) (S true)) + 1 := by
  have hp := (odd_cap_normalization true true).2
  have hm := (odd_cap_normalization false true).2
  have hp' : tableDegree oddDatum oddSymmetrizer 0 (tLay (A true true) (R true)) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay (a true ++ b true) (S true)) + 3 ∧
      xpar oddDatum 0 (tLay (A true true) (R true)) =
        xpar oddDatum 0 (tLay (a true ++ b true) (S true)) := by
    simpa only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, suffix_weight_shift.2,
      cupPar, add_zero, show (1 + - -2 : ℤ) = 3 by decide] using hp
  have hm' : tableDegree oddDatum oddSymmetrizer 0 (tLay (A false true) (R true)) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay (a true ++ b true) (S true)) - 1 ∧
      xpar oddDatum 0 (tLay (A false true) (R true)) =
        xpar oddDatum 0 (tLay (a true ++ b true) (S true)) + 1 := by
    have hpar : cupPar oddDatum (wt oddDatum 0 (b true)) (true, false) = 1 := by
      rw [cupPar_wt]
      rfl
    simpa only [Bool.not_false, ↓reduceIte, suffix_weight_shift.2, hpar,
      show (1 + -2 : ℤ) = -1 by decide, sub_eq_add_neg] using hm
  exact ⟨hp'.1, hp'.2, hm'.1, hm'.2⟩

/-- Empty-context EF and FE recover degree one; FE retains the odd cap parity. -/
theorem odd_empty_cap_values :
    tableDegree oddDatum oddSymmetrizer 0 (tLay (A true false) (R false)) = 1 ∧
    xpar oddDatum 0 (tLay (A true false) (R false)) = 0 ∧
    tableDegree oddDatum oddSymmetrizer 0 (tLay (A false false) (R false)) = 1 ∧
    xpar oddDatum 0 (tLay (A false false) (R false)) = 1 := by
  have hp := (odd_cap_normalization true false).2
  have hm := (odd_cap_normalization false false).2
  constructor
  · simpa [a, b, S, tLay, tableDegree, cupPar, ipar, oddDatum, Datum.h] using hp.1
  constructor
  · simpa [a, b, S, tLay, tableDegree, cupPar, ipar, oddDatum, Datum.h] using hp.2
  constructor
  · simpa [a, b, S, tLay, tableDegree, cupPar, ipar, oddDatum, Datum.h] using hm.1
  · simpa [a, b, S, tLay, tableDegree, cupPar, ipar, oddDatum, Datum.h] using hm.2

end OddMath.SKM.CapNormalizationExamples
