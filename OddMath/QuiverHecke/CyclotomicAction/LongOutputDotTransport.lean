/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveTransport
import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveOrderedCoefficients

/-!
# Last-output-dot normalization for the long moving shuffle

The position and sign in signed dot normal ordering are evaluated on the
canonical long shuffle. This supplies the scalar normalization needed to compare
output-last-dot coordinates with the input PBW coordinates in
`DeformedMackeyBoundary.md` (2). It does not identify the short submodule.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} {k : Type w} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X)

/-- The last output dot returns to the moving position in every prefix. -/
theorem sourceDotPosition_leadingMoveWord_last (l s : List I) :
    sourceDotPosition (leadingMoveWord l s) (l.length + s.length) = l.length := by
  induction s generalizing l with
  | nil => simp [leadingMoveWord, sourceDotPosition]
  | cons j s ih =>
    rw [leadingMoveWord, sourceDotPosition_append]
    have he : l.length + (j :: s).length = (l ++ [j]).length + s.length := by simp; omega
    rw [he, ih]
    simp [sourceDotPosition, swapNat]

/-- Each incident slide contributes the moving-colour times old-colour parity. -/
theorem sourceDotSign_leadingMoveWord_last (i : I) (l s : List I) :
    sourceDotSign D (k := k) (l ++ i :: s) (leadingMoveWord l s)
      (l.length + s.length) = SKM.zsign k (D.parity i * wordSumParity D s) := by
  induction s generalizing l with
  | nil => simp [leadingMoveWord, sourceDotSign, wordSumParity, SKM.zsign]
  | cons j s ih =>
    rw [leadingMoveWord, sourceDotSign_append]
    have he : l.length + (j :: s).length = (l ++ [j]).length + s.length := by simp; omega
    rw [he, sourceDotPosition_leadingMoveWord_last]
    have ht : tgt (l ++ i :: j :: s) (cw [l.length]) = (l ++ [j]) ++ i :: s := by
      simp [cw, PG.act, List.append_assoc]
    rw [ht, ih]
    simp [sourceDotSign, crossDotExponent, PG.par, wordSumParity, mul_add,
      zsign_add_aux, mul_comm]

/-- The long canonical shuffle sends the last output dot to input position zero. -/
theorem sourceDotPosition_longPrependShuffle_last (s : List I) :
    sourceDotPosition (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹)
      s.length = 0 := by
  rw [canWord_longPrependShuffle]
  have hw := leadingMoveWord_eq_descRun ([] : List I) s
  simp only [List.length_nil] at hw
  rw [← hw]
  simpa using sourceDotPosition_leadingMoveWord_last ([] : List I) s

/-- Exact library sign for the last output dot on the long canonical shuffle. -/
theorem sourceDotSign_longPrependShuffle_last (i : I) (s : List I) :
    sourceDotSign D (k := k) (i :: s)
      (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹) s.length =
      SKM.zsign k (D.parity i * wordSumParity D s) := by
  rw [canWord_longPrependShuffle]
  have hw := leadingMoveWord_eq_descRun ([] : List I) s
  simp only [List.length_nil] at hw
  rw [← hw]
  simpa using sourceDotSign_leadingMoveWord_last D (k := k) i [] s
end OddMath.QuiverHecke
