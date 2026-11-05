/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldPairPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMulticolourInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionTripleCorrection

/-! # The OLD correction in the three prescribed append dots

Brundan–Ellis (1.9): identify the full untruncated OLD coefficient braid
correction with the polynomial in three independent positional dots.
Its original-parameter ordered induction operator is retained on every
module. No source braid, polynomial-naturality or comparison premise is
introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction Distinct
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local notation "A" i => append D Sc cutoff i

/-- The first dot, independently appended twice to the three-letter source. -/
def tripleFirstDot (i j : I) (s : OldCategory D Sc cutoff) : End ((tripleAppend D Sc cutoff i j i).obj s) :=
  (A i).map (pairFirstDot D Sc cutoff i j s)

/-- The middle dot, appended once to the three-letter source. -/
def tripleMiddleDot (i j : I) (s : OldCategory D Sc cutoff) : End ((tripleAppend D Sc cutoff i j i).obj s) :=
  (A i).map (pairSecondDot D Sc cutoff i j s)

/-- The last independent moving dot in the same source endomorphism algebra. -/
def tripleLastDot (i j : I) (s : OldCategory D Sc cutoff) : End ((tripleAppend D Sc cutoff i j i).obj s) :=
  oldAppendDotComponent D Sc cutoff i (((A i) ⋙ (A j)).obj s)

theorem tripleFirstDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    tripleFirstDot D Sc cutoff i j s = oldAffineEndAlgHom D Sc cutoff ((tripleAppend D Sc cutoff i j i).obj s)
      (dotE D Sc (s.word ++ [i] ++ [j] ++ [i]) s.word.length) := by
  rw [tripleFirstDot, pairFirstDot_affine]
  change (ideal D Sc cutoff _ _).mkQ
    (rightContext D Sc cutoff [i] (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])
      (affineUnit D Sc cutoff _ _ (dotE D Sc (s.word ++ [i] ++ [j]) s.word.length))) = _
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
    (dotE D Sc (s.word ++ [i] ++ [j]) s.word.length ▷ (pres D Sc).obj (ob D [i]))) = _
  rw [dotE_whiskerRight D Sc (s.word ++ [i] ++ [j]) [i] s.word.length (by simp)]
  rfl

theorem tripleMiddleDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    tripleMiddleDot D Sc cutoff i j s = oldAffineEndAlgHom D Sc cutoff ((tripleAppend D Sc cutoff i j i).obj s)
      (dotE D Sc (s.word ++ [i] ++ [j] ++ [i]) (s.word.length + 1)) := by
  rw [tripleMiddleDot, pairSecondDot_affine]
  change (ideal D Sc cutoff _ _).mkQ
    (rightContext D Sc cutoff [i] (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])
      (affineUnit D Sc cutoff _ _ (dotE D Sc (s.word ++ [i] ++ [j]) (s.word.length + 1)))) = _
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
    (dotE D Sc (s.word ++ [i] ++ [j]) (s.word.length + 1) ▷ (pres D Sc).obj (ob D [i]))) = _
  rw [dotE_whiskerRight D Sc (s.word ++ [i] ++ [j]) [i] (s.word.length + 1) (by simp)]
  rfl

theorem tripleLastDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    tripleLastDot D Sc cutoff i j s = oldAffineEndAlgHom D Sc cutoff ((tripleAppend D Sc cutoff i j i).obj s)
      (dotE D Sc (s.word ++ [i] ++ [j] ++ [i]) (s.word.length + 2)) := by
  rw [tripleLastDot, oldAppendDotComponent_eq, appendMovingPower, pow_one]
  change (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
    (dotE D Sc (s.word ++ [i] ++ [j] ++ [i]) (s.word ++ [i] ++ [j]).length)) = _
  simp only [List.length_append, List.length_singleton, Nat.add_assoc]
  rfl

/-- The coefficient correction is exactly the polynomial of the three chosen OLD dots. -/
theorem tripleCorrection_tripleDots (i j : I) (s : OldCategory D Sc cutoff) :
    tripleCorrection D Sc cutoff i j s =
      tripleDotCorrectionPolynomial D Sc i j
        (tripleLastDot D Sc cutoff i j s) (tripleMiddleDot D Sc cutoff i j s)
        (tripleFirstDot D Sc cutoff i j s) := by
  rw [tripleLastDot_affine, tripleMiddleDot_affine, tripleFirstDot_affine,
    ← tripleDotCorrectionPolynomial_map]
  change oldAffineEndAlgHom D Sc cutoff ((tripleAppend D Sc cutoff i j i).obj s) (coefficientCorrection D Sc s.word i j) = _
  congr 1
  simp only [coefficientCorrection, positionalCorrection, tripleDotCorrectionPolynomial,
    tripleDotCorrectionSum, pow_zero, mul_one]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
