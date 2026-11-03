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
private theorem source_naturality_congr
    {k C B : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {p : ZMod 2} {a b : ∀ s, F.obj s ⟶ G.obj s}
    (he : ∀ s, a s = b s) (hb : IsSupernatural k p b) : IsSupernatural k p a := by
  have h : a = b := funext he
  rw [h]
  exact hb

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

theorem tripleFirstDot_supernatural (i j : I) :
    IsSupernatural k (D.parity i) (tripleFirstDot D Sc cutoff i j) :=
  ((oldAppendDot_supernatural D Sc cutoff i).whiskerRight (A j)).whiskerRight (A i)

theorem tripleMiddleDot_supernatural (i j : I) :
    IsSupernatural k (D.parity j) (tripleMiddleDot D Sc cutoff i j) :=
  ((oldAppendDot_supernatural D Sc cutoff j).whiskerLeft (A i)).whiskerRight (A i)

theorem tripleLastDot_supernatural (i j : I) :
    IsSupernatural k (D.parity i) (tripleLastDot D Sc cutoff i j) :=
  (oldAppendDot_supernatural D Sc cutoff i).whiskerLeft ((A i) ⋙ (A j))

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

/-- Naturality of the explicit coefficient correction is constructed from the actual dots. -/
theorem tripleCorrection_supernatural {i j : I} (hij : i ≠ j) :
    IsSupernatural k (D.parity i) (F := tripleAppend D Sc cutoff i j i) (G := tripleAppend D Sc cutoff i j i)
      (tripleCorrection D Sc cutoff i j) := by
  have ht := tripleSourcePolynomial_supernatural (tripleAppend D Sc cutoff i j i) D Sc i j
    (tripleFirstDot_supernatural D Sc cutoff i j) (tripleMiddleDot_supernatural D Sc cutoff i j)
    (tripleLastDot_supernatural D Sc cutoff i j) hij
  exact source_naturality_congr (tripleCorrection_tripleDots D Sc cutoff i j) ht

/-- The original-Sc correction is the whole balanced transform of the literal OLD braid coefficient. -/
theorem oldTriplePolynomial_operator {i j : I} (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D (parameterTwist D Sc) cutoff) (SVec k))
    (w : OldCategory D (parameterTwist D Sc) cutoff) :
    tripleDotCorrectionPolynomial D Sc i j
        (transformLinear (tripleFirstDot_supernatural D (parameterTwist D Sc) cutoff i j) N w)
        (transformLinear (tripleMiddleDot_supernatural D (parameterTwist D Sc) cutoff i j) N w)
        (transformLinear (tripleLastDot_supernatural D (parameterTwist D Sc) cutoff i j) N w) =
      sign k (D.parity i * D.parity j) •
        transformLinear (tripleCorrection_supernatural D (parameterTwist D Sc) cutoff hij) N w := by
  apply hom_ext
  intro s g z
  rw [LinearMap.smul_apply, transformLinear_tensor,
    transformLinear_triplePolynomial_tensor (tripleAppend D (parameterTwist D Sc) cutoff i j i)
      D Sc i j (tripleFirstDot_supernatural D (parameterTwist D Sc) cutoff i j)
      (tripleMiddleDot_supernatural D (parameterTwist D Sc) cutoff i j)
      (tripleLastDot_supernatural D (parameterTwist D Sc) cutoff i j) hij N w s g z,
    tripleCorrection_tripleDots]
  rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
