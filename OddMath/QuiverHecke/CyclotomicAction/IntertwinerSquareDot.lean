/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContentDot

/-!
# Untwisted squares of the prepend right dot

For the cancellation step in KKO I, arXiv:1206.5933v2, Lemma 8.1 and
Theorem 8.5, the square of the shifted right dot is first-dot-square
multiplication with unchanged coefficient. This identifies the operator;
it does not prove its injectivity or a prepend coset decomposition.
-/

noncomputable section
open Categorification MulOpposite StringDiagrams
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The first-dot square commutes with the whole shifted old algebra,
including odd elements and at height zero. -/
theorem affineFirstDot_sq_comm (i : I) (n : ℕ) (r : Hn D Sc n) :
    prependAlgebra D Sc i n r * affineFirstDot D Sc i n ^ 2 =
      affineFirstDot D Sc i n ^ 2 * prependAlgebra D Sc i n r := by
  rw [pow_two, ← mul_assoc, affineFirstDot_twist_comm, mul_assoc,
    affineFirstDot_twist_comm, homMatrixTwist_twice, ← mul_assoc]

/-- Two applications of the corner dot remove the old-algebra twist. -/
theorem targetDotCorner_twice_op_smul (i : I) (n : ℕ)
    (x : InductionAlong.Corner (prependAlgebra D Sc i n :
      Hn D Sc n →ₙ+* Hn D Sc (n + 1))) (r : Hn D Sc n) :
    targetDotCorner D Sc i n (targetDotCorner D Sc i n (op r • x)) =
      op r • targetDotCorner D Sc i n (targetDotCorner D Sc i n x) := by
  rw [targetDotCorner_op_smul, targetDotCorner_op_smul, homMatrixTwist_twice]

/-- Squaring the right dot cancels the shifted coefficient involution.
The endomorphism product here is ordinary function composition. -/
theorem targetRightDot_sq_tmul (i : I) (β : Multiset I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (x : InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : (qCoefficient D Sc i β a ha n).toSVec) :
    (targetRightDot D Sc i β a ha n ^ 2) (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul
        (targetDotCorner D Sc i (n + 1) (targetDotCorner D Sc i (n + 1) x)) b := by
  rw [pow_two, Module.End.mul_apply, targetRightDot_tmul, targetRightDot_tmul,
    SVec.sgn_sgn_apply]

/-- The squared corner action multiplies on the right, without moving
any dot through a crossing in its argument. -/
theorem targetDotCorner_twice_val (i : I) (n : ℕ)
    (x : InductionAlong.Corner (prependAlgebra D Sc i n :
      Hn D Sc n →ₙ+* Hn D Sc (n + 1))) :
    (targetDotCorner D Sc i n (targetDotCorner D Sc i n x)).1 =
      x.1 * affineFirstDot D Sc i n ^ 2 := by
  change (x.1 * _) * _ = _
  rw [pow_two, mul_assoc]

/-- The same coefficient cancellation holds on the unital content tensor. -/
theorem contentTargetRightDot_sq_tmul (i : I) (β : Multiset I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (x : InductionAlong.Corner (qPrependAlgebra D Sc i β n))
    (b : qContentCoefficient D Sc i β a ha n) :
    (contentTargetRightDot D Sc i β a ha n ^ 2) (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul
        (contentTargetDotCorner D Sc i β n (contentTargetDotCorner D Sc i β n x)) b := by
  rw [pow_two, Module.End.mul_apply, contentTargetRightDot_tmul,
    contentTargetRightDot_tmul]
  have hb : qContentDotCoefficient D Sc i β a ha n
      (qContentDotCoefficient D Sc i β a ha n b) = b := by
    apply Subtype.ext
    exact SVec.sgn_sgn_apply _ _ _
  rw [hb]

end OddMath.QuiverHecke
