/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.DownAdjointCoefficients
import OddMath.CoveringQuantum.UDot.TensorGram.MixedGram
import OddMath.SKM.CoveringDatum

/-!
# Physical downward left-cons coefficient step

BE2, arXiv:1701.04133v2, Theorem 10.3 Claim 3, algebraic side.
Reuse the existing composable mixed algebraWord, with unchanged physical order.
This does not assert a graphical matching bijection or normalized family identity.
-/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients GenericVerma.MixedGram
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (D : RootDatum I X)

omit [DecidableEq I] [DecidableEq X] in
/-- The existing mixed algebraWord's shift is the physical left region. -/
theorem mixed_word_physical_weight (μ : X) (a : List (Bool × I)) :
    OddMath.SKM.wt D.toSKM μ a = μ + shift D a := by
  induction a with
  | nil => simp [shift]
  | cons g a ih =>
    simp only [OddMath.SKM.wt_cons, OddMath.SKM.sh, RootDatum.toSKM_α, ih,
      shift, halfRoot]
    abel

/-- Physical Claim 3 algebraic coefficient step on existing mixed words.
The endpoint condition says b ends where the downward-left-cons a ends.
F acts at ν = wt μ a, whereas the upward generator on b acts at ν−αᵢ.
No reversal of mixed words is used. -/
theorem sesquilinearForm_mixed_down_leftCons_bent_coeff
    (σ : ℚ) (hσ : σ ^ 2 = 1) (i : I) (μ : X)
    (a b : List (Bool × I))
    (hwt : OddMath.SKM.wt D.toSKM μ b = OddMath.SKM.wt D.toSKM μ a - D.α i)
    (z : ℤ) :
    let ν := OddMath.SKM.wt D.toSKM μ a
    (signLaurent σ hσ (sesquilinearForm D
      (algebraWord D μ a) (algebraWord D μ ((true, i) :: b)))).coeff z =
    σ ^ (D.parl i ν).val *
      (signLaurent σ hσ (sesquilinearForm D
        (algebraWord D μ ((false, i) :: a)) (algebraWord D μ b))).coeff
          (z - D.d i * (1 - D.h i ν)) := by
  have hw : μ + shift D b = μ + shift D a - D.α i := by
    simpa only [mixed_word_physical_weight] using hwt
  dsimp only
  rw [mixed_word_physical_weight]
  simpa only [algebraWord, halfGen, ite_true, Bool.false_eq_true, ite_false, hw] using
    sesquilinearForm_F_bent_coeff D σ hσ i (μ + shift D a)
      (algebraWord D μ a) (algebraWord D μ b) z

end OddMath.CoveringQuantum.UDot.GenericTensor
