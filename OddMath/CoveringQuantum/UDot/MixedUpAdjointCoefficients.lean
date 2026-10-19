import OddMath.CoveringQuantum.UDot.MixedAdjointCoefficients

/-!
# Physical upward left-cons coefficient step

BE2, arXiv:1701.04133v2, Theorem 10.3 Claim 2, algebraic side.
The existing signed algebraWord is evaluated in unchanged physical order.
The finite-colour, bar-consistent form uses purely even covering coefficients.
No graphical family identity or mixed-word reversal is asserted.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients GenericVerma.MixedGram
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  [Finite I] (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent)

/-- Physical Claim 2 algebraic coefficient step for arbitrary existing signed words.
The explicit endpoint condition places b at the endpoint of upward-left-cons a.
E has right weight ν = wt μ a, and its adjoint F has right weight ν+αᵢ.
The coefficient shift has no π factor. No reversal or graphical premise is used. -/
theorem sesquilinearForm_mixed_up_leftCons_bent_coeff
    (σ : ℚ) (hσ : σ ^ 2 = 1) (i : I) (μ : X)
    (a b : List (Bool × I))
    (hwt : OddMath.SKM.wt D.toSKM μ b = OddMath.SKM.wt D.toSKM μ a + D.α i)
    (z : ℤ) :
    let ν := OddMath.SKM.wt D.toSKM μ a
    (signLaurent σ hσ (sesquilinearForm D hD
      (algebraWord D μ a) (algebraWord D μ ((false, i) :: b)))).coeff z =
    (signLaurent σ hσ (sesquilinearForm D hD
      (algebraWord D μ ((true, i) :: a)) (algebraWord D μ b))).coeff
        (z - D.d i * (1 + D.h i ν)) := by
  have hw : μ + shift D b = μ + shift D a + D.α i := by
    simpa only [mixed_word_physical_weight] using hwt
  dsimp only
  rw [mixed_word_physical_weight]
  simpa only [algebraWord, halfGen, ite_true, Bool.false_eq_true, ite_false, hw] using
    sesquilinearForm_E_bent_coeff D hD σ hσ i (μ + shift D a)
      (algebraWord D μ a) (algebraWord D μ b) z

end OddMath.CoveringQuantum.UDot.GenericTensor
