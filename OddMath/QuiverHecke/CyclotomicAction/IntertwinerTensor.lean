/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerCorners

/-!
# Balanced tensor descent of the moving-strand element

The underlying left-module map of KKO I, arXiv:1206.5933v2, Proposition 8.4.
We use the existing `InductionAlong.Ind` balanced tensor, not a free tensor.
The parity involution is placed on the right action of the first factor:
`a ⋅ r = a ξ(φ_i^{p(β)}(r))`. Moving this involution to the coefficient
factor gives the action underlying `Π_i^{p(β)} R^Λ(β)`.

`contentQ` descends for every coefficient module, hence also for the
cyclotomic quotient. It is the content-β component in the height algebra;
the other content blocks map to zero. No projectivity or flatness is used.
This module does not supply the parity grading or the signed right `t_i`
action, and therefore does not assert the full superbimodule proposition.
-/

noncomputable section
namespace OddMath.QuiverHecke
open Categorification

variable {I k X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Left insertion with the coefficient parity twist moved to the right action. -/
def twistedPrepend (i : I) (n : ℕ) (β : Multiset I) : Hn D Sc n →ₙ+* Hn D Sc (n + 1) :=
  (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)).comp
    (homMatrixTwistAlgebra D Sc n (D.parity i * contentSumParity D β) :
      Hn D Sc n →ₙ+* Hn D Sc n)

/-- The proved corner balance, with the involution on the target right action. -/
theorem contentMove_intertwines (i : I) (n : ℕ) (β : Multiset I) :
    InductionAlong.Intertwines (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))
      (twistedPrepend D Sc i n β) (contentMove D Sc i n β) := by
  intro z
  have h := contentMove_balance D Sc i n β
    (homMatrixTwist D Sc n (D.parity i * contentSumParity D β) z)
  rw [homMatrixTwist_twice] at h
  exact h

/-- The moving-strand map on the balanced tensor quotient, not just its free generators. -/
def contentQ (i : I) (n : ℕ) (β : Multiset I)
    (N : Type*) [AddCommGroup N] [Module (Hn D Sc n) N] :
    InductionAlong.Ind N (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) →ₗ[Hn D Sc (n + 1)]
      InductionAlong.Ind N (twistedPrepend D Sc i n β) :=
  InductionAlong.natMap (contentMove_intertwines D Sc i n β)

/-- On a pure balanced tensor the map is `a ⊗ b ↦ a G_β ⊗ b`. -/
@[simp] theorem contentQ_tmul (i : I) (n : ℕ) (β : Multiset I)
    (N : Type*) [AddCommGroup N] [Module (Hn D Sc n) N]
    (a : InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))) (b : N) :
    contentQ D Sc i n β N (InductionAlong.Ind.tmul a b) =
      InductionAlong.Ind.tmul
        (InductionAlong.cornerMul (contentMove_intertwines D Sc i n β) a) b := rfl

/-- Specialization to the actual cyclotomic quotient coefficient module. -/
def cyclotomicContentQ (i : I) (n : ℕ) (β : Multiset I)
    (a : I → _root_.Polynomial k) :=
  contentQ D Sc i (n + 1) β (CyclotomicAlgebra D Sc a n)

end OddMath.QuiverHecke
