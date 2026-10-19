/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.MixedUpAdjointCoefficients
import OddMath.CoveringQuantum.UDot.ContextualCommutator
import OddMath.CoveringQuantum.UDot.VermaWeightExamples

/-!
# Mixed steps at a negative weight with infinite non-bar-consistent colours

The physical Claim 2/3 steps and corrected Claim 5 algebraic equation of BE2,
arXiv:1701.04133v2, Theorem 10.3 are instantiated on actual composable words.
The suffix endpoints are proved, not assumed. Both signs occur, with nonempty
context and suffix. The finite tensor expansion evaluates the same modified word
using either native Delta1/Delta2 action. No graphical equality, form compatibility,
nonzero total coefficient or non-bottom filter is asserted.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.MixedWordStepExamples
open Coefficients GenericTensor GenericVerma GenericVerma.MixedGram VermaWeightExamples
open TensorProduct

/-- The actual colour set is infinite and bar consistency fails. -/
theorem infinite_nonbar : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ⟨infinite_colours, not_barConsistent⟩

/-- External right weight, negative at colour zero. -/
def rightWeight : ℕ →₀ ℤ := Finsupp.single 0 (-3)

/-- Negativity is checked on the specified datum, not supplied as a premise. -/
theorem negative_right_weight : datum.h 0 rightWeight = -3 := by
  simp [rightWeight, datum, RootDatum.h]

/-- A physical word with both signs and distinct colours. -/
def mixedWord : List (Bool × ℕ) := [(true, 0), (false, 1)]

/-- The exact physical endpoint of the mixed word. -/
theorem mixed_endpoint :
    OddMath.SKM.wt datum.toSKM rightWeight mixedWord =
      rightWeight + datum.α 0 - datum.α 1 := by
  rw [mixed_word_physical_weight]
  simp only [mixedWord, shift, halfRoot, ite_true, Bool.false_eq_true, ite_false, add_zero]
  abel

/-- The upward partner has the required physical endpoint. -/
theorem up_endpoint :
    OddMath.SKM.wt datum.toSKM rightWeight ((true, 0) :: mixedWord) =
      OddMath.SKM.wt datum.toSKM rightWeight mixedWord + datum.α 0 := by
  simp [OddMath.SKM.wt_cons, OddMath.SKM.sh, add_comm]

/-- The downward partner has the required physical endpoint. -/
theorem down_endpoint :
    OddMath.SKM.wt datum.toSKM rightWeight ((false, 0) :: mixedWord) =
      OddMath.SKM.wt datum.toSKM rightWeight mixedWord - datum.α 0 := by
  simp [OddMath.SKM.wt_cons, OddMath.SKM.sh, sub_eq_add_neg, add_comm]

/-- Both actual word elements have the same external right weight in the modified algebra. -/
theorem mixed_block :
    (algebraWord datum rightWeight mixedWord).val ∈
      block datum Coefficients.q pi (rightWeight + shift datum mixedWord) rightWeight :=
  algebraWord_mem_block datum rightWeight mixedWord

/-- Upward adjunction retains its exact integral q shift on the physical words. -/
theorem up_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    let ν := OddMath.SKM.wt datum.toSKM rightWeight mixedWord
    (signLaurent σ hσ (sesquilinearForm datum
      (algebraWord datum rightWeight mixedWord)
      (algebraWord datum rightWeight ((false, 0) :: (true, 0) :: mixedWord)))).coeff z =
    (signLaurent σ hσ (sesquilinearForm datum
      (algebraWord datum rightWeight ((true, 0) :: mixedWord))
      (algebraWord datum rightWeight ((true, 0) :: mixedWord)))).coeff
        (z - datum.d 0 * (1 + datum.h 0 ν)) :=
  sesquilinearForm_mixed_up_leftCons_bent_coeff datum σ hσ 0 rightWeight
    mixedWord ((true, 0) :: mixedWord) up_endpoint z

/-- Downward adjunction retains the star parity factor and the exact q shift. -/
theorem down_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    let ν := OddMath.SKM.wt datum.toSKM rightWeight mixedWord
    (signLaurent σ hσ (sesquilinearForm datum
      (algebraWord datum rightWeight mixedWord)
      (algebraWord datum rightWeight ((true, 0) :: (false, 0) :: mixedWord)))).coeff z =
    σ ^ (datum.parl 0 ν).val *
      (signLaurent σ hσ (sesquilinearForm datum
        (algebraWord datum rightWeight ((false, 0) :: mixedWord))
        (algebraWord datum rightWeight ((false, 0) :: mixedWord)))).coeff
          (z - datum.d 0 * (1 - datum.h 0 ν)) :=
  sesquilinearForm_mixed_down_leftCons_bent_coeff datum σ hσ 0 rightWeight
    mixedWord ((false, 0) :: mixedWord) down_endpoint z

/-- The suffix in the contextual commutator has pairing minus one, not minus three. -/
theorem suffix_pairing :
    datum.h 0 (OddMath.SKM.wt datum.toSKM rightWeight [(true, 0)]) = -1 := by
  simp [OddMath.SKM.wt_cons, OddMath.SKM.wt_nil, OddMath.SKM.sh,
    rightWeight, datum, RootDatum.h, RootDatum.α]

/-- Corrected Claim 5 with nonempty prefix and suffix, retaining the inner scalar bar. -/
theorem contextual_commutator :
    sesquilinearForm datum
      (algebraWord datum rightWeight ([(false, 0)] ++ (true, 0) :: (false, 0) :: [(true, 0)]))
      (algebraWord datum rightWeight []) -
      datum.pii pi 0 * sesquilinearForm datum
        (algebraWord datum rightWeight
          ([(false, 0)] ++ (false, 0) :: (true, 0) :: [(true, 0)]))
        (algebraWord datum rightWeight []) =
      bar (qpInt (datum.qi Coefficients.q 0) (datum.pii pi 0) (-1)) *
        sesquilinearForm datum
          (algebraWord datum rightWeight ([(false, 0)] ++ [(true, 0)]))
          (algebraWord datum rightWeight []) := by
  simpa only [suffix_pairing] using
    sesquilinearForm_context_EF datum rightWeight [(false, 0)] [(true, 0)] 0

/-- The two tensor weights give exactly the negative external weight. -/
theorem tensor_difference : (0 : ℕ →₀ ℤ) - Finsupp.single 0 3 = rightWeight := by
  simp [rightWeight, ← Finsupp.single_neg]

/-- The actual finite expansion computes the original algebra word in both coproducts. -/
theorem tensor_word_evaluation (s : Bool) :
    tensorRepresentation datum 0 (Finsupp.single 0 3) s
      (algebraWord datum rightWeight mixedWord).val
      (toIntegrable datum 0 1 ⊗ₜ[Coefficients.Ring]
        toIntegrable datum (Finsupp.single 0 3) 1) =
      listValue datum 0 (Finsupp.single 0 3)
        (expansion datum 0 (Finsupp.single 0 3) s mixedWord) := by
  rw [← tensor_difference, algebraWord_action, expansion_action]

end OddMath.CoveringQuantum.UDot.MixedWordStepExamples
