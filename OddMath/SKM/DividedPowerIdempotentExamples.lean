/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.DividedPowerIdempotents
import OddMath.SKM.TwoStrandSummands

/-! Rank-two tests distinguish the printed negative element from the opposite projector. -/

namespace OddMath.SKM.DividedPowerIdempotents.Consumer

open OddMath.Frontier
open NilHeckeAction

/-- Both mixed constants remain positive in the rank-two source coordinates. -/
theorem rankTwo_mixed :
    sourceCrossing 0 0 * sourceDot 0 0 + sourceDot 0 1 * sourceCrossing 0 0 = 1 :=
  (source_mixed (n := 0) 0).1

/-- Concrete nonzero counterexample to the literal printed odd idempotence. -/
theorem rankTwo_printed :
    printedGenerator 0 0 ≠ 0 ∧
      ¬ IsIdempotentElem (printedGenerator 0 0) ∧
      action 0 (printedGenerator 0 0) 1 = -1 :=
  ⟨printedGenerator_ne_zero 0, printedGenerator_not_idempotent 0,
    action_printedGenerator_one 0⟩

/-- The existing reflected opposite longest projector is nonzero and idempotent. -/
theorem rankTwo_opposite :
    oppositeProjector 0 ≠ 0 ∧ IsIdempotentElem (oppositeProjector 0) :=
  ⟨oppositeProjector_ne_zero 0, oppositeProjector_idempotent 0⟩

/-- At rank two the unsigned longest word is the single generator. -/
theorem rankTwo_opposite_eq : oppositeProjector 0 = unsignedGenerator 0 0 := by
  rw [oppositeProjector_eq_unsignedProduct]
  change unsignedGenerator 0 0 * 1 = unsignedGenerator 0 0
  exact mul_one _

/-- Exact sign discrepancy at the first nontrivial longest word. -/
theorem rankTwo_printed_eq : printedGenerator 0 0 = -oppositeProjector 0 := by
  rw [rankTwo_opposite_eq, printedGenerator_eq_neg]

/-- The discrepancy cannot be hidden by renaming the two rank-two elements. -/
theorem rankTwo_distinct : printedGenerator 0 0 ≠ oppositeProjector 0 := by
  intro h
  apply printedGenerator_not_idempotent (n := 0) 0
  rw [h]
  exact oppositeProjector_idempotent 0

/-- Apply reduced-word independence on the two adjacent rank-three braid words. -/
theorem rankThree_braid :
    unsignedGenerator 1 0 * unsignedGenerator 1 1 * unsignedGenerator 1 0 =
      unsignedGenerator 1 1 * unsignedGenerator 1 0 * unsignedGenerator 1 1 :=
  unsignedGenerator_braid 0 1 rfl

/-- ℚ is characteristic zero and two is invertible, as required for odd colours in BE2. -/
theorem rational_ground : CharZero ℚ ∧ IsUnit (2 : ℚ) :=
  ⟨inferInstance, rational_two_isUnit⟩

/-- The polynomial witness over ℚ is constructed and has constant coefficient exactly one. -/
theorem rankTwo_rational_witness :
    rationalConstantCoeff 0 (rationalOne 0) = 1 ∧ rationalOne 0 ≠ 0 :=
  ⟨rationalConstantCoeff_one 0, rationalOne_ne_zero 0⟩

/-- Over an admissible ground field the printed element is nonzero and not idempotent. -/
theorem rankTwo_rational_printed :
    rationalPrintedGenerator 0 0 ≠ 0 ∧
      ¬ IsIdempotentElem (rationalPrintedGenerator 0 0) ∧
      rationalAction 0 (rationalPrintedGenerator 0 0) (rationalOne 0) = -rationalOne 0 :=
  ⟨rationalPrintedGenerator_ne_zero 0, rationalPrintedGenerator_not_idempotent 0,
    rationalPrintedGenerator_one 0⟩

/-- The positive mixed relation survives scalar extension with its source sign unchanged. -/
theorem rankTwo_rational_mixed :
    rationalInclude 0 (sourceCrossing 0 0) * rationalInclude 0 (sourceDot 0 0) +
      rationalInclude 0 (sourceDot 0 1) * rationalInclude 0 (sourceCrossing 0 0) = 1 := by
  rw [← map_mul, ← map_mul, ← map_add, rankTwo_mixed, map_one]

/-- The unsigned correction is an idempotent over ℚ. -/
theorem rankTwo_rational_corrected : IsIdempotentElem (rationalUnsignedGenerator 0 0) :=
  rationalUnsignedGenerator_idempotent 0

/-- The sign change preserves the actual left submodule, not only its isomorphism class. -/
theorem rankTwo_rational_leftIdeal :
    LinearMap.range (LinearMap.mulRight (RationalPresented 0) (rationalPrintedGenerator 0 0)) =
      LinearMap.range
        (LinearMap.mulRight (RationalPresented 0) (rationalUnsignedGenerator 0 0)) :=
  rationalPrintedGenerator_leftIdeal 0

/-- The corresponding integral left-ideal equality remains available as a construction lemma. -/
theorem rankTwo_integral_leftIdeal :
    LinearMap.range (LinearMap.mulRight (Presented 0) (printedGenerator 0 0)) =
      LinearMap.range (LinearMap.mulRight (Presented 0) (unsignedGenerator 0 0)) :=
  printedGenerator_leftIdeal 0

/-- A fixed three-letter braid word has exactly the predicted odd length sign. -/
theorem rankThree_word_sign :
    printedGenerator 1 0 * printedGenerator 1 1 * printedGenerator 1 0 =
      -(unsignedGenerator 1 0 * unsignedGenerator 1 1 * unsignedGenerator 1 0) := by
  simp only [printedGenerator_eq_neg, mul_neg, neg_mul, neg_neg]

/-- The reduced-longest left-module theorem is used over ℚ without an assumed representation. -/
theorem rational_reduced_longest {n : ℕ} (w : NilCoxeterWords.Word n)
    (hw : NilCoxeterWords.Reduced w)
    (hp : NilCoxeterWords.permutation w = LongestElementary.longest (n + 2)) :
    LinearMap.range (LinearMap.mulRight (RationalPresented n)
      (rationalInclude n (w.map (printedGenerator n)).prod)) =
      LinearMap.range (LinearMap.mulRight (RationalPresented n)
        (rationalInclude n (oppositeProjector n))) :=
  rationalPrinted_longest_leftIdeal w hw hp

/-- The existing even two-strand idempotent has exactly the printed sign and order. -/
theorem even_twoStrand {I X k : Type*} [AddCommGroup X] {D : Datum I X}
    [CommRing k] (Sc : Scalars D k) (sy : Symmetrizer D) (hc : Sc.Homogeneous)
    (i : I) (ν : X) (hi : D.parity i = 0) :
    IsIdempotentElem (TwoStrand.e Sc sy hc i ν) :=
  even_generator_idempotent _ _ _ TwoStrand.t_sq (TwoStrand.slideR hi)

/-- The corrected odd projector has both required gradings. -/
theorem rankThree_homogeneous :
    oppositeProjector 1 ∈ EQOnhDG.grading 1 0 ∧
      oppositeProjector 1 ∈ OddMath.Diagrams.OddNilHecke.parity 1 0 :=
  ⟨oppositeProjector_degree 1, oppositeProjector_even 1⟩

end OddMath.SKM.DividedPowerIdempotents.Consumer
