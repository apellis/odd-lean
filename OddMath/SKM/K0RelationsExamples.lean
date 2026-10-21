import OddMath.SKM.K0Commutation
import OddMath.SKM.DimensionFormulaExamples
import OddMath.SKM.TwoStrandShiftExamples

/-!
# Consumers of the weight and mixed K₀ relations

The examples include two odd colours, both signs of a nonzero coroot weight,
zero weight, and integral even coefficients. No nondegeneracy input is used.
-/

noncomputable section
namespace OddMath.SKM.K0RelationsExamples
open CategoryTheory StringDiagrams CoveringQuantum K0Relations
open CoveringQuantum.UDot.ContextualExchangeExamples

private abbrev S := DimensionFormulaExamples.scalars
private abbrev hS := DimensionFormulaExamples.homogeneous
private abbrev sy := twoOddDatum.skmSymmetrizer
attribute [local instance] K0Relations.homModule

/-- Orthogonality and all positive/negative generator supports for two odd colours. -/
theorem odd_weights : WeightRelations S sy hS := weight_relations S sy hS

/-- Distinct odd colours require a parity shift, not an unshifted crossing. -/
theorem odd_distinct (ν : Bool → ℤ) :
    blockClass S sy hS (wt twoOddDatum.toSKM ν [up false, dn true]) ν
        [up false, dn true] rfl 0 0 -
      piCoeff 1 • blockClass S sy hS (wt twoOddDatum.toSKM ν [up false, dn true]) ν
        [dn true, up false] (by simp [wt, sh]; abel) 0 0 = 0 := by
  exact comm_ne S sy hS false true ν _ rfl (by simp [wt, sh]; abel) (by decide)

/-- The same-colour relation at every weight, including negative odd weights. -/
theorem odd_comm (i : Bool) (ν : Bool → ℤ) :
    blockClass S sy hS ν ν [up i, dn i] (by simp [wt, sh]) 0 0 -
      piCoeff 1 • blockClass S sy hS ν ν [dn i, up i] (by simp [wt, sh]) 0 0 =
      qpInt (qUnit 1) (piCoeff 1) (ν i) • blockClass S sy hS ν ν [] rfl 0 0 :=
  comm_same S sy hS i ν

/-- The positive-weight inversion has two shifted identity summands. -/
theorem positive_two :
    let ν : Bool → ℤ := fun _ => 2
    K₀.mk ((inclusion S sy hS ν ν).obj (ef S sy hS false ν 0)) =
      K₀.mk ((inclusion S sy hS ν ν).obj
        (fe S sy hS false ν (twoOddDatum.parity false + 0))) +
      ∑ n : Fin (twoOddDatum.h false ν).toNat,
        K₀.mk ((inclusion S sy hS ν ν).obj (idShift S sy hS ν
          (sy.d false * (twoOddDatum.h false ν - 1 - 2 * n.val)) (n.val * twoOddDatum.parity false + 0))) :=
  mixed_nonneg S sy hS false (fun _ => 2) 0 (by decide)

/-- The negative-weight inversion has two summands with the corrected degrees. -/
theorem negative_two :
    let ν : Bool → ℤ := fun _ => -2
    K₀.mk ((inclusion S sy hS ν ν).obj (fe S sy hS true ν 0)) =
      K₀.mk ((inclusion S sy hS ν ν).obj
        (ef S sy hS true ν (twoOddDatum.parity true + 0))) +
      ∑ n : Fin (-twoOddDatum.h true ν).toNat,
        K₀.mk ((inclusion S sy hS ν ν).obj (idShift S sy hS ν
          (sy.d true * (twoOddDatum.h true ν + 1 + 2 * n.val)) (n.val * twoOddDatum.parity true + 0))) :=
  mixed_nonpos S sy hS true (fun _ => -2) 0 (by decide)

/-- Zero weight, where the finite identity sum is empty. -/
theorem zero_weight :
    blockClass S sy hS (fun _ => 0) (fun _ => 0) [up false, dn false]
      (by simp [wt, sh]) 0 0 -
    piCoeff 1 • blockClass S sy hS (fun _ => 0) (fun _ => 0) [dn false, up false]
      (by simp [wt, sh]) 0 0 = 0 := by
  simpa [qpInt] using odd_comm false (fun _ => 0)

/-- The family also specializes to integral coefficients in even rank one. -/
theorem even_integral :
    let S := TwoStrandShiftConsumer.scalars
    let sy := TwoStrandShiftConsumer.symmetrizer
    let hc := TwoStrandShiftConsumer.homogeneous
    blockClass S sy hc (-3) (-3) [up (), dn ()] (by simp [wt, sh]) 0 0 -
      piCoeff 0 • blockClass S sy hc (-3) (-3) [dn (), up ()] (by simp [wt, sh]) 0 0 =
      qpInt (qUnit 1) (piCoeff 0) (-3) • blockClass S sy hc (-3) (-3) [] rfl 0 0 :=
  comm_same TwoStrandShiftConsumer.scalars
    TwoStrandShiftConsumer.symmetrizer TwoStrandShiftConsumer.homogeneous () (-3)

/-- A specialization of the negative quantum integer in the proof of Lemma 11.6. -/
theorem negative_two_coefficient :
    qpInt (Units.mk0 (2 : ℚ) (by norm_num)) (-1) (-2) = -3 / 2 := by
  rw [show (-2 : ℤ) = -(2 : ℕ) by rfl, qpInt_neg_natCast]
  norm_num [qpNat, Finset.sum_range_succ]

/-- The printed negative-weight scalar identity is false; the lemma statement is unchanged. -/
theorem printed_negative_coefficient_fails :
    qpInt (Units.mk0 (2 : ℚ) (by norm_num)) (-1) (-2) ≠
      -((-1 : ℚ) * qpNat (Units.mk0 (2 : ℚ) (by norm_num)) (-1) 2) := by
  rw [show (-2 : ℤ) = -(2 : ℕ) by rfl, qpInt_neg_natCast]
  norm_num [qpNat, Finset.sum_range_succ]

#print axioms K0Relations.weight_relations
#print axioms K0Relations.mixed_ne
#print axioms K0Relations.mixed_nonneg
#print axioms K0Relations.mixed_nonpos
#print axioms K0Relations.comm_same
#print axioms K0Relations.comm_ne
#print axioms K0Relations.covering_comm_same
#print axioms K0Relations.weight_mixed_relations

end OddMath.SKM.K0RelationsExamples
