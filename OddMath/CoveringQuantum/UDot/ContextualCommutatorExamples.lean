import OddMath.CoveringQuantum.UDot.ContextualCommutator
import OddMath.SKM.PositiveFormCoefficientsExamples

/-! Nonempty contextual consumers and a coefficient-bar diagnostic for BE2 Theorem 10.3 Claim 5. -/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.ContextualCommutatorExamples
open Coefficients GenericTensor GenericVerma.MixedGram
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples

/-- The suffix E ends at weight two, while its F-prefix closes the word at zero. -/
theorem odd_context_endpoints :
    OddMath.SKM.wt oddDatum.toSKM 0 [(true, ())] = 2 ∧
    oddDatum.h () (OddMath.SKM.wt oddDatum.toSKM 0 [(true, ())]) = 2 ∧
    OddMath.SKM.wt oddDatum.toSKM 0 [(false, ()), (true, ())] = 0 ∧
    (algebraWord oddDatum 0 [(true, ())]).val ∈ block oddDatum Coefficients.q pi 2 0 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact algebraWord_mem_block oddDatum 0 [(true, ())]

private theorem quantum_two : qpInt Coefficients.q pi 2 =
    (Coefficients.q : Coefficients.Ring) +
      pi * ((Coefficients.q⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring) := by
  change qpNat Coefficients.q pi 2 = _
  exact qpNat_two

/-- A nonzero weight with nonempty context: the scalar is q⁻¹+πq, not q+πq⁻¹. -/
theorem odd_context_commutator :
    sesquilinearForm oddDatum odd_barConsistent
      (algebraWord oddDatum 0 [(false, ()), (true, ()), (false, ()), (true, ())])
      (algebraWord oddDatum 0 []) -
    pi * sesquilinearForm oddDatum odd_barConsistent
      (algebraWord oddDatum 0 [(false, ()), (false, ()), (true, ()), (true, ())])
      (algebraWord oddDatum 0 []) =
    (((Coefficients.q⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring) +
      pi * (Coefficients.q : Coefficients.Ring)) *
      sesquilinearForm oddDatum odd_barConsistent
        (algebraWord oddDatum 0 [(false, ()), (true, ())]) (algebraWord oddDatum 0 []) := by
  have h := sesquilinearForm_context_EF oddDatum odd_barConsistent 0
    [(false, ())] [(true, ())] ()
  have hw : oddDatum.h () (OddMath.SKM.wt oddDatum.toSKM 0 [(true, ())]) = 2 := rfl
  rw [hw] at h
  have hq : oddDatum.qi Coefficients.q () = Coefficients.q := by simp [SuperCartanDatum.qi, oddDatum]
  have hp : oddDatum.pii pi () = pi := by simp [SuperCartanDatum.pii, oddDatum, ZMod.val_one]
  rw [hq, hp] at h
  have hb : bar (qpInt Coefficients.q pi 2) =
      ((Coefficients.q⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring) +
        pi * (Coefficients.q : Coefficients.Ring) := by
    rw [quantum_two, map_add, map_mul, bar_pi, bar_q]
    have hh := bar_bar (Coefficients.q : Coefficients.Ring)
    rw [bar_q] at hh
    rw [hh]
  simpa only [hb, List.cons_append, List.nil_append] using h

/-- The unbarred and barred quantum integers are distinguished by a formal coefficient;
q is not numerically evaluated. -/
theorem odd_two_bar_ne : bar (qpInt Coefficients.q pi 2) ≠ qpInt Coefficients.q pi 2 := by
  have hq (σ : ℚ) (hσ : σ ^ 2 = 1) :
      signLaurent σ hσ (((Coefficients.q⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring)) =
        HahnSeries.single (-1) 1 := by
    simpa only [qp, zpow_neg_one] using signLaurent_qp σ hσ (-1)
  have hb : bar (qpInt Coefficients.q pi 2) =
      ((Coefficients.q⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring) +
        pi * (Coefficients.q : Coefficients.Ring) := by
    rw [quantum_two, map_add, map_mul, bar_pi, bar_q]
    have hh := bar_bar (Coefficients.q : Coefficients.Ring)
    rw [bar_q] at hh
    rw [hh]
  intro h
  rw [hb, quantum_two] at h
  have he := congrArg (fun c => (signLaurent (-1) (by norm_num) c).coeff 1) h
  simp only [map_add, map_mul, hq, signLaurent_q,
    signLaurent_pi, HahnSeries.coeff_add, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_single] at he
  norm_num at he

/-- Dropping the bar in the first-slot commutator fails already at odd weight two.
This tests the contextual headline itself, not just the original defining relation. -/
theorem odd_unbarred_commutator_false :
    sesquilinearForm oddDatum odd_barConsistent
      (algebraWord oddDatum 2 [(true, ()), (false, ())]) (algebraWord oddDatum 2 []) -
    pi * sesquilinearForm oddDatum odd_barConsistent
      (algebraWord oddDatum 2 [(false, ()), (true, ())]) (algebraWord oddDatum 2 []) ≠
    qpInt Coefficients.q pi 2 := by
  have hn : sesquilinearForm oddDatum odd_barConsistent
      (algebraWord oddDatum 2 []) (algebraWord oddDatum 2 []) = 1 := by
    have he : algebraWord oddDatum 2 [] = positiveHalf oddDatum Coefficients.q pi 2
        (oddDatum.toSerreF Coefficients.q pi (PreF.monomial Coefficients.Ring [])) := by
      apply Subtype.ext
      simp only [PreF.monomial_nil, map_one, positiveHalf_one, algebraWord]
    rw [he, sesquilinearForm_positiveHalf, GenericVerma.halfBar_monomial]
    simp only [PreF.monomial_nil, map_one, SuperCartanDatum.serreForm_one_one]
  have h := sesquilinearForm_context_EF oddDatum odd_barConsistent 2 [] [] ()
  have hw : oddDatum.h () (OddMath.SKM.wt oddDatum.toSKM 2 []) = 2 := rfl
  have hq : oddDatum.qi Coefficients.q () = Coefficients.q := by
    simp [SuperCartanDatum.qi, oddDatum]
  have hp : oddDatum.pii pi () = pi := by
    simp [SuperCartanDatum.pii, oddDatum, ZMod.val_one]
  simp only [List.nil_append, hw, hq, hp, hn, mul_one] at h
  rw [h]
  exact odd_two_bar_ne

end OddMath.CoveringQuantum.UDot.ContextualCommutatorExamples
