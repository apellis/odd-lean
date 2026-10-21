import OddMath

/-! Non-vacuity checks in `NonVacuity.Claim2Coefficients`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Claim2Coefficients
open OddMath.SKM OddMath.CoveringQuantum UDot GenericTensor GenericVerma.MixedGram
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples (oddDatum)
open OddMath.SKM.PositiveFormCoefficientsExamples (odd_barConsistent)
open scoped BigOperators

example : ∃ (T U : Type) (d : T → ℤ) (e : U → ℤ)
    (p : T → ZMod 2) (q : U → ZMod 2)
    (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
    (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
    (∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
      ((∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm oddDatum
        (algebraWord oddDatum 0 [(true, ()), (false, ())])
        (algebraWord oddDatum 0 []))).coeff z =
          ∑ t ∈ (hf z).toFinset, σ ^ (p t).val) ↔
       (∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm oddDatum
        (algebraWord oddDatum 0 [(false, ())])
        (algebraWord oddDatum 0 [(false, ())]))).coeff z =
          ∑ u ∈ (hg z).toFinset, σ ^ (q u).val))) ∧
    (∃ t, d t = 3) ∧ (∃ u, e u = 2) := by
  classical
  obtain ⟨hf, hg, hiff, hcounts⟩ := Claim2CoefficientsExamples.cap_form_coeff_iff
  refine ⟨_, _, _, _, _, _, hf, hg, hiff, ?_, ?_⟩
  · simpa using (hcounts 1 1).1
  · simpa using (hcounts 1 1).2.1

example (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm oddDatum
      (algebraWord oddDatum 0 [(true, ()), (true, ()), (false, ())])
      (algebraWord oddDatum 0 [(true, ()), (false, ())]))).coeff z = 0 ∧
    (signLaurent σ hσ (sesquilinearForm oddDatum
      (algebraWord oddDatum 0 [(true, ()), (false, ())])
      (algebraWord oddDatum 0 [(false, ()), (true, ()), (false, ())]))).coeff z = 0 := by
  obtain ⟨_, _, _, hzero⟩ := Claim2MismatchExamples.mismatch_form_coeff_iff
  exact ⟨(hzero σ hσ z).1, (hzero σ hσ z).2.1⟩

end NonVacuity.Claim2Coefficients
