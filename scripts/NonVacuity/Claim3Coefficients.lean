import OddMath

/-! Non-vacuity checks in `NonVacuity.Claim3Coefficients`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Claim3Coefficients
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
        (algebraWord oddDatum 0 [(false, ()), (true, ())])
        (algebraWord oddDatum 0 []))).coeff z =
          ∑ t ∈ (hf z).toFinset, σ ^ (p t).val) ↔
       (∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm oddDatum
        (algebraWord oddDatum 0 [(true, ())])
        (algebraWord oddDatum 0 [(true, ())]))).coeff z =
          ∑ u ∈ (hg z).toFinset, σ ^ (q u).val))) ∧
    (∃ t, d t = 1) ∧ (∃ u, e u = 0) ∧
    (∑ t ∈ (hf 1).toFinset, (-1 : ℚ) ^ (p t).val) = -1 ∧
    (∑ u ∈ (hg 0).toFinset, (-1 : ℚ) ^ (q u).val) = 1 := by
  classical
  obtain ⟨hf, hg, hiff, hcounts⟩ := Claim3CoefficientsExamples.cap_form_coeff_iff
  obtain ⟨hx, hu, hs, ht⟩ := hcounts 0 (-1) (by norm_num)
  refine ⟨_, _, _, _, _, _, hf, hg, hiff, ?_, ?_, ?_, ?_⟩
  · simpa using hx
  · simpa using hu
  · simpa [show (1 : ZMod 2).val = 1 from rfl] using hs
  · rw [hs] at ht
    simpa [show (1 : ZMod 2).val = 1 from rfl] using ht

example : ∃ (T U : Type) (d : T → ℤ) (e : U → ℤ)
    (p : T → ZMod 2) (q : U → ZMod 2)
    (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
    (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
    (∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
      ((∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm oddDatum
        (algebraWord oddDatum 0 [(false, ())]) (algebraWord oddDatum 0 []))).coeff z =
          ∑ t ∈ (hf z).toFinset, σ ^ (p t).val) ↔
       (∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm oddDatum
        (algebraWord oddDatum 0 []) (algebraWord oddDatum 0 [(true, ())]))).coeff z =
          ∑ u ∈ (hg z).toFinset, σ ^ (q u).val))) ∧
    (∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      (signLaurent σ hσ (sesquilinearForm oddDatum
        (algebraWord oddDatum 0 [(false, ())]) (algebraWord oddDatum 0 []))).coeff z = 0 ∧
      (signLaurent σ hσ (sesquilinearForm oddDatum
        (algebraWord oddDatum 0 []) (algebraWord oddDatum 0 [(true, ())]))).coeff z = 0 ∧
      (∑ t ∈ (hf z).toFinset, σ ^ (p t).val) = 0 ∧
      (∑ u ∈ (hg z).toFinset, σ ^ (q u).val) = 0) := by
  classical
  obtain ⟨hf, hg, hiff⟩ := Claim3CoefficientsExamples.Mismatch.empty_form_coeff_iff
  exact ⟨_, _, _, _, _, _, hf, hg, hiff, fun σ hσ z =>
    Claim3CoefficientsExamples.Mismatch.empty_coefficients_zero σ hσ z (hf z) (hg z)⟩

end NonVacuity.Claim3Coefficients
