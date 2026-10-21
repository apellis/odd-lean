import OddMath

/-! Non-vacuity checks in `NonVacuity.Claim4Coefficients`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Claim4Coefficients
open OddMath.SKM OddMath.CoveringQuantum UDot GenericTensor GenericVerma.MixedGram
open UDot.ContextualExchangeExamples
open scoped BigOperators

example (k : Bool) :
    let a := (true, false) :: (false, true) ::
      (if k then [(false, false), (true, true)] else [(true, true), (false, false)])
    let b := (false, true) :: (true, false) ::
      (if k then [(false, false), (true, true)] else [(true, true), (false, false)])
    ∃ (T U : Type) (d : T → ℤ) (e : U → ℤ) (p : T → ZMod 2) (q : U → ZMod 2)
      (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
      (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
      (∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
        ((∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm twoOddDatum
          (algebraWord twoOddDatum 0 a) (algebraWord twoOddDatum 0 []))).coeff z =
            ∑ t ∈ (hf z).toFinset, σ ^ (p t).val) ↔
         (∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm twoOddDatum
          (algebraWord twoOddDatum 0 b) (algebraWord twoOddDatum 0 []))).coeff z =
            ∑ u ∈ (hg z).toFinset, σ ^ (q u).val))) ∧
      (∃ t, d t = 4) ∧ (∃ t, d t = 2) ∧ (∃ u, e u = 2) ∧
      (∀ (σ : ℚ), σ ^ 2 = 1 →
        (∑ t ∈ (hf 2).toFinset, σ ^ (p t).val) = σ ^ (if k then 0 else 1) ∧
        (∑ u ∈ (hg 2).toFinset, σ ^ (q u).val) = σ * σ ^ (if k then 0 else 1)) ∧
      (∑ t ∈ (hf 2).toFinset, (-1 : ℚ) ^ (p t).val) ≠
        ∑ u ∈ (hg 2).toFinset, (-1 : ℚ) ^ (q u).val := by
  classical
  obtain ⟨hf, hg, hiff, hdot, htwo, htwo', hvalues, hne⟩ :=
    Claim4CoefficientsExamples.populated_iff k
  exact ⟨_, _, _, _, _, _, hf, hg, hiff,
    ⟨hdot.choose, hdot.choose_spec.1⟩, htwo, htwo', hvalues, hne⟩

example (k : Bool) : ∃ (T U : Type) (d : T → ℤ) (e : U → ℤ)
    (p : T → ZMod 2) (q : U → ZMod 2)
    (hf : Set.Finite {t | d t = 5}) (hg : Set.Finite {u | e u = 5}),
    (∃ t, d t = 5) ∧ (∃ u, e u = 5) ∧
    (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (p t).val) = (-1 : ℚ) ^ (if k then 1 else 0) ∧
    (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (q u).val) = -1 * (-1 : ℚ) ^ (if k then 1 else 0) := by
  classical
  obtain ⟨hf, hg, hdot, hu, hs, ht⟩ :=
    BoundaryFamilyExamples.populated_coefficient k (-1) (by norm_num)
  exact ⟨_, _, _, _, _, _, hf, hg, ⟨hdot.choose, hdot.choose_spec.1⟩, hu, hs, ht⟩

example (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm twoOddDatum
      (algebraWord twoOddDatum 0 [(false, false), (true, false), (false, true), (true, true)])
      (algebraWord twoOddDatum 0 []))).coeff z =
    σ * (signLaurent σ hσ (sesquilinearForm twoOddDatum
      (algebraWord twoOddDatum 0 [(false, false), (false, true), (true, false), (true, true)])
      (algebraWord twoOddDatum 0 []))).coeff z :=
  twoOdd_context_coeff σ hσ z

end NonVacuity.Claim4Coefficients
