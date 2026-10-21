import OddMath

/-! Non-vacuity checks in `NonVacuity.LeftCupFamilyCoefficients`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.LeftCupFamilyCoefficients
open OddMath.SKM
open scoped BigOperators

example : ∃ (T U : Type) (d : T → ℤ) (e : U → ℤ)
    (p : T → ZMod 2) (q : U → ZMod 2)
    (hf : Set.Finite {x | d x = 1}) (hg : Set.Finite {u | e u = 0}),
    (∃ x, d x = 1) ∧ (∃ u, e u = 0) ∧
    (∑ x ∈ hf.toFinset, (-1 : ℚ) ^ (p x).val) = -1 ∧
    (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (q u).val) = 1 ∧
    (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (q u).val) ≠
      ∑ x ∈ hf.toFinset, (-1 : ℚ) ^ (p x).val := by
  classical
  obtain ⟨hf, hg, hx, hu, hs, ht, hne⟩ :=
    LeftCupFamilyCoefficientsExamples.left_cup_negative_sign_distinction
  exact ⟨_, _, _, _, _, _, hf, hg, hx, hu, hs, ht, hne⟩

end NonVacuity.LeftCupFamilyCoefficients
