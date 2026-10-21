import OddMath

/-! Non-vacuity checks in `NonVacuity.Claim5CapAndNoncap`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Claim5CapAndNoncap
open OddMath.SKM
open OddMath.SKM.NoncapFamilyCoefficientsExamples
open scoped BigOperators

-- A populated coefficient cancellation, with unequal signed coefficients.
example : ∃ (hf : Set.Finite {t : T false | d false t = 2})
    (hg : Set.Finite {u : U false | e false u = 2}),
    (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (p false t).val) = 2 ∧
    (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' false u).val) = -2 ∧
    (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (p false t).val) +
      (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' false u).val) = 0 ∧
    (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (p false t).val) ≠
      (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' false u).val) := by
  obtain ⟨hf, hg, h1, h2⟩ := (both_signs false).2
  refine ⟨hf, hg, h1, h2, ?_, ?_⟩ <;> rw [h1, h2] <;> norm_num

-- The other intersection branch reverses both signs.
example : ∃ (hf : Set.Finite {t : T true | d true t = 2})
    (hg : Set.Finite {u : U true | e true u = 2}),
    (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (p true t).val) = -2 ∧
    (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' true u).val) = 2 :=
  (both_signs true).2

open StringDiagrams StringDiagrams.Chord
open MixedCrossingLocalExamples (oddDatum oddSymmetrizer)

example (ε : Bool) :
    let A : List (Letter Bool) := [(true, true), (ε, false), (!ε, false), (false, true)]
    let R : List (TMove (Letter Bool)) := [.cap 1, .cap 0]
    ∃ (c : MatchingStrand A R → ℕ) (j k : MatchingStrand A R),
      matchingStrandColour A R j = false ∧ matchingStrandColour A R k = true ∧
      c j = 3 ∧ c k = 2 := by
  obtain ⟨j, hj, hc, hcap⟩ := CapStrandsExamples.nonempty_labels ε 3 2
  exact ⟨_, _, _, (CapStrandsExamples.strand_colours ε true).1,
    ((CapStrandsExamples.strand_colours ε true).2 j).trans hj, hcap, hc⟩

example :
    let A : Bool → List (Letter Bool) := fun ε =>
      [(true, false), (ε, false), (!ε, false), (false, false)]
    let B : List (Letter Bool) := [(true, false), (false, false)]
    let R : List (TMove (Letter Bool)) := [.cap 1, .cap 0]
    let S : List (TMove (Letter Bool)) := [.cap 0]
    tableDegree oddDatum oddSymmetrizer 0 (tLay (A true) R) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay B S) + 3 ∧
    xpar oddDatum 0 (tLay (A true) R) = xpar oddDatum 0 (tLay B S) ∧
    tableDegree oddDatum oddSymmetrizer 0 (tLay (A false) R) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay B S) - 1 ∧
    xpar oddDatum 0 (tLay (A false) R) = xpar oddDatum 0 (tLay B S) + 1 :=
  CapNormalizationExamples.odd_nonempty_cap_values

end NonVacuity.Claim5CapAndNoncap
