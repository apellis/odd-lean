import OddMath

/-! Non-vacuity checks in `NonVacuity.Claim5MatchingClasses`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Claim5MatchingClasses
open StringDiagrams StringDiagrams.Chord OddMath.SKM
open MixedCrossingLocalExamples (oddDatum oddSymmetrizer)
open BoundaryExchangeExamples

example :
    tableDegree oddDatum oddSymmetrizer 0 (tLay B S) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay A R) ∧
    xpar oddDatum 0 (tLay B S) = xpar oddDatum 0 (tLay A R) + 1 :=
  existing_intersection_normalized

example :
    tableDegree oddDatum oddSymmetrizer 0 (tLay B₀ S₀) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay A₀ R₀) ∧
    xpar oddDatum 0 (tLay B₀ S₀) = xpar oddDatum 0 (tLay A₀ R₀) + 1 :=
  no_intersection_normalized

example : Ilv (pairing₂ A R) 2 ∧ ¬ Ilv (pairing₂ A₀ R₀) 2 :=
  ⟨existing_intersection, no_existing_intersection⟩

example (ε k : Bool) :
    let a : List (Letter Bool) := if k then [(true, true)] else []
    let b : List (Letter Bool) := if k then [(false, true)] else []
    let C := a ++ (ε, false) :: (!ε, false) :: b
    ∃ (M N : Set (List (TMove (Letter Bool))))
      (E : {V // V ∈ M ∧ Same (pairing₂ C V) b.length (b.length + 1)} ≃ {W // W ∈ N})
      (r : {V // V ∈ M ∧ Same (pairing₂ C V) b.length (b.length + 1)})
      (s : {W // W ∈ N}),
      E.symm (E r) = r ∧ E (E.symm s) = s ∧
      (∀ V, Iso (pairing₂ (a ++ b) (E V).val) (rmAt (pairing₂ C V.val) b.length)) ∧
      (∀ W, Iso (pairing₂ C (E.symm W).val) (capInsertedPairing a b ε false W.val)) := by
  exact ⟨_, _, _, _, _, (CapFamilyExamples.odd_cap_roundtrips ε k).2.1,
    (CapFamilyExamples.odd_cap_roundtrips ε k).2.2, CapFamilyExamples.odd_cap_pairings ε k⟩

end NonVacuity.Claim5MatchingClasses
