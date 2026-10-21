import OddMath

/-! Non-vacuity checks in `NonVacuity.DecoratedEnumeration`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.DecoratedEnumeration

open OddMath.SKM StringDiagrams.Chord
open OddMath.SKM.PositiveDecoratedEnumerationExamples

-- Concrete representative families, with all coverage and uniqueness hypotheses proved.
example :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      Nonempty (({w : Equiv.Perm (Fin 2) // ∀ r, (fun _ => ()) r = (fun _ => ()) (w r)} ×
        (Fin 2 → ℕ)) ≃ {L // L ∈ decoratedFamily₂ repeatedWord repeatedFamily
          (fun R c => topDotMoves repeatedWord R (topPositionExtension repeatedFamily p R)
            (fun j => c j))}) := repeated_enumeration

example :
    ∃ p : ∀ R : {R : List (TMove (Letter Empty)) // R ∈ ({[]} : Set _)},
        MatchingStrand [] R.val ≃ Fin 0,
      Nonempty (({w : Equiv.Perm (Fin 0) // ∀ r, (Fin.elim0 r : Empty) = Fin.elim0 (w r)} ×
        (Fin 0 → ℕ)) ≃ {L // L ∈ decoratedFamily₂ [] ({[]} : Set _)
          (fun R c => topDotMoves [] R (topPositionExtension {[]} p R) (fun j => c j))}) :=
  empty_enumeration

example :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      let f := fun z : {R // R ∈ repeatedFamily} × (Fin 2 → ℕ) =>
        dLay repeatedWord (topDotMoves repeatedWord z.1.val
          (fun j => (p z.1 j).val) (fun j => z.2 (p z.1 j)))
      let R : {R // R ∈ repeatedFamily} := ⟨[], by simp [repeatedFamily]⟩
      let S : {R // R ∈ repeatedFamily} := ⟨[.mv (.cross 0)], by simp [repeatedFamily]⟩
      f (R, ![1, 2]) ≠ f (S, ![1, 2]) ∧ f (S, ![1, 2]) ≠ f (S, ![2, 1]) :=
  repeated_decorations_distinct

end NonVacuity.DecoratedEnumeration
