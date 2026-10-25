import OddMath.SKM.CanonicalUpwardMatching

/-! Repeated-colour, non-involutive endpoint tests of the PBW skeleton family. -/
noncomputable section
namespace NonVacuity.CanonicalUpwardMatching
open StringDiagrams StringDiagrams.Chord Categorification.TypeA OddMath.SKM
open CanonicalUpward
private def a : Fin 3 → Bool := fun _ => false
private def w : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
private def A : List (Letter Bool) := List.ofFn fun j => (true, a j)

/-- All three colours agree, but the endpoints still detect the 3-cycle. -/
theorem repeated_colour_canonical :
    IsMatching₂ A A (crossingMoves (canWord 3 w)) ∧
      StrictReduced₂ A (crossingMoves (canWord 3 w)) := by
  simpa only [A, a] using canonical_matching a w

theorem permutation_not_its_inverse : w (0 : Fin 3) ≠ w⁻¹ (0 : Fin 3) := by decide

theorem first_strand_endpoint :
    Same (pairing₂ A (crossingMoves (canWord 3 w))) 2 4 := by
  have hv : ValidWord A.length (canWord 3 w) := by
    change ValidWord 3 _
    exact validWord_canWord 3 w
  have h := crossing_pairing A (canWord 3 w) hv ⟨0, by decide⟩
  change Same _ 2 (3 + (wordProd 3 (canWord 3 w) ⟨0, by decide⟩).val) at h
  rw [wordProd_canWord] at h
  exact h

private def t : List Bool := [false, false, false]

theorem canonical_family_nonempty : Nonempty (choiceList t t rfl).members := by
  have hm : IsMatching₂ (ups t) (ups t) [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ (ups t) [] := by
    constructor
    · change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
      simp
    · change ([] : List ℕ).Nodup
      simp
  obtain ⟨R, hR, _⟩ := (choiceList t t rfl).complete [] hm hr
  exact ⟨⟨R, hR⟩⟩

theorem literal_family_word (R : (choiceList t t rfl).members) :
    R.val = (canWord t.length (choiceList_word t t rfl R)).reverse.map
      (fun p => TMove.mv (Move.cross p)) := choiceList_word_spec t t rfl R

#print axioms repeated_colour_canonical
#print axioms first_strand_endpoint
#print axioms canonical_family_nonempty
#print axioms literal_family_word
end NonVacuity.CanonicalUpwardMatching
