import OddMath.SKM.LeftCupNormalization
import OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples

/-! Nonempty odd-root consumer of normalized left-cup transport.
The source has an internal cup, a dot on its fresh strand and a cap.
The independently serialized target is one left cup with a dot on its upward leg. -/
namespace OddMath.SKM.LeftCupNormalizationExamples
open StringDiagrams StringDiagrams.Chord DTMove CoveringQuantum
open PositiveDecoratedFamilyCoefficientsExamples (oddDatum)

private abbrev A : List (Letter Unit) := [(false, ())]
private abbrev R : List (TMove (Letter Unit)) := [.mv (.cup 1 (true, ())), .cap 0]
private abbrev ds : List (DTMove Unit) := [.tm (.mv (.cup 1 (true, ()))), .dt 2, .tm (.cap 0)]
private def q (_ : ℕ) : ℕ × ℕ := (1, 2)
private def c (_ : MatchingStrand A R) : ℕ := 1

private theorem matching : IsMatching₂ A A R := by
  constructor
  · refine ⟨by change 2 ≤ 2; decide, ?_⟩
    refine ⟨?_, trivial⟩
    exact ⟨(0, (false, ())), (2, (true, ())), rfl, rfl, rfl, by decide⟩
  · rfl

private theorem ends : leftEnds₂ A R = [0] := by
  have h (j : ℕ) : IsLeftEnd (pairing₂ A R) j ↔ j = 0 := by
    change (j < 2 ∧ ¬ ∃ k, k < j ∧ Same [(0, (true, ())), (0, (false, ()))] j k) ↔ j = 0
    constructor
    · intro h
      have hj := h.1
      interval_cases j
      · rfl
      · exact (h.2 ⟨0, by decide, by simp [Same, idAt]⟩).elim
    · rintro rfl
      exact ⟨by decide, by simp⟩
  unfold leftEnds₂
  simp only [show (pairing₂ A R).length = 2 from rfl, h]
  decide

private theorem points : ∀ j ∈ leftEnds₂ A R,
    (q j).1 ≤ R.length ∧ OnStrand₂ A R j (q j) := by
  intro j hj
  rw [ends] at hj
  obtain rfl := List.mem_singleton.mp hj
  change 1 ≤ 2 ∧ 2 < 3 ∧ 0 = 0
  decide

private theorem decoration : Decorates₂ A R q (strandCounts c) ds := by
  constructor
  · rfl
  · simp [dotPts, ends, strandCounts, c, q]

private theorem reduced : Reduced₂ A R := by
  constructor
  · exact List.nodup_nil
  · intro z hz
    change z ∈ ([] : List (Sym2 ℕ)) at hz
    exact False.elim (List.not_mem_nil hz)

private abbrev S : List (TMove (Letter Unit)) := [.mv (.cup 0 (true, ()))]
private abbrev es : List (DTMove Unit) := [.tm (.mv (.cup 0 (true, ()))), .dt 0]
private def r (_ : ℕ) : ℕ × ℕ := (1, 0)

private theorem target_matching : IsMatching₂ [] [(true, ()), (false, ())] S := by
  exact ⟨⟨by change 0 ≤ 0; decide, trivial⟩, rfl⟩

private theorem target_reduced : Reduced₂ [] S := by
  constructor
  · exact List.nodup_nil
  · intro z hz
    change z ∈ ([] : List (Sym2 ℕ)) at hz
    exact False.elim (List.not_mem_nil hz)

private theorem pairing_iso : Iso (pairing₂ A R) (pairing₂ [] S) := Iso.refl _

private theorem target_ends : leftEnds₂ [] S = [0] := ends

private theorem target_points : ∀ j ∈ leftEnds₂ [] S, OnStrand₂ [] S j (r j) := by
  intro j hj
  rw [target_ends] at hj
  obtain rfl := List.mem_singleton.mp hj
  change 0 < 2 ∧ 0 = 0
  decide

private theorem target_decoration : Decorates₂ [] S r
    (strandCounts (c ∘ (matchingStrandEquivOfIso pairing_iso).symm)) es := by
  constructor
  · rfl
  · simp [dotPts, target_ends, strandCounts, c, r]

/-- The source-style theorem is applied with every geometric and decoration premise
constructed. The source and target points are `(1,2)` and `(1,0)`, rather than the
literal attachment point `(2,3)`. -/
theorem normalized_internal_cap_odd_shift :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay [] es) =
      tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay A ds) - 1 ∧
    xpar oddDatum.toSKM 2 (dLay [] es) = xpar oddDatum.toSKM 2 (dLay A ds) + 1 := by
  obtain ⟨hd, hp⟩ := leftCupAttach_normalized_decorated_degree_parity
    oddDatum.toSKM oddDatum.skmSymmetrizer 2 matching reduced target_matching target_reduced
    pairing_iso q r points target_points c ds es decoration target_decoration
  have hdeg : oddDatum.skmSymmetrizer.d () *
      (1 - oddDatum.toSKM.h () (wt oddDatum.toSKM 2 [])) = -1 := by decide
  have hpar : ipar oddDatum.toSKM () (wt oddDatum.toSKM 2 []) = 1 := by decide
  rw [hdeg] at hd
  exact ⟨by simpa only [sub_eq_add_neg] using hd, by simpa only [hpar] using hp⟩

/-- The diagrams and dot counts are nonempty. Source degree/parity are 2/1;
the normalized target has degree/parity 1/0, so both transport shifts are nonzero. -/
theorem normalized_internal_cap_values :
    R ≠ [] ∧ S ≠ [] ∧ ds ≠ [] ∧ es ≠ [] ∧
    (∃ j : MatchingStrand A R, c j = 1) ∧
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay A ds) = 2 ∧
    xpar oddDatum.toSKM 2 (dLay A ds) = 1 ∧
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay [] es) = 1 ∧
    xpar oddDatum.toSKM 2 (dLay [] es) = 0 := by
  have hd : tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay A ds) = 2 := by decide
  have hp : xpar oddDatum.toSKM 2 (dLay A ds) = 1 := by decide
  obtain ⟨htd, htp⟩ := normalized_internal_cap_odd_shift
  refine ⟨by decide, by decide, by decide, by decide, ?_, hd, hp, ?_, ?_⟩
  · exact ⟨⟨0, by rw [ends]; decide⟩, rfl⟩
  · rw [hd] at htd
    exact htd.trans (by decide)
  · rw [hp] at htp
    exact htp.trans (by decide)


end OddMath.SKM.LeftCupNormalizationExamples
