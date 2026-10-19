import OddMath.SKM.MixedRealization
import OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples

/-! # Mixed matching degree-fibre examples for BE2 Theorem 10.3 -/

noncomputable section
namespace OddMath.SKM.MixedFibresExamples
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators
open PositiveDecoratedFamilyCoefficientsExamples (oddDatum)

abbrev B : List (Letter Unit) := [(false, ()), (true, ())]
def cup : List (TMove (Letter Unit)) := [.mv (.cup 0 (false, ()))]
def family : Set (List (TMove (Letter Unit))) := {cup}
def points (_ : {R // R ∈ family}) (_ : ℕ) : ℕ × ℕ := (1, 0)

theorem cup_matching : IsMatching₂ [] B cup := ⟨⟨by change 0 ≤ 0; decide, trivial⟩, rfl⟩
theorem cup_strict : StrictReduced₂ [] cup := by
  exact ⟨⟨List.nodup_nil, by simp [cup, tRun, tStart, tStep]⟩, List.nodup_singleton _⟩

theorem ends : leftEnds₂ [] cup = [0] := by
  have h (j : ℕ) : IsLeftEnd (pairing₂ [] cup) j ↔ j = 0 := by
    change (j < 2 ∧ ¬ ∃ k, k < j ∧ Same [(0, (false, ())), (0, (true, ()))] j k) ↔ j = 0
    constructor
    · intro h
      have hj := h.1
      interval_cases j
      · rfl
      · exact (h.2 ⟨0, by decide, by simp [Same, idAt]⟩).elim
    · rintro rfl
      exact ⟨by decide, by simp⟩
  unfold leftEnds₂
  simp only [show (pairing₂ [] cup).length = 2 from rfl, h]
  decide

theorem family_matching : ∀ R ∈ family, IsMatching₂ [] B R := by
  intro R hR
  have : R = cup := Set.mem_singleton_iff.mp hR
  subst R
  exact cup_matching

theorem family_unique : ∀ R ∈ family, ∀ S ∈ family,
    Iso (pairing₂ [] R) (pairing₂ [] S) → R = S := by
  intro R hR S hS _
  exact (Set.mem_singleton_iff.mp hR).trans (Set.mem_singleton_iff.mp hS).symm

theorem points_valid (R : {R // R ∈ family}) (j : ℕ) (hj : j ∈ leftEnds₂ [] R.val) :
    OnStrand₂ [] R.val j (points R j) ∧ (points R j).1 ≤ R.val.length := by
  have he : R.val = cup := Set.mem_singleton_iff.mp R.property
  rw [he, ends] at hj
  have : j = 0 := List.mem_singleton.mp hj
  subst j
  rw [he]
  change (0 < 2 ∧ 0 = 0) ∧ 1 ≤ 1
  decide

/-- Choose the bounded-point serializer once, for every natural label vector. -/
def serializer (R : {R // R ∈ family}) (c : MatchingStrand [] R.val → ℕ) : List (DTMove Unit) :=
  Classical.choose (exists_decorates₂_of_bounded_points [] R.val (points R)
    (fun j hj => (points_valid R j hj).1) (fun j hj => (points_valid R j hj).2) c)

theorem serializer_valid (R : {R // R ∈ family}) (c : MatchingStrand [] R.val → ℕ) :
    Decorates₂ [] R.val (points R) (strandCounts c) (serializer R c) :=
  (Classical.choose_spec (exists_decorates₂_of_bounded_points [] R.val (points R)
    (fun j hj => (points_valid R j hj).1) (fun j hj => (points_valid R j hj).2) c)).1

abbrev Index := Σ R : {R // R ∈ family}, MatchingStrand [] R.val → ℕ
def oneDot : Index := ⟨⟨cup, Set.mem_singleton _⟩, fun _ => 1⟩

theorem oneDot_degree : tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
    (dLay [] (serializer oneDot.1 oneDot.2)) = 3 := by
  classical
  have h := (mixed_decorated_degree_parity oddDatum.toSKM oddDatum.skmSymmetrizer 0
    cup_matching (points oneDot.1) (fun j hj => (points_valid oneDot.1 j hj).1)
    oneDot.2 _ (serializer_valid oneDot.1 oneDot.2)).1
  let j₀ : MatchingStrand [] cup := ⟨0, by rw [ends]; simp⟩
  have hj (j : MatchingStrand [] cup) : j = j₀ := by
    apply Subtype.ext
    have h := j.property
    simpa only [ends, List.mem_singleton] using h
  have hsum (f : MatchingStrand [] cup → ℤ) : ∑ j, f j = f j₀ := by
    apply Finset.sum_eq_single j₀
    · intro j _ hne
      exact (hne (hj j)).elim
    · simp
  change _ = tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0 (tLay [] cup) +
    ∑ j : MatchingStrand [] cup, (1 : ℤ) * (2 * oddDatum.skmSymmetrizer.d (matchingStrandColour [] cup j)) at h
  rw [hsum] at h
  change _ = (1 : ℤ) + 1 * (2 * 1) at h
  exact h

/-- A genuinely populated, odd nonzero degree fiber of a loop-free cup family. -/
theorem cup_degree_three :
    Set.Finite {t : Index | tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (dLay [] (serializer t.1 t.2)) = 3} ∧
    oneDot ∈ {t : Index | tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (dLay [] (serializer t.1 t.2)) = 3} := by
  exact ⟨mixed_labelled_degree_finite oddDatum.toSKM oddDatum.skmSymmetrizer 0 [] B family
    family_matching family_unique points (fun R j hj => (points_valid R j hj).1)
    serializer serializer_valid 3, oneDot_degree⟩

/-- The same chosen serializer has ordinary source branches in every degree. -/
theorem cup_ordinary_fibres :
    ∃ (L : Index → List (LayerData Unit)) (hL : ∀ t, SChain [] (L t) B),
      (∀ t, Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
        (mkD oddDatum.toSKM 0 (L t) (hL t)) =
        tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0 (dLay [] (serializer t.1 t.2))) ∧
      ∀ z : ℤ, Set.Finite {t : Index | Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
        (mkD oddDatum.toSKM 0 (L t) (hL t)) = z} :=
  mixed_labelled_source_degree_finite oddDatum.toSKM oddDatum.skmSymmetrizer 0 [] B family
    family_matching family_unique points (fun R j hj => (points_valid R j hj).1)
    serializer serializer_valid

/-- No colour inhabitant is used, including for the zero-strand boundary. -/
theorem empty_colour_fibres {X : Type*} [AddCommGroup X]
    (D : Datum Empty X) (sy : Symmetrizer D) (μ : X) (z : ℤ) :
    Set.Finite {_t : Σ R : {R : List (TMove (Letter Empty)) // R ∈ ({[]} : Set _)},
      MatchingStrand [] R.val → ℕ | tableDegree D sy μ (dLay [] ([] : List (DTMove Empty))) = z} := by
  apply mixed_labelled_degree_finite D sy μ [] [] ({[]} : Set _) _ _ (fun _ _ => (0, 0)) _
    (fun _ _ => []) _ z
  · intro R hR
    have : R = [] := Set.mem_singleton_iff.mp hR
    subst R
    exact ⟨trivial, rfl⟩
  · intro R hR S hS _
    exact (Set.mem_singleton_iff.mp hR).trans (Set.mem_singleton_iff.mp hS).symm
  · intro R j hj
    have he : R.val = [] := Set.mem_singleton_iff.mp R.property
    simp [he, leftEnds₂, pairing₂, tRun, tStart, cupMoves, run] at hj
  · intro R c
    have he : R.val = [] := Set.mem_singleton_iff.mp R.property
    constructor
    · exact he.symm
    · simp [he, leftEnds₂, pairing₂, tRun, tStart, cupMoves, run, DTMove.dotPts]

/-- The empty-colour fiber at zero contains its zero-strand labelled diagram. -/
theorem empty_colour_zero_member {X : Type*} [AddCommGroup X]
    (D : Datum Empty X) (sy : Symmetrizer D) (μ : X) :
    (⟨⟨[], Set.mem_singleton _⟩, fun _ => 0⟩ :
      Σ R : {R : List (TMove (Letter Empty)) // R ∈ ({[]} : Set _)},
        MatchingStrand [] R.val → ℕ) ∈
      {_t | tableDegree D sy μ (dLay [] ([] : List (DTMove Empty))) = 0} := rfl

/-- Empty representative families require no coverage premise. -/
theorem empty_family {I : Type*} (a b : List (Letter I)) :
    (∅ : Set (List (TMove (Letter I)))).Finite :=
  matching_representatives_finite a b ∅ (by simp) (by simp)

end OddMath.SKM.MixedFibresExamples
