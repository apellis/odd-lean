import OddMath.SKM.BoundedPointSerialization

/-!
# Bounded-point serialization examples

Interior points, unsorted heights, zero counts, empty boundaries, and noncanonical
dot order exercise the distinguished-point construction supporting BE2 §8.
-/

namespace OddMath.SKM.BoundedPointSerializationExamples
open StringDiagrams.Chord DTMove

private def A : List (Letter Unit) := List.ofFn fun _ : Fin 3 => (true, ())
private def R : List (TMove (Letter Unit)) := [.mv (.cross 0), .mv (.cross 1)]
private def q (j : ℕ) : ℕ × ℕ := (1, if j = 0 then 2 else if j = 1 then 0 else 1)

private theorem matching : IsMatching₂ A A R := by
  constructor
  · change 4 < 6 ∧ 5 < 6 ∧ True
    decide
  · rfl

private theorem points : ∀ j ∈ leftEnds₂ A R, OnStrand₂ A R j (q j) := by
  intro j hj
  have hj' : j < 3 := (positive_mem_leftEnds₂ (fun _ : Fin 3 => ())
    (fun _ : Fin 3 => ()) matching j).mp hj
  interval_cases j <;> unfold OnStrand₂ <;> decide

/-- Three strands with nonuniform multiplicities at an interior height, not at the top. -/
theorem interior_counts :
    ∃ ds : List (DTMove Unit),
      Decorates₂ A R q (strandCounts fun j : MatchingStrand A R => j.val + 1) ds ∧ DOk₂ A ds := by
  exact exists_decorates₂_of_bounded_points A R q points (by intro j _; change 1 ≤ 2; decide)
    (fun j => j.val + 1)

/-- Zero multiplicities work with the same nonempty matching and interior points. -/
theorem zero_counts :
    ∃ ds : List (DTMove Unit),
      Decorates₂ A R q (strandCounts fun _ : MatchingStrand A R => 0) ds ∧ DOk₂ A ds := by
  exact exists_decorates₂_of_bounded_points A R q points (by intro j _; change 1 ≤ 2; decide)
    (fun _ => 0)

/-- The interleaving lemma accepts unsorted heights, repeated points, and both boundaries. -/
theorem unsorted_boundaries :
    ∃ ds : List (DTMove Unit), tmoves ds = R ∧
      (dotPts ds).Perm [(2, 1), (0, 2), (1, 0), (0, 1), (2, 1)] := by
  apply exists_tmoves_dotPts_perm
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide

/-- An explicit interior serialization with interleaved rather than strand-block dot order. -/
theorem noncanonical_order :
    tmoves ([.tm (.mv (.cross 0)), .dt 1, .dt 0, .dt 2, .dt 1, .dt 0, .dt 1,
      .tm (.mv (.cross 1))] : List (DTMove Unit)) = R ∧
    (dotPts ([.tm (.mv (.cross 0)), .dt 1, .dt 0, .dt 2, .dt 1, .dt 0, .dt 1,
      .tm (.mv (.cross 1))] : List (DTMove Unit))).Perm
      [(1, 2), (1, 0), (1, 0), (1, 1), (1, 1), (1, 1)] ∧
    DOk₂ A [.tm (.mv (.cross 0)), .dt 1, .dt 0, .dt 2, .dt 1, .dt 0, .dt 1,
      .tm (.mv (.cross 1))] := by
  refine ⟨rfl, ?_, ?_⟩
  · decide
  · simp only [DOk₂]
    decide

private theorem leftEnds : leftEnds₂ A R = [0, 1, 2] := by
  calc
    leftEnds₂ A R = (List.range 6).filter (fun j => decide (j < 3)) := by
      unfold leftEnds₂
      change (List.range 6).filter _ = _
      apply List.filter_congr
      intro j _
      simp only [decide_eq_decide]
      rw [← mem_leftEnds₂]
      exact positive_mem_leftEnds₂ (fun _ : Fin 3 => ()) (fun _ : Fin 3 => ()) matching j
    _ = [0, 1, 2] := by decide

/-- The explicit noncanonical ordering satisfies the actual decoration relation. -/
theorem noncanonical_decorates :
    Decorates₂ A R q (strandCounts fun j : MatchingStrand A R => j.val + 1)
      [.tm (.mv (.cross 0)), .dt 1, .dt 0, .dt 2, .dt 1, .dt 0, .dt 1,
        .tm (.mv (.cross 1))] ∧
    DOk₂ A [.tm (.mv (.cross 0)), .dt 1, .dt 0, .dt 2, .dt 1, .dt 0, .dt 1,
      .tm (.mv (.cross 1))] := by
  refine ⟨⟨noncanonical_order.1, ?_⟩, noncanonical_order.2.2⟩
  simpa [leftEnds, strandCounts, q] using noncanonical_order.2.1

/-- No moves and no strands: even the point function is unrestricted. -/
theorem empty_boundary (q₀ : ℕ → ℕ × ℕ) :
    ∃ ds : List (DTMove Unit),
      Decorates₂ [] [] q₀ (strandCounts fun _ : MatchingStrand ([] : List (Letter Unit)) [] => 0) ds ∧ DOk₂ [] ds := by
  have he : leftEnds₂ ([] : List (Letter Unit)) [] = [] := by
    change (List.range 0).filter _ = []
    rfl
  apply exists_decorates₂_of_bounded_points
  · intro j hj
    simp [he] at hj
  · intro j hj
    simp [he] at hj

/-- With no matching moves, height zero is both the lower and upper boundary. -/
theorem identity_boundary :
    ∃ ds : List (DTMove Unit),
      Decorates₂ [(true, ())] [] (fun _ => (0, 0))
        (strandCounts fun _ : MatchingStrand [(true, ())] [] => 3) ds ∧
      DOk₂ [(true, ())] ds := by
  apply exists_decorates₂_of_bounded_points
  · intro j hj
    have hm : IsMatching₂ (List.ofFn fun _ : Fin 1 => (true, ()))
        (List.ofFn fun _ : Fin 1 => (true, ())) [] := ⟨trivial, rfl⟩
    have hj' : j < 1 := (positive_mem_leftEnds₂ (fun _ : Fin 1 => ())
      (fun _ : Fin 1 => ()) hm j).mp hj
    have : j = 0 := by omega
    subst j
    unfold OnStrand₂
    decide
  · intro j _
    exact Nat.zero_le _

end OddMath.SKM.BoundedPointSerializationExamples
