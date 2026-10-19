import OddMath.SKM.PositiveMatchingDots

/-!
# Serializing bounded distinguished points

Supporting list constructions for the distinguished-point decorations of
[BE2, arXiv:1701.04133v2, §8] used in Theorem 10.3, Claim 1.
No matching, reducedness, or positivity hypothesis is needed for serialization.
-/

namespace OddMath.SKM
open StringDiagrams.Chord DTMove
variable {I : Type*}

private theorem exists_insert_dot (ds : List (DTMove I)) (h k : ℕ)
    (hh : h ≤ (tmoves ds).length) :
    ∃ es : List (DTMove I), tmoves es = tmoves ds ∧
      (dotPts es).Perm ((h, k) :: dotPts ds) := by
  induction ds generalizing h with
  | nil =>
    have : h = 0 := by simpa [tmoves] using hh
    subst h
    exact ⟨[.dt k], rfl, List.Perm.refl _⟩
  | cons d ds ih =>
    cases h with
    | zero => exact ⟨.dt k :: d :: ds, rfl, List.Perm.refl _⟩
    | succ h =>
      cases d with
      | tm m =>
        obtain ⟨es, he, hp⟩ := ih h (by simpa [tmoves] using hh)
        refine ⟨.tm m :: es, congrArg (m :: ·) he, ?_⟩
        exact hp.map (fun p => (p.1 + 1, p.2))
      | dt j =>
        obtain ⟨es, he, hp⟩ := ih (h + 1) hh
        refine ⟨.dt j :: es, he, ?_⟩
        exact (hp.cons (0, j)).trans (List.Perm.swap _ _ _)

/-- A finite list of points with bounded heights can be interleaved with the existing
matching moves, preserving the moves and all dot occurrences up to permutation. -/
theorem exists_tmoves_dotPts_perm (R : List (TMove (Letter I)))
    (P : List (ℕ × ℕ)) (hh : ∀ p ∈ P, p.1 ≤ R.length) :
    ∃ ds : List (DTMove I), tmoves ds = R ∧ (dotPts ds).Perm P := by
  induction P with
  | nil =>
    refine ⟨R.map .tm, tmoves_map_tm R, ?_⟩
    have hz : dotPts (R.map DTMove.tm) = [] := by
      induction R with
      | nil => rfl
      | cons m R ih => simp [dotPts, ih]
    rw [hz]
  | cons p P ih =>
    obtain ⟨ds, hd, hp⟩ := ih (fun q hq => hh q (List.mem_cons_of_mem _ hq))
    obtain ⟨es, he, heP⟩ := exists_insert_dot ds p.1 p.2 (by
      rw [hd]
      exact hh p List.mem_cons_self)
    exact ⟨es, he.trans hd, heP.trans (hp.cons p)⟩

/-- Any finite strand counts have a valid layered decoration at the chosen bounded
points. The bound excludes heights beyond the end of the matching move list. -/
theorem exists_decorates₂_of_bounded_points
    (A : List (Letter I)) (R : List (TMove (Letter I))) (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ A R, OnStrand₂ A R j (q j))
    (hh : ∀ j ∈ leftEnds₂ A R, (q j).1 ≤ R.length)
    (c : MatchingStrand A R → ℕ) :
    ∃ ds : List (DTMove I), Decorates₂ A R q (strandCounts c) ds ∧ DOk₂ A ds := by
  obtain ⟨ds, hd, hp⟩ := exists_tmoves_dotPts_perm R
    ((leftEnds₂ A R).flatMap fun j => List.replicate (strandCounts c j) (q j)) (by
      intro p hp
      obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
      rw [List.eq_of_mem_replicate hp]
      exact hh j hj)
  refine ⟨ds, ⟨hd, hp⟩, dOk₂_of_dotPts ds A ?_⟩
  intro p hp'
  obtain ⟨j, hj, hp'⟩ := List.mem_flatMap.mp (hp.subset hp')
  rw [List.eq_of_mem_replicate hp', hd]
  exact (hq j hj).1

end OddMath.SKM
