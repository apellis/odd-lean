import OddMath.SKM.MixedDotGrading

/-! Nonempty mixed consumer: an internal cup and cap rename the fresh ID 2 to 0.
The dot lies on the downward leg of the new cup, below the cap. -/
namespace OddMath.SKM.MixedDotGradingExamples
open StringDiagrams StringDiagrams.Chord DTMove
open scoped BigOperators

private def A {I : Type*} (i : I) : List (Letter I) := [(true, i)]
private def R {I : Type*} (i : I) : List (TMove (Letter I)) :=
  [.mv (.cup 1 (false, i)), .cap 0]
private def ds {I : Type*} (i : I) : List (DTMove I) :=
  [.tm (.mv (.cup 1 (false, i))), .dt 1, .tm (.cap 0)]
private def q (_ : ℕ) : ℕ × ℕ := (1, 1)

private theorem matching {I : Type*} (i : I) : IsMatching₂ (A i) (A i) (R i) := by
  constructor
  · refine ⟨by change 2 ≤ 2; decide, ?_⟩
    refine ⟨?_, trivial⟩
    exact ⟨(0, (true, i)), (2, (false, i)), rfl, rfl, rfl, by change (0 : ℕ) ≠ 2; decide⟩
  · rfl

private theorem ends {I : Type*} (i : I) : leftEnds₂ (A i) (R i) = [0] := by
  have h (j : ℕ) : IsLeftEnd (pairing₂ (A i) (R i)) j ↔ j = 0 := by
    change (j < 2 ∧ ¬ ∃ k, k < j ∧ Same [(0, (false, i)), (0, (true, i))] j k) ↔ j = 0
    constructor
    · intro h
      have hj := h.1
      interval_cases j
      · rfl
      · exact (h.2 ⟨0, by decide, by simp [Same, idAt]⟩).elim
    · rintro rfl
      exact ⟨by decide, by simp⟩
  unfold leftEnds₂
  simp only [show (pairing₂ (A i) (R i)).length = 2 from rfl, h]
  decide

private theorem points {I : Type*} (i : I) :
    ∀ j ∈ leftEnds₂ (A i) (R i), (q j).1 ≤ (R i).length ∧
      OnStrand₂ (A i) (R i) j (q j) := by
  intro j hj
  rw [ends] at hj
  have : j = 0 := by simpa using hj
  subst j
  change 1 ≤ 2 ∧ 1 < 3 ∧ 0 = 0
  decide

private theorem decoration {I : Type*} (i : I) :
    Decorates₂ (A i) (R i) q (strandCounts fun _ : MatchingStrand (A i) (R i) => 1) (ds i) := by
  constructor
  · rfl
  · simp only [ds, dotPts, ends, List.flatMap_cons, List.flatMap_nil, strandCounts]
    simp [q]

/-- The tracked dot begins with fresh ID 2, and the cap genuinely renames it to 0. -/
theorem internal_cup_cap_renaming {I : Type*} (i : I) :
    let T := tRun flipL (A i).length (tStart (A i)) ((R i).take 1)
    idD T.st ((A i).length + 1) = 2 ∧
      tRen (A i).length T ((R i).drop 1) 2 = 0 := by
  exact ⟨rfl, rfl⟩

/-- The general bridge computes a downward dot inside a nonempty cup-cap zigzag. -/
theorem internal_cup_cap_dot {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (i : I) :
    tableDegree D sy μ (dLay (A i) (ds i)) = 2 * sy.d i ∧
      xpar D μ (dLay (A i) (ds i)) = D.parity i := by
  classical
  obtain ⟨hd, hp⟩ := mixed_decorated_degree_parity D sy μ (matching i) q
    (fun j hj => (points i j hj).2) (fun _ => 1) (ds i) (decoration i)
  let j₀ : MatchingStrand (A i) (R i) := ⟨0, by rw [ends]; simp⟩
  have hj (j : MatchingStrand (A i) (R i)) : j = j₀ := by
    apply Subtype.ext
    have h := j.property
    simpa only [ends, List.mem_singleton] using h
  have hsum {M : Type} [AddCommMonoid M] (f : MatchingStrand (A i) (R i) → M) :
      ∑ j, f j = f j₀ := by
    apply Finset.sum_eq_single j₀
    · intro j _ hne
      exact (hne (hj j)).elim
    · simp
  have hc : matchingStrandColour (A i) (R i) j₀ = i := rfl
  rw [hsum, hc] at hd hp
  have hbase : tableDegree D sy μ (tLay (A i) (R i)) = 0 := by
    simp [A, R, tLay, tmLay, moveLay, tLet, chStep, lstep, insAt, flipL, xCupL, xCapL, xwhL,
      tableDegree, gdeg, wt, sh, D.cd.coroot_root_self]
    ring
  have hpbase : xpar D μ (tLay (A i) (R i)) = 0 := by
    simp [A, R, tLay, tmLay, moveLay, tLet, chStep, lstep, insAt, flipL, xCupL, xCapL, xwhL,
      xpar, xlpar, Shape.parity]
  constructor
  · simpa [hbase] using hd
  · simpa [hpbase] using hp

end OddMath.SKM.MixedDotGradingExamples
