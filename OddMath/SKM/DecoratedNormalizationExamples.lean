import OddMath.SKM.DecoratedNormalization
import OddMath.SKM.PositivePointGradingExamples

/-! Nonempty dot and cup-cap consumers for decorated numerical normalization. -/

namespace OddMath.SKM.DecoratedNormalizationExamples
open StringDiagrams StringDiagrams.Chord DTMove

private theorem ends_pair {I : Type*} {a : List (Letter I)}
    {R : List (TMove (Letter I))} (n : ℕ) (x y : Letter I)
    (he : pairing₂ a R = [(n, x), (n, y)]) : leftEnds₂ a R = [0] := by
  have h (j : ℕ) : IsLeftEnd (pairing₂ a R) j ↔ j = 0 := by
    rw [he]
    change (j < 2 ∧ ¬ ∃ k, k < j ∧ Same [(n, x), (n, y)] j k) ↔ j = 0
    constructor
    · intro h
      have hj := h.1
      interval_cases j
      · rfl
      · exact (h.2 ⟨0, by decide, by simp [Same, idAt]⟩).elim
    · rintro rfl
      exact ⟨by decide, by simp⟩
  have hlen : (pairing₂ a R).length = 2 := by rw [he]; rfl
  unfold leftEnds₂
  simp only [hlen, h]
  decide

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

private theorem ends {I : Type*} (i : I) : leftEnds₂ (A i) (R i) = [0] :=
  ends_pair 0 (false, i) (true, i) rfl

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

/-- This is a fresh strand ID, and the cap renames it before normalization. -/
theorem internal_cup_cap_renaming {I : Type*} (i : I) :
    let T := tRun flipL (A i).length (tStart (A i)) ((R i).take 1)
    idD T.st ((A i).length + 1) = 2 ∧
      tRen (A i).length T ((R i).drop 1) 2 = 0 := by
  exact ⟨rfl, rfl⟩

/-- Apply the headline across the cap zigzag with one downward dot on fresh ID 2;
the independently serialized normalized identity has an upward dot instead. -/
theorem internal_cup_cap_normalized_dot {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (i : I) :
    tableDegree D sy μ (dLay (A i) (ds i)) = 2 * sy.d i ∧
      xpar D μ (dLay (A i) (ds i)) = D.parity i := by
  have hr : Reduced₂ (A i) (R i) := by
    change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
    simp
  have hs : IsMatching₂ (A i) (A i) [] := ⟨trivial, rfl⟩
  have hrs : Reduced₂ (A i) [] := by
    change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
    simp
  have hi : Iso (pairing₂ (A i) (R i)) (pairing₂ (A i) []) := Iso.refl _
  have hends : leftEnds₂ (A i) [] = [0] := ends_pair 0 (false, i) (true, i) rfl
  have hpoints : ∀ j ∈ leftEnds₂ (A i) [], OnStrand₂ (A i) [] j (0, 0) := by
    intro j hj
    have : j = 0 := by simpa [hends] using hj
    subst j
    exact ⟨by change 0 < 1; decide, rfl⟩
  have hdec : Decorates₂ (A i) [] (fun _ => (0, 0))
      (strandCounts ((fun _ : MatchingStrand (A i) (R i) => 1) ∘
        (matchingStrandEquivOfIso hi).symm)) [.dt 0] := by
    constructor
    · rfl
    · simp [dotPts, hends, strandCounts]
  obtain ⟨hd, hp⟩ := mixed_decorated_degree_parity_of_iso D sy μ (matching i) hr hs hrs hi
    q (fun _ => (0, 0)) (fun j hj => (points i j hj).2) hpoints (fun _ => 1)
    (ds i) [.dt 0] (decoration i) hdec
  have hl : dLay (A i) [.dt 0] = xDotL (true, i) := by
    simp [A, dLay, dotOn, xDotL, xwhL]
  rw [hl, tableDegree_dot] at hd
  rw [hl, xpar_dot] at hp
  exact ⟨hd, hp⟩

/-- Right cup followed by cap normalizes to the downward identity, with one dot.
The points and serializers on the cap and identity are chosen separately. -/
theorem right_cup_cap_normalized_dot {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (i : I) :
    tableDegree D sy μ (dLay [(false, i)] [.dt 0]) =
      tableDegree D sy μ (dLay [(true, i), (false, i)] [.dt 1, .tm (.cap 0)]) +
        sy.d i * (1 + D.h i (wt D μ [(false, i)])) ∧
    xpar D μ (dLay [(false, i)] [.dt 0]) =
      xpar D μ (dLay [(true, i), (false, i)] [.dt 1, .tm (.cap 0)]) := by
  have hm : IsMatching₂ [(true, i), (false, i)] [] [.cap 0] := by
    constructor
    · refine ⟨?_, trivial⟩
      exact ⟨(2, (true, i)), (0, (false, i)), rfl, rfl, rfl, by change (2 : ℕ) ≠ 0; decide⟩
    · rfl
  have hr : Reduced₂ [(true, i), (false, i)] [.cap 0] := by
    change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
    simp
  have hs : IsMatching₂ [(false, i)] [(false, i)] [] := ⟨trivial, rfl⟩
  have hrs : Reduced₂ [(false, i)] [] := by
    change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
    simp
  have hi : Iso (pairing₂ [(true, i), (false, i)] [.cap 0])
      (pairing₂ [(false, i)] []) := by
    change Iso [(2, (true, i)), (2, (false, i))] [(0, (true, i)), (0, (false, i))]
    exact Chord.iso_map_of_injOn [(0, (true, i)), (0, (false, i))]
      (fun n => n + 2) (by intro x _ y _ h; omega)
  have heR : leftEnds₂ [(true, i), (false, i)] [.cap 0] = [0] :=
    ends_pair 2 (true, i) (false, i) rfl
  have heS : leftEnds₂ [(false, i)] [] = [0] := ends_pair 0 (true, i) (false, i) rfl
  have hq : ∀ j ∈ leftEnds₂ [(true, i), (false, i)] [.cap 0],
      (0, 1).1 ≤ ([.cap 0] : List (TMove (Letter I))).length ∧
      OnStrand₂ [(true, i), (false, i)] [.cap 0] j (0, 1) := by
    intro j hj
    have : j = 0 := by simpa [heR] using hj
    subst j
    exact ⟨by change 0 ≤ 1; decide, by change 1 < 2; decide, rfl⟩
  have hp : ∀ j ∈ leftEnds₂ [(false, i)] [], OnStrand₂ [(false, i)] [] j (0, 0) := by
    intro j hj
    have : j = 0 := by simpa [heS] using hj
    subst j
    exact ⟨by change 0 < 1; decide, rfl⟩
  have hd : Decorates₂ [(true, i), (false, i)] [.cap 0] (fun _ => (0, 1))
      (strandCounts fun _ : MatchingStrand [(true, i), (false, i)] [.cap 0] => 1)
      [.dt 1, .tm (.cap 0)] := by
    constructor
    · rfl
    · simp [dotPts, heR, strandCounts]
  have he : Decorates₂ [(false, i)] [] (fun _ => (0, 0))
      (strandCounts ((fun _ => 1) ∘ (matchingStrandEquivOfIso hi).symm)) [.dt 0] := by
    constructor
    · rfl
    · simp [dotPts, heS, strandCounts]
  exact cupAttach_normalized_decorated_degree_parity D sy μ hm hr hs hrs hi
    (fun _ => (0, 1)) (fun _ => (0, 0)) hq hp (fun _ => 1) _ _ hd he

/-- An odd root gives genuinely nonzero degree 2 and parity 1. -/
theorem odd_internal_cup_cap_normalized_dot :
    tableDegree PositivePointGradingExamples.twoColourDatum
      PositivePointGradingExamples.twoColourSymmetrizer 0 (dLay (A false) (ds false)) = 2 ∧
    xpar PositivePointGradingExamples.twoColourDatum 0 (dLay (A false) (ds false)) = 1 := by
  exact internal_cup_cap_normalized_dot PositivePointGradingExamples.twoColourDatum
    PositivePointGradingExamples.twoColourSymmetrizer 0 false

/-- The odd normalized cup consumer has degree 2 and parity 1, not zero values. -/
theorem odd_right_cup_cap_normalized_dot :
    tableDegree PositivePointGradingExamples.twoColourDatum
      PositivePointGradingExamples.twoColourSymmetrizer 0
        (dLay [(true, false), (false, false)] [.dt 1, .tm (.cap 0)]) +
      PositivePointGradingExamples.twoColourSymmetrizer.d false *
        (1 + PositivePointGradingExamples.twoColourDatum.h false
          (wt PositivePointGradingExamples.twoColourDatum 0 [(false, false)])) = 2 ∧
    xpar PositivePointGradingExamples.twoColourDatum 0
      (dLay [(true, false), (false, false)] [.dt 1, .tm (.cap 0)]) = 1 := by
  obtain ⟨hd, hp⟩ := right_cup_cap_normalized_dot
    PositivePointGradingExamples.twoColourDatum PositivePointGradingExamples.twoColourSymmetrizer
    0 false
  have hl : dLay [(false, false)] [.dt 0] = xDotL (false, false) := by
    simp [dLay, dotOn]
  rw [hl, tableDegree_dot] at hd
  rw [hl, xpar_dot] at hp
  exact ⟨hd.symm, hp.symm⟩

end OddMath.SKM.DecoratedNormalizationExamples
