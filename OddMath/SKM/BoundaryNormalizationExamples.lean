import OddMath.SKM.BoundaryNormalization
import OddMath.SKM.MixedCrossingLocalExamples

/-! Distinct odd colours, both intersection cases, and finite dot labels. -/
namespace OddMath.SKM.BoundaryNormalizationExamples
open StringDiagrams StringDiagrams.Chord DTMove
open MixedCrossingLocalExamples

private theorem pairing_iso : Iso (pairing₂ B S) (swapAt (pairing₂ A R) 2) := by
  convert iso_map_of_injOn (swapAt (pairing₂ A R) 2) (Equiv.swap 4 6)
    (by intro x _ y _ h; exact (Equiv.swap 4 6).injective h) using 1
  decide

/-- The original source really has the existing intersection. -/
theorem existing_intersection : Ilv (pairing₂ A R) 2 := by
  refine ⟨0, 1, 2, 3, ?_, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  exact ⟨by decide, by decide, by decide,
    by unfold Same idAt; decide, by unfold Same idAt; decide⟩

/-- Invoke the new normalization theorem on the old nonminimal-attachment example. -/
theorem existing_intersection_normalized :
    tableDegree oddDatum oddSymmetrizer 0 (tLay B S) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay A R) ∧
    xpar oddDatum 0 (tLay B S) = xpar oddDatum 0 (tLay A R) + 1 := by
  exact reduced₂_opposite_boundary_degree_parity oddDatum oddSymmetrizer 0 []
    [(false, false), (true, true)] false true colours_distinct source_matching
    source_reduced.1 target_matching target_reduced.1 pairing_iso

private def A₀ : List (Letter Bool) :=
  [(true, false), (false, true), (true, true), (false, false)]
private def B₀ : List (Letter Bool) :=
  [(false, true), (true, false), (true, true), (false, false)]
private def R₀ : List (TMove (Letter Bool)) := [.cap 1, .cap 0]
private def S₀ : List (TMove (Letter Bool)) := [.mv (.cross 0), .cap 1, .cap 0]

private theorem matching₀ : IsMatching₂ A₀ [] R₀ := by
  refine ⟨?_, rfl⟩
  refine ⟨⟨(4, (false, true)), (2, (true, true)), rfl, rfl, rfl, by decide⟩, ?_⟩
  exact ⟨⟨(6, (true, false)), (0, (false, false)), rfl, rfl, rfl, by decide⟩, trivial⟩

private theorem matching₁ : IsMatching₂ B₀ [] S₀ := by
  refine ⟨⟨by change 5 < 8; decide, ?_⟩, rfl⟩
  refine ⟨⟨(6, (false, true)), (2, (true, true)), rfl, rfl, rfl, by decide⟩, ?_⟩
  exact ⟨⟨(4, (true, false)), (0, (false, false)), rfl, rfl, rfl, by decide⟩, trivial⟩

private theorem reduced₀ : Reduced₂ A₀ R₀ := by
  change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
  simp

private theorem reduced₁ : Reduced₂ B₀ S₀ := by
  change ([s(6, 4)] : List (Sym2 ℕ)).Nodup ∧
    ∀ z ∈ ([s(6, 4)] : List (Sym2 ℕ)), ¬ z.IsDiag
  simp

private theorem pairing_iso₀ : Iso (pairing₂ B₀ S₀) (swapAt (pairing₂ A₀ R₀) 2) := by
  convert iso_map_of_injOn (swapAt (pairing₂ A₀ R₀) 2) (Equiv.swap 4 6)
    (by intro x _ y _ h; exact (Equiv.swap 4 6).injective h) using 1
  decide

/-- The second source has no existing intersection. -/
theorem no_existing_intersection : ¬ Ilv (pairing₂ A₀ R₀) 2 := by
  rintro ⟨i, j, k, l, ⟨hij, hjk, hkl, hik, hjl⟩, _⟩
  have hi := hik.lt_left
  have hj := hjl.lt_left
  have hk := hik.lt_right
  have hl := hjl.lt_right
  change i < 4 at hi
  change j < 4 at hj
  change k < 4 at hk
  change l < 4 at hl
  have ei : i = 0 := by omega
  have ej : j = 1 := by omega
  have ek : k = 2 := by omega
  subst i j k
  exact (by unfold Same idAt; decide : ¬ Same (pairing₂ A₀ R₀) 0 2) hik

/-- Invoke the same theorem with a source having no intersection. -/
theorem no_intersection_normalized :
    tableDegree oddDatum oddSymmetrizer 0 (tLay B₀ S₀) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay A₀ R₀) ∧
    xpar oddDatum 0 (tLay B₀ S₀) = xpar oddDatum 0 (tLay A₀ R₀) + 1 := by
  exact reduced₂_opposite_boundary_degree_parity oddDatum oddSymmetrizer 0 []
    [(true, true), (false, false)] false true colours_distinct matching₀
    reduced₀ matching₁ reduced₁ pairing_iso₀

private theorem endsR : leftEnds₂ A R = [0, 1] := by
  classical
  change (List.range 4).filter (fun j => decide (IsLeftEnd
    [(4, (false, true)), (6, (true, false)), (4, (true, true)), (6, (false, false))] j)) = [0, 1]
  norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
  exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

private theorem endsS : leftEnds₂ B S = [0, 1] := by
  classical
  change (List.range 4).filter (fun j => decide (IsLeftEnd
    [(6, (false, true)), (4, (true, false)), (4, (false, false)), (6, (true, true))] j)) = [0, 1]
  norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
  exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩

private def qR (j : ℕ) : ℕ × ℕ := (1, if j = 1 then 1 else 0)
private def qS (j : ℕ) : ℕ × ℕ := (0, if j = 1 then 1 else 0)
private def cR (j : MatchingStrand A R) : ℕ := if j.val = 1 then 1 else 0
private def cS (j : MatchingStrand B S) : ℕ := if j.val = 1 then 1 else 0

private theorem pointsR : ∀ j ∈ leftEnds₂ A R,
    (qR j).1 ≤ R.length ∧ OnStrand₂ A R j (qR j) := by
  intro j hj
  simp only [endsR, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> unfold OnStrand₂ <;> decide

private theorem pointsS : ∀ j ∈ leftEnds₂ B S,
    (qS j).1 ≤ S.length ∧ OnStrand₂ B S j (qS j) := by
  intro j hj
  simp only [endsS, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> unfold OnStrand₂ <;> decide

/-- The previous nonzero dot lists are genuine finite-strand decorations. -/
theorem finite_dot_decorations :
    Decorates₂ A R qR (strandCounts cR) sourceDots ∧
    Decorates₂ B S qS (strandCounts cS) targetDots := by
  constructor
  · refine ⟨rfl, ?_⟩
    simp [sourceDots, targetDots, dotPts, endsR, strandCounts, cR, qR]
  · refine ⟨rfl, ?_⟩
    simp [targetDots, dotPts, endsS, strandCounts, cS, qS]

/-- Finite labels and valid distinguished points feed the library dot formula;
the normalized existing-intersection pair has degree 5 and parity shift 1. -/
theorem finite_dotted_normalization :
    (∀ j ∈ leftEnds₂ A R, (qR j).1 ≤ R.length ∧ OnStrand₂ A R j (qR j)) ∧
    (∀ j ∈ leftEnds₂ B S, (qS j).1 ≤ S.length ∧ OnStrand₂ B S j (qS j)) ∧
    Decorates₂ A R qR (strandCounts cR) sourceDots ∧
    Decorates₂ B S qS (strandCounts cS) targetDots ∧
    tableDegree oddDatum oddSymmetrizer 0 (dLay B targetDots) = 5 ∧
    tableDegree oddDatum oddSymmetrizer 0 (dLay A sourceDots) = 5 ∧
    xpar oddDatum 0 (dLay B targetDots) = 0 ∧
    xpar oddDatum 0 (dLay A sourceDots) = 1 := by
  refine ⟨pointsR, pointsS, finite_dot_decorations.1, finite_dot_decorations.2,
    dot_values.1, rightward_dot_transport.1.trans dot_values.1, dot_values.2, ?_⟩
  rw [rightward_dot_transport.2, dot_values.2, zero_add]

/-- The source finite decoration obeys the pointwise dot formula relative
to the normalized target base, whose grading is proved above. -/
theorem finite_dot_formula :
    tableDegree oddDatum oddSymmetrizer 0 (dLay A sourceDots) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay B S) +
        ∑ j : MatchingStrand A R, (cR j : ℤ) * (2 * oddSymmetrizer.d (matchingStrandColour A R j)) ∧
    xpar oddDatum 0 (dLay A sourceDots) = xpar oddDatum 0 (tLay B S) + 1 +
        ∑ j : MatchingStrand A R, (cR j : ZMod 2) * oddDatum.parity (matchingStrandColour A R j) := by
  obtain ⟨hd, hp⟩ := mixed_decorated_degree_parity oddDatum oddSymmetrizer 0
    source_matching qR (fun j hj => (pointsR j hj).2) cR sourceDots finite_dot_decorations.1
  rw [← existing_intersection_normalized.1] at hd
  have hbase : xpar oddDatum 0 (tLay A R) = xpar oddDatum 0 (tLay B S) + 1 := by
    rw [existing_intersection_normalized.2, add_assoc,
      show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]
  rw [hbase] at hp
  exact ⟨hd, hp⟩

end OddMath.SKM.BoundaryNormalizationExamples
