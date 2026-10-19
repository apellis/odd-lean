/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.BoundaryExchange
import OddMath.SKM.MixedCrossingLocalExamples

/-! Populated equal odd-colour fixtures for the two non-cap classes of
Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.3 Claim 5. -/
namespace OddMath.SKM.BoundaryExchangeExamples
open StringDiagrams StringDiagrams.Chord DTMove
open MixedCrossingLocalExamples (oddDatum oddSymmetrizer)

def A : List (Letter Bool) := [(true, false), (false, false), (false, false), (true, false)]
def B : List (Letter Bool) := [(false, false), (true, false), (false, false), (true, false)]
def S : List (TMove (Letter Bool)) := [.cap 1, .cap 0]
def R : List (TMove (Letter Bool)) := [.mv (.cross 0), .cap 1, .cap 0]


theorem source_matching : IsMatching₂ A [] R := by
  refine ⟨⟨by change 5 < 8; decide, ?_⟩, rfl⟩
  refine ⟨⟨(6, (true, false)), (2, (false, false)), rfl, rfl, rfl, by decide⟩, ?_⟩
  exact ⟨⟨(4, (false, false)), (0, (true, false)), rfl, rfl, rfl, by decide⟩, trivial⟩

theorem target_matching : IsMatching₂ B [] S := by
  refine ⟨?_, rfl⟩
  refine ⟨⟨(4, (true, false)), (2, (false, false)), rfl, rfl, rfl, by decide⟩, ?_⟩
  exact ⟨⟨(6, (false, false)), (0, (true, false)), rfl, rfl, rfl, by decide⟩, trivial⟩

theorem source_reduced : StrictReduced₂ A R := by
  change (([s(6, 4)] : List (Sym2 ℕ)).Nodup ∧
    (∀ z ∈ ([s(6, 4)] : List (Sym2 ℕ)), ¬ z.IsDiag)) ∧ ([6, 4] : List ℕ).Nodup
  simp

theorem target_reduced : StrictReduced₂ B S := by
  change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
    ([4, 6] : List ℕ).Nodup
  simp

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
  exact reduced₂_opposite_boundary_degree_parity_of_not_same oddDatum oddSymmetrizer 0 []
    [(false, false), (true, false)] false false source_matching
    source_reduced.1 target_matching target_reduced.1
    (Ilv.not_same source_matching.pairing_properties.1 existing_intersection) pairing_iso

def A₀ : List (Letter Bool) :=
  [(true, false), (false, false), (true, false), (false, false)]
def B₀ : List (Letter Bool) :=
  [(false, false), (true, false), (true, false), (false, false)]
def R₀ : List (TMove (Letter Bool)) := [.cap 1, .cap 0]
def S₀ : List (TMove (Letter Bool)) := [.mv (.cross 0), .cap 1, .cap 0]

theorem matching₀ : IsMatching₂ A₀ [] R₀ := by
  refine ⟨?_, rfl⟩
  refine ⟨⟨(4, (false, false)), (2, (true, false)), rfl, rfl, rfl, by decide⟩, ?_⟩
  exact ⟨⟨(6, (true, false)), (0, (false, false)), rfl, rfl, rfl, by decide⟩, trivial⟩

theorem matching₁ : IsMatching₂ B₀ [] S₀ := by
  refine ⟨⟨by change 5 < 8; decide, ?_⟩, rfl⟩
  refine ⟨⟨(6, (false, false)), (2, (true, false)), rfl, rfl, rfl, by decide⟩, ?_⟩
  exact ⟨⟨(4, (true, false)), (0, (false, false)), rfl, rfl, rfl, by decide⟩, trivial⟩

theorem reduced₀ : StrictReduced₂ A₀ R₀ := by
  change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
    ([4, 6] : List ℕ).Nodup
  simp

theorem reduced₁ : StrictReduced₂ B₀ S₀ := by
  change (([s(6, 4)] : List (Sym2 ℕ)).Nodup ∧
    ∀ z ∈ ([s(6, 4)] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧ ([6, 4] : List ℕ).Nodup
  simp

theorem pairing_iso₀ : Iso (pairing₂ B₀ S₀) (swapAt (pairing₂ A₀ R₀) 2) := by
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
  exact reduced₂_same_colour_boundary_degree_parity oddDatum oddSymmetrizer 0 []
    [(true, false), (false, false)] false matching₀
    reduced₀.1 matching₁ reduced₁.1 (by unfold Same idAt; decide) pairing_iso₀

def targetDots : List (DTMove Bool) := [.dt 1, .tm (.cap 1), .tm (.cap 0)]
def sourceDots : List (DTMove Bool) := .tm (.mv (.cross 0)) :: targetDots

theorem rightward_dot_transport :
    tableDegree oddDatum oddSymmetrizer 0 (dLay A sourceDots) =
      tableDegree oddDatum oddSymmetrizer 0 (dLay B targetDots) ∧
    xpar oddDatum 0 (dLay A sourceDots) = xpar oddDatum 0 (dLay B targetDots) + 1 := by
  simpa only [A, B, sourceDots, List.nil_append, List.length_nil, oddDatum, one_mul] using
    right_cross_attach_degree_parity oddDatum oddSymmetrizer 0 []
      [(false, false), (true, false)] false false targetDots

private theorem endsR : leftEnds₂ A R = [0, 1] := by
  classical
  change (List.range 4).filter (fun j => decide (IsLeftEnd
    [(4, (false, false)), (6, (true, false)), (4, (true, false)), (6, (false, false))] j)) = [0, 1]
  norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
  exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

private theorem endsS : leftEnds₂ B S = [0, 1] := by
  classical
  change (List.range 4).filter (fun j => decide (IsLeftEnd
    [(6, (false, false)), (4, (true, false)), (4, (false, false)), (6, (true, false))] j)) = [0, 1]
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

/-- The source finite decoration obeys the pointwise dot formula relative
to the normalized target base, whose grading is proved above. -/
theorem finite_dot_formula :
    tableDegree oddDatum oddSymmetrizer 0 (dLay A sourceDots) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay B S) +
        ∑ j : MatchingStrand A R, (cR j : ℤ) * (2 * oddSymmetrizer.d (matchingStrandColour A R j)) ∧
    xpar oddDatum 0 (dLay A sourceDots) = xpar oddDatum 0 (tLay B S) + 1 +
        ∑ j : MatchingStrand A R,
          (cR j : ZMod 2) * oddDatum.parity (matchingStrandColour A R j) := by
  obtain ⟨hd, hp⟩ := mixed_decorated_degree_parity oddDatum oddSymmetrizer 0
    source_matching qR (fun j hj => (pointsR j hj).2) cR sourceDots finite_dot_decorations.1
  rw [← existing_intersection_normalized.1] at hd
  have hbase : xpar oddDatum 0 (tLay A R) = xpar oddDatum 0 (tLay B S) + 1 := by
    rw [existing_intersection_normalized.2, add_assoc,
      show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]
  rw [hbase] at hp
  exact ⟨hd, hp⟩

/-- Every distinguished colour is the same odd colour, not an unequal-colour fixture. -/
theorem equal_odd_colour : oddDatum.parity false = 1 := rfl

/-- The source and target lists contain the dot constructor. -/
theorem nonzero_dot_counts :
    sourceDots = [.tm (.mv (.cross 0)), .dt 1, .tm (.cap 1), .tm (.cap 0)] ∧
    targetDots = [.dt 1, .tm (.cap 1), .tm (.cap 0)] := ⟨rfl, rfl⟩

/-- A nonzero dot on the nonintersecting source and its intersecting target. -/
def sourceDots₀ : List (DTMove Bool) := [.dt 1, .tm (.cap 1), .tm (.cap 0)]
def targetDots₀ : List (DTMove Bool) := .tm (.mv (.cross 0)) :: sourceDots₀

private theorem endsR₀ : leftEnds₂ A₀ R₀ = [0, 1] := by
  classical
  change (List.range 4).filter (fun j => decide (IsLeftEnd
    [(6, (true, false)), (4, (false, false)), (4, (true, false)), (6, (false, false))] j)) = [0, 1]
  norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
  exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩

private theorem endsS₀ : leftEnds₂ B₀ S₀ = [0, 1] := by
  classical
  change (List.range 4).filter (fun j => decide (IsLeftEnd
    [(4, (true, false)), (6, (false, false)), (4, (false, false)), (6, (true, false))] j)) = [0, 1]
  norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
  exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

private def qR₀ (j : ℕ) : ℕ × ℕ := (0, if j = 1 then 1 else 0)
private def qS₀ (j : ℕ) : ℕ × ℕ := (1, if j = 1 then 1 else 0)
private def cR₀ (j : MatchingStrand A₀ R₀) : ℕ := if j.val = 1 then 1 else 0
private def cS₀ (j : MatchingStrand B₀ S₀) : ℕ := if j.val = 1 then 1 else 0

private theorem pointsR₀ : ∀ j ∈ leftEnds₂ A₀ R₀,
    (qR₀ j).1 ≤ R₀.length ∧ OnStrand₂ A₀ R₀ j (qR₀ j) := by
  intro j hj
  simp only [endsR₀, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> unfold OnStrand₂ <;> decide

private theorem pointsS₀ : ∀ j ∈ leftEnds₂ B₀ S₀,
    (qS₀ j).1 ≤ S₀.length ∧ OnStrand₂ B₀ S₀ j (qS₀ j) := by
  intro j hj
  simp only [endsS₀, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> unfold OnStrand₂ <;> decide

/-- The previous nonzero dot lists are genuine finite-strand decorations. -/
theorem finite_dot_decorations₀ :
    Decorates₂ A₀ R₀ qR₀ (strandCounts cR₀) sourceDots₀ ∧
    Decorates₂ B₀ S₀ qS₀ (strandCounts cS₀) targetDots₀ := by
  constructor
  · refine ⟨rfl, ?_⟩
    simp [sourceDots₀, dotPts, endsR₀, strandCounts, cR₀, qR₀]
  · refine ⟨rfl, ?_⟩
    simp [targetDots₀, sourceDots₀, dotPts, endsS₀, strandCounts, cS₀, qS₀]

/-- The source finite decoration obeys the pointwise dot formula relative
to the normalized target base, whose grading is proved above. -/
theorem finite_dot_formula₀ :
    tableDegree oddDatum oddSymmetrizer 0 (dLay A₀ sourceDots₀) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay B₀ S₀) +
        ∑ j : MatchingStrand A₀ R₀,
          (cR₀ j : ℤ) * (2 * oddSymmetrizer.d (matchingStrandColour A₀ R₀ j)) ∧
    xpar oddDatum 0 (dLay A₀ sourceDots₀) = xpar oddDatum 0 (tLay B₀ S₀) + 1 +
        ∑ j : MatchingStrand A₀ R₀,
          (cR₀ j : ZMod 2) * oddDatum.parity (matchingStrandColour A₀ R₀ j) := by
  obtain ⟨hd, hp⟩ := mixed_decorated_degree_parity oddDatum oddSymmetrizer 0
    matching₀ qR₀ (fun j hj => (pointsR₀ j hj).2) cR₀ sourceDots₀ finite_dot_decorations₀.1
  rw [← no_intersection_normalized.1] at hd
  have hbase : xpar oddDatum 0 (tLay A₀ R₀) = xpar oddDatum 0 (tLay B₀ S₀) + 1 := by
    rw [no_intersection_normalized.2, add_assoc,
      show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]
  rw [hbase] at hp
  exact ⟨hd, hp⟩

theorem nonzero_dot_counts₀ :
    sourceDots₀ = [.dt 1, .tm (.cap 1), .tm (.cap 0)] ∧
    targetDots₀ = [.tm (.mv (.cross 0)), .dt 1, .tm (.cap 1), .tm (.cap 0)] := ⟨rfl, rfl⟩

end OddMath.SKM.BoundaryExchangeExamples
