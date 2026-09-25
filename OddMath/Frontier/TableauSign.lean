import Mathlib.Combinatorics.Young.SemistandardTableau
import OddMath.LrLegA

/-!
# Genuine semistandard tableaux discharge the Leg A sign hypothesis

Ellis, arXiv:1111.3932v1, §2.1 (positive alphabet, weak rows, strict
columns), §2.2 (English box directions), and Theorem 3.8, first sign
comparison in the proof, PDF p.11. This proves the combinatorial sign
premise, not the full equality of Schur functions.

The shape is Mathlib's finite lower set `YoungDiagram`; semistandardness
is Mathlib's existing row/column predicate plus positivity on the shape.
`boxes` enumerates each actual cell once. Its order is irrelevant to these
all-pairs counts and is NOT a choice of tableau reading word.
-/

namespace OddMath.Frontier.TableauSign

open LrLegA

/-- Ellis's positive-alphabet semistandard tableaux on an English shape. -/
structure PositiveTableau (μ : YoungDiagram) extends SemistandardYoungTableau μ where
  positive : ∀ {i j}, (i, j) ∈ μ → 0 < entry i j

variable {μ : YoungDiagram}

/-- Convert a coordinate to the existing Leg A box representation. -/
def box (T : PositiveTableau μ) (c : ℕ × ℕ) : TBox :=
  ⟨c.1, c.2, T.entry c.1 c.2⟩

/-- All actual cells, once each; no reading order is imposed. -/
noncomputable def boxes (T : PositiveTableau μ) : Tableau :=
  μ.cells.toList.map (box T)

/-- Exact membership, including both shape and the actual entry. -/
theorem mem_boxes (T : PositiveTableau μ) (B : TBox) :
    B ∈ boxes T ↔ (B.row, B.col) ∈ μ ∧ B.entry = T.entry B.row B.col := by
  simp only [boxes, List.mem_map, Finset.mem_toList, YoungDiagram.mem_cells]
  constructor
  · rintro ⟨⟨i, j⟩, hc, rfl⟩
    exact ⟨hc, rfl⟩
  · rintro ⟨hc, he⟩
    refine ⟨(B.row, B.col), hc, ?_⟩
    cases B
    simp_all [box]

/-- Coordinate projection returns exactly the finite shape enumeration. -/
theorem boxes_coordinates (T : PositiveTableau μ) :
    (boxes T).map (fun B => (B.row, B.col)) = μ.cells.toList := by
  simp [boxes, box, List.map_map, Function.comp_def]

/-- No coordinate is repeated: the sum cannot silently overcount boxes. -/
theorem boxes_coordinates_nodup (T : PositiveTableau μ) :
    ((boxes T).map (fun B => (B.row, B.col))).Nodup := by
  rw [boxes_coordinates]
  exact μ.cells.nodup_toList

/-- The enumeration has exactly the shape's cardinality. -/
theorem boxes_length (T : PositiveTableau μ) : (boxes T).length = μ.card := by
  simp [boxes, YoungDiagram.card]

/-- Entries of actual boxes belong to the positive alphabet. -/
theorem boxes_positive (T : PositiveTableau μ) {B : TBox} (hB : B ∈ boxes T) :
    0 < B.entry := by
  obtain ⟨hc, he⟩ := (mem_boxes T B).mp hB
  rw [he]
  exact T.positive hc

/-- A north-but-not-east cell has smaller entry. The intermediate cell
`(i₁,j₂)` exists by Ferrers closure; row weakness and column strictness
supply the two comparisons. No diagonal comparison is assumed. -/
theorem north_not_east_lt (T : PositiveTableau μ)
    {i₁ i₂ j₁ j₂ : ℕ} (hB : (i₂, j₂) ∈ μ)
    (hN : i₁ < i₂) (hNotE : j₁ ≤ j₂) :
    T.entry i₁ j₁ < T.entry i₂ j₂ := by
  have hC : (i₁, j₂) ∈ μ := μ.up_left_mem (Nat.le_of_lt hN) le_rfl hB
  exact lt_of_le_of_lt (T.toSemistandardYoungTableau.row_weak_of_le hNotE hC)
    (T.toSemistandardYoungTableau.col_strict hN hB)

/-- The exact Boolean premise consumed by the inherited Leg A lemmas. -/
theorem legA_hypothesis (T : PositiveTableau μ) :
    ∀ B ∈ boxes T, ∀ A ∈ boxes T,
      isNorth A B = true → isEast A B = false → isLtEntry A B = true := by
  intro B hB A hA hN hE
  obtain ⟨hBc, hBe⟩ := (mem_boxes T B).mp hB
  obtain ⟨_, hAe⟩ := (mem_boxes T A).mp hA
  simp only [isNorth, decide_eq_true_eq] at hN
  simp only [isEast, decide_eq_false_iff_not] at hE
  have h := north_not_east_lt T hBc hN (Nat.le_of_not_gt hE)
  simpa only [isLtEntry, decide_eq_true_eq, hAe, hBe] using h

/-- Exact per-box even-exponent difference on a genuine tableau. -/
theorem perBox (T : PositiveTableau μ) (B : TBox) (hB : B ∈ boxes T) :
    countNorth (boxes T) B + countNorthLt (boxes T) B =
      countNE (boxes T) B + countNELt (boxes T) B + 2 * countRest (boxes T) B :=
  LrLegA.perBox (boxes T) B (legA_hypothesis T B hB)

/-- Global exact exponent difference, not just a parity assertion. -/
theorem global (T : PositiveTableau μ) :
    totalNorth (boxes T) (boxes T) + totalNorthLt (boxes T) (boxes T) =
      totalNE (boxes T) (boxes T) + totalNELt (boxes T) (boxes T) +
        2 * totalRest (boxes T) (boxes T) :=
  LrLegA.global (boxes T) (boxes T) (legA_hypothesis T)

/-- Ellis's Leg A sign identity for every positive semistandard tableau
of every Young shape, with no residual per-box hypothesis. -/
theorem global_sign (T : PositiveTableau μ) :
    signLeft (boxes T) (boxes T) = signRight (boxes T) (boxes T) :=
  LrLegA.global_sign (boxes T) (boxes T) (legA_hypothesis T)

end OddMath.Frontier.TableauSign
