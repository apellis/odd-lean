import OddMath.Frontier.OddLRVerticalPieri
import OddMath.Frontier.OddLRElimination

/-! PRE-production controls (Ellis 1111.3932v1, (3.10), Thm 3.8).

Compiled BEFORE `OddLRThm38`; nothing here mentions a production declaration.  These pin the
two indexing conventions that the production bridge identifies, on an exact fixture:

* both transcriptions of |i/λ| are ZERO-indexed in the same way (paper row i = a+1,
  |i/λ| = boxes of λ strictly below 0-indexed row a): on λ = (1,1) the values at rows 0,1,2 are
  1,0,0 for the vertical-Pieri `belowCount` and for the elimination's `belowRows`;
* an off-by-one transcription (`belowRows λ (a+1)`) is DISTINGUISHED by the fixture (row 0
  gives 0 ≠ 1), so the production identity `belowCount = belowRows` is not vacuous;
* the two one-column diagrams have the same row/column lengths on the fixture.
-/
namespace OddMath.Frontier.OddLRThm38Controls
open scoped BigOperators
open OddLRVerticalPieri (column belowCount)
open OddLRElimination (belowRows)
noncomputable section

theorem belowRows_col2_0 : belowRows (column 2) 0 = 1 := by
  unfold OddLRElimination.belowRows
  rw [OddLRVerticalPieri.column_colLen]
  simp [Finset.sum_range_succ, OddLRVerticalPieri.column_rowLen 2 1 (by omega)]

theorem belowRows_col2_1 : belowRows (column 2) 1 = 0 := by
  unfold OddLRElimination.belowRows
  rw [OddLRVerticalPieri.column_colLen]
  simp [Finset.sum_range_succ]

theorem belowRows_col2_2 : belowRows (column 2) 2 = 0 := by
  unfold OddLRElimination.belowRows
  rw [OddLRVerticalPieri.column_colLen]
  simp [Finset.sum_range_succ]

theorem cells_col2 : (column 2).cells = {(0, 0), (1, 0)} := by
  ext ⟨a, b⟩
  rw [YoungDiagram.mem_cells, OddLRVerticalPieri.mem_column]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

theorem belowCount_col2_0 : belowCount (column 2) 0 = 1 := by
  unfold OddLRVerticalPieri.belowCount
  rw [cells_col2, Finset.card_eq_one]
  exact ⟨(1, 0), by ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]; omega⟩

theorem belowCount_col2_1 : belowCount (column 2) 1 = 0 := by
  unfold OddLRVerticalPieri.belowCount
  rw [cells_col2, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> simp

theorem belowCount_col2_2 : belowCount (column 2) 2 = 0 := by
  unfold OddLRVerticalPieri.belowCount
  rw [cells_col2, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> simp

/-- Negative control: the off-by-one transcription differs from `belowCount` on the fixture. -/
theorem offByOne_distinguished : belowRows (column 2) (0 + 1) ≠ belowCount (column 2) 0 := by
  rw [zero_add, belowRows_col2_1, belowCount_col2_0]
  omega

/-- The literal (1^k) of `TableauExtremal` has the fixture's cells. -/
theorem columnShape_cells_2 : (TableauExtremal.columnShape 2).cells = {(0, 0), (1, 0)} := by
  ext ⟨a, b⟩
  rw [YoungDiagram.mem_cells, TableauExtremal.mem_columnShape]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

end
end OddMath.Frontier.OddLRThm38Controls
