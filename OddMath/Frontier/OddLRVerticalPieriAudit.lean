import OddMath.Frontier.OddLRVerticalPieri
import OddMath.Frontier.OddLRVerticalPieriControls

/-! Audit (Ellis 1111.3932v1 (3.10)).
Connects the preproduction control fixtures to the production vocabulary and prints the axioms
of every owned declaration (expected: at most propext, Classical.choice, Quot.sound). -/
namespace OddMath.Frontier.OddLRVerticalPieriAudit
open OddLRVerticalPieri OddLRVerticalPieriControls

/-- The production statistic is literally the control transcription of |i/λ|. -/
theorem belowCount_is_literal (lam : YoungDiagram) (r : ℕ) :
    belowCount lam r = belowLiteral lam r := rfl

/-- The production column is the control fixture (1^2). -/
theorem column_two : column 2 = shape11 := by
  apply YoungDiagram.ext
  decide

/-- Separating fixture in production vocabulary: (2,1)/(2) is a vertical 1-strip whose printed
exponent is 0, whereas the wrong column convention gives exponent 1 (controls). -/
theorem fixture_vertical : Vertical shape2 shape21 ∧ stripBelow shape2 shape21 = 0 := by
  unfold Vertical stripBelow belowCount
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide

/-- (1,1) + box in row 1 (zero-based 0): printed exponent 1. -/
theorem fixture_vertical_two : Vertical shape11 shape21 ∧ stripBelow shape11 shape21 = 1 := by
  unfold Vertical stripBelow belowCount
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide

/-- (2,2)/(2) is not a vertical strip: both new boxes lie in (zero-based) row 1. -/
theorem fixture_not_vertical :
    ¬ Vertical shape2 (YoungDiagram.ofRowLens [2,2] (by decide)) := by
  unfold Vertical
  decide

section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
/-- The main theorem, restated verbatim for the audit record. -/
theorem audit_vertical_pieri (n : ℕ) (lam : YoungDiagram) (k : ℕ) :
    letI := DegreeShapes.degreeFintype (lam.card + k)
    CompleteTableauExpansion.sp n lam * CompleteTableauExpansion.sp n (column k) =
      ∑ mu : DegreeShapes.DegreeShape (lam.card + k), if Vertical lam mu.val then
        (-1 : ℤ) ^ stripBelow lam mu.val • CompleteTableauExpansion.sp n mu.val
      else 0 :=
  vertical_pieri n lam k
end

#print axioms OddMath.Frontier.OddLRVerticalPieri.State
#print axioms OddMath.Frontier.OddLRVerticalPieri.Tab
#print axioms OddMath.Frontier.OddLRVerticalPieri.Vertical
#print axioms OddMath.Frontier.OddLRVerticalPieri.belowCount
#print axioms OddMath.Frontier.OddLRVerticalPieri.stripBelow
#print axioms OddMath.Frontier.OddLRVerticalPieri.histBelow
#print axioms OddMath.Frontier.OddLRVerticalPieri.column
#print axioms OddMath.Frontier.OddLRVerticalPieri.mem_column
#print axioms OddMath.Frontier.OddLRVerticalPieri.mem_column_cells
#print axioms OddMath.Frontier.OddLRVerticalPieri.column_colLen
#print axioms OddMath.Frontier.OddLRVerticalPieri.column_rowLen
#print axioms OddMath.Frontier.OddLRVerticalPieri.flatten_singletons
#print axioms OddMath.Frontier.OddLRVerticalPieri.column_word_labels
#print axioms OddMath.Frontier.OddLRVerticalPieri.column_entries_sorted
#print axioms OddMath.Frontier.OddLRVerticalPieri.column_word_decreasing
#print axioms OddMath.Frontier.OddLRVerticalPieri.column_word_length
#print axioms OddMath.Frontier.OddLRVerticalPieri.map_succ_injective
#print axioms OddMath.Frontier.OddLRVerticalPieri.column_ext
#print axioms OddMath.Frontier.OddLRVerticalPieri.columnEntry
#print axioms OddMath.Frontier.OddLRVerticalPieri.columnTableau
#print axioms OddMath.Frontier.OddLRVerticalPieri.columnTableau_bounded
#print axioms OddMath.Frontier.OddLRVerticalPieri.range_getD
#print axioms OddMath.Frontier.OddLRVerticalPieri.columnTableau_word
#print axioms OddMath.Frontier.OddLRVerticalPieri.column_directNorth
#print axioms OddMath.Frontier.OddLRVerticalPieri.sp_column
#print axioms OddMath.Frontier.OddLRVerticalPieri.run_rows
#print axioms OddMath.Frontier.OddLRVerticalPieri.rows_injective
#print axioms OddMath.Frontier.OddLRVerticalPieri.run_vertical
#print axioms OddMath.Frontier.OddLRVerticalPieri.run_card
#print axioms OddMath.Frontier.OddLRVerticalPieri.word_chain_of_rows
#print axioms OddMath.Frontier.OddLRVerticalPieri.word_decreasing_of_rows
#print axioms OddMath.Frontier.OddLRVerticalPieri.row_enumeration_unique
#print axioms OddMath.Frontier.OddLRVerticalPieri.strict_preimage_unique
#print axioms OddMath.Frontier.OddLRVerticalPieri.bottom_corner
#print axioms OddMath.Frontier.OddLRVerticalPieri.erase_vertical
#print axioms OddMath.Frontier.OddLRVerticalPieri.erase_difference
#print axioms OddMath.Frontier.OddLRVerticalPieri.vertical_peel_order
#print axioms OddMath.Frontier.OddLRVerticalPieri.decreasing_row_enumeration
#print axioms OddMath.Frontier.OddLRVerticalPieri.exists_vertical_peel
#print axioms OddMath.Frontier.OddLRVerticalPieri.vertical_exists
#print axioms OddMath.Frontier.OddLRVerticalPieri.VInputs
#print axioms OddMath.Frontier.OddLRVerticalPieri.VOutputs
#print axioms OddMath.Frontier.OddLRVerticalPieri.vForward
#print axioms OddMath.Frontier.OddLRVerticalPieri.vForward_bijective
#print axioms OddMath.Frontier.OddLRVerticalPieri.vInsertionEquiv
#print axioms OddMath.Frontier.OddLRVerticalPieri.no_southeast
#print axioms OddMath.Frontier.OddLRVerticalPieri.insert_northEast
#print axioms OddMath.Frontier.OddLRVerticalPieri.neg_one_pow_congr
#print axioms OddMath.Frontier.OddLRVerticalPieri.belowCount_insert
#print axioms OddMath.Frontier.OddLRVerticalPieri.run_parity
#print axioms OddMath.Frontier.OddLRVerticalPieri.run_polynomial
#print axioms OddMath.Frontier.OddLRVerticalPieri.run_histBelow
#print axioms OddMath.Frontier.OddLRVerticalPieri.inputMap
#print axioms OddMath.Frontier.OddLRVerticalPieri.inputMap_bijective
#print axioms OddMath.Frontier.OddLRVerticalPieri.inputEquiv
#print axioms OddMath.Frontier.OddLRVerticalPieri.Outer
#print axioms OddMath.Frontier.OddLRVerticalPieri.Indexed
#print axioms OddMath.Frontier.OddLRVerticalPieri.outputMap
#print axioms OddMath.Frontier.OddLRVerticalPieri.outputMap_bijective
#print axioms OddMath.Frontier.OddLRVerticalPieri.outputEquiv
#print axioms OddMath.Frontier.OddLRVerticalPieri.aggregateEquiv
#print axioms OddMath.Frontier.OddLRVerticalPieri.inputValue
#print axioms OddMath.Frontier.OddLRVerticalPieri.outputValue
#print axioms OddMath.Frontier.OddLRVerticalPieri.pointwise
#print axioms OddMath.Frontier.OddLRVerticalPieri.tableau_sum
#print axioms OddMath.Frontier.OddLRVerticalPieri.input_sum
#print axioms OddMath.Frontier.OddLRVerticalPieri.output_sum
#print axioms OddMath.Frontier.OddLRVerticalPieri.vertical_pieri
#print axioms OddMath.Frontier.OddLRVerticalPieriControls.belowLiteral
#print axioms OddMath.Frontier.OddLRVerticalPieriControls.rightLiteral
#print axioms OddMath.Frontier.OddLRVerticalPieriControls.shape2
#print axioms OddMath.Frontier.OddLRVerticalPieriControls.shape11
#print axioms OddMath.Frontier.OddLRVerticalPieriControls.shape21
#print axioms OddMath.Frontier.OddLRVerticalPieriControls.shape3
#print axioms OddMath.Frontier.OddLRVerticalPieriControls.separating_fixture
#print axioms OddMath.Frontier.OddLRVerticalPieriControls.agreeing_fixture
#print axioms OddMath.Frontier.OddLRVerticalPieriControls.separating_fixture_two
#print axioms OddMath.Frontier.OddLRVerticalPieriControls.column_prefactor
#print axioms OddMath.Frontier.OddLRVerticalPieriControls.signs_differ
#print axioms belowCount_is_literal
#print axioms column_two
#print axioms fixture_vertical
#print axioms fixture_vertical_two
#print axioms fixture_not_vertical
#print axioms audit_vertical_pieri
end OddMath.Frontier.OddLRVerticalPieriAudit
