import OddMath.Frontier.TableauStripSigns

/-! Preproduction controls for Ellis 1111.3932v1 (3.10).
Compiled BEFORE the production module and independent of it.

Source notation (Ellis Sec. 3.2, verbatim): "For a partition λ, let i/λ be the Young diagram
obtained by removing rows 1 through i from the diagram corresponding to λ.  Similarly, let λ/i,
i|λ, and λ|i be obtained by removing rows i through the bottom, columns 1 through i, and
columns i through the rightmost respectively."

English zero-based cells: a new box p = (p.1, p.2) sits in the 1-based row i = p.1 + 1, so
|i/λ| = #{q ∈ λ | p.1 < q.1} (printed statistic) whereas the wrong column convention
|j|λ| with j = p.2 + 1 is #{q ∈ λ | p.2 < q.2} (the (3.8) statistic).

The exact polynomial checks (n ≤ 3, |λ|+k ≤ 4, 104 cases, printed (3.10) holds in all, the
column-convention variant fails in 10) are exact-integer computations in
an unpublished script (receipts in an unpublished script); the model is validated there
against the existing `TableauHorizontalPieri.horizontal_pieri` (an unpublished script).
Here we kernel-check the literal combinatorial statistics on the fixture that separates them. -/
namespace OddMath.Frontier.OddLRVerticalPieriControls

/-- Printed |i/λ| for the 1-based row i = r + 1: boxes of λ strictly below row r (zero-based). -/
def belowLiteral (μ : YoungDiagram) (r : ℕ) : ℕ := (μ.cells.filter (fun q => r < q.1)).card
/-- Wrong (column) convention |j|λ| for the 1-based column j = c + 1. -/
def rightLiteral (μ : YoungDiagram) (c : ℕ) : ℕ := (μ.cells.filter (fun q => c < q.2)).card

def shape2 : YoungDiagram := YoungDiagram.ofRowLens [2] (by decide)
def shape11 : YoungDiagram := YoungDiagram.ofRowLens [1,1] (by decide)
def shape21 : YoungDiagram := YoungDiagram.ofRowLens [2,1] (by decide)
def shape3 : YoungDiagram := YoungDiagram.ofRowLens [3] (by decide)

/-- λ = (2), μ = (2,1): new box (1,0).  Printed exponent 0, column-variant exponent 1. -/
theorem separating_fixture :
    (1,0) ∈ shape21 ∧ (1,0) ∉ shape2 ∧ belowLiteral shape2 1 = 0 ∧ rightLiteral shape2 0 = 1 := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> decide

/-- λ = (2), μ = (3): new box (0,2). Both statistics vanish (agreement case). -/
theorem agreeing_fixture :
    (0,2) ∈ shape3 ∧ (0,2) ∉ shape2 ∧ belowLiteral shape2 0 = 0 ∧ rightLiteral shape2 2 = 0 := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> decide

/-- λ = (1,1), new box (0,1) (μ = (2,1)): printed |1/λ| = 1, column convention 0. -/
theorem separating_fixture_two :
    (0,1) ∈ shape21 ∧ (0,1) ∉ shape11 ∧ belowLiteral shape11 0 = 1 ∧ rightLiteral shape11 1 = 0 := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> decide

/-- Literal inherited sign statistics of the column (1^2) = shape11: directNorth = north = 1,
so the (3.4) prefactor of s^p_(1^2) is (-1)^2 = +1 (compare Lemma 3.5 bookkeeping). -/
theorem column_prefactor :
    TableauStripSigns.directNorth shape11 = 1 ∧ TableauStripSigns.north shape11 = 1 := by
  refine ⟨?_, ?_⟩ <;> decide

theorem signs_differ : (-1 : ℤ) ^ belowLiteral shape2 1 ≠ (-1 : ℤ) ^ rightLiteral shape2 0 := by
  rw [separating_fixture.2.2.1, separating_fixture.2.2.2]; decide

end OddMath.Frontier.OddLRVerticalPieriControls
