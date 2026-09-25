import OddMath.Frontier.TableauRunGeometry
import OddMath.Frontier.TableauOfRows
import OddMath.Frontier.TableauRowTransport

/-!
One-letter insertion of a genuine bounded positive semistandard tableau.
The output is reconstruction of the installed first-strictly-greater recursion.
Exact cell growth is derived below; it is not an input certificate.
Fulton, Young Tableaux §1.1, printed pp. 7–8 (frozen PDF pp. 19–20)
fixes the row insertion convention. Odd signs use the installed row transport:
each bumped old row contributes its length minus one; the final append contributes zero.
-/
namespace OddMath.Frontier.TableauInsertion
open TableauSign TableauEvaluation TableauRowStep TableauRowRecursion TableauRunGeometry

structure Inserted (n : ℕ) where
  shape : YoungDiagram
  tableau : PositiveTableau shape
  bounded : InAlphabet n tableau
  newCell : ℕ × ℕ
  crossings : ℕ

noncomputable def insert (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (a : Fin n) : Inserted n where
  shape := TableauOfRows.shape n (runRows n (rows n T hT) a).output
    (tableau_run_geometry n μ T hT a).2.1
  tableau := TableauOfRows.tableau n (runRows n (rows n T hT) a).output
    (tableau_run_geometry n μ T hT a).1 (tableau_run_geometry n μ T hT a).2.1
  bounded := TableauOfRows.bounded n (runRows n (rows n T hT) a).output
    (tableau_run_geometry n μ T hT a).1 (tableau_run_geometry n μ T hT a).2.1
  newCell := newCell n (rows n T hT) a
  crossings := (runRows n (rows n T hT) a).crossings

def insertCell (p : ℕ × ℕ) (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  Insert.insert p s

variable (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ) (hT : InAlphabet n T) (a : Fin n)

theorem insert_rows : rows n (insert n μ T hT a).tableau (insert n μ T hT a).bounded =
    (runRows n (rows n T hT) a).output :=
  TableauOfRows.rows_tableau n _ (tableau_run_geometry n μ T hT a).1
    (tableau_run_geometry n μ T hT a).2.1 (tableau_run_geometry n μ T hT a).2.2.1

theorem insert_rowFinWord : rowFinWord n (insert n μ T hT a).tableau
    (insert n μ T hT a).bounded = readRows (runRows n (rows n T hT) a).output :=
  TableauOfRows.rowFinWord_tableau n _ (tableau_run_geometry n μ T hT a).1
    (tableau_run_geometry n μ T hT a).2.1 (tableau_run_geometry n μ T hT a).2.2.1

theorem insert_newCell : (insert n μ T hT a).newCell = newCell n (rows n T hT) a := rfl

theorem insert_crossings : (insert n μ T hT a).crossings =
    (runRows n (rows n T hT) a).crossings := rfl

theorem insert_crossings_sum : (insert n μ T hT a).crossings =
    (((rows n T hT).take (insert n μ T hT a).newCell.1).map (fun w => w.length - 1)).sum :=
  runRows_crossings n (rows n T hT) a

theorem insert_entry (r c : ℕ) : (insert n μ T hT a).tableau.entry r c =
    (((((runRows n (rows n T hT) a).output)[r]?.getD [])[c]?).map
      (fun x : Fin n => x.val + 1)).getD 0 := rfl

-- The terminal row alone gains one cell, including a new row beyond the old shape.
private theorem run_length_at (rs : List (List (Fin n))) (a : Fin n) (r : ℕ) :
    ((runRows n rs a).output[r]?.getD []).length = (rs[r]?.getD []).length +
      if r = (runRows n rs a).columns.length - 1 then 1 else 0 := by
  induction rs generalizing a r with
  | nil => cases r <;> simp [runRows]
  | cons w ws ih =>
    cases hfg : firstGreater n w a with
    | append ha => cases r <;> simp [runRows, hfg]
    | bump u b v hs hu hab =>
      simp only [runRows, hfg]
      have hp := List.length_pos_iff.mpr (runRows_columns_nonempty n ws b)
      have he : (runRows n ws b).columns.length =
          (runRows n ws b).columns.length - 1 + 1 := by omega
      simp only [List.length_cons, Nat.add_sub_cancel]
      cases r with
      | zero => simp [hs, (Nat.ne_of_gt hp).symm]
      | succ r =>
        simp only [List.getElem?_cons_succ]
        rw [ih b r]
        have hi : (r = (runRows n ws b).columns.length - 1) ↔
            (r + 1 = (runRows n ws b).columns.length) := by omega
        simp only [Nat.succ_eq_add_one, hi]

private theorem old_row_length (r : ℕ) :
    ((rows n T hT)[r]?.getD []).length = μ.rowLen r := by
  by_cases hr : r < μ.colLen 0
  · simp [rows, hr, row_length]
  · have hz : μ.rowLen r = 0 := by
      have hn : (r, 0) ∉ μ := by simpa only [YoungDiagram.mem_iff_lt_colLen] using hr
      rw [YoungDiagram.mem_iff_lt_rowLen] at hn
      omega
    have ho : (List.range (μ.colLen 0))[r]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hr)
    simp [rows, ho, hz]

theorem insert_cells : (insert n μ T hT a).newCell ∉ μ.cells ∧
    (insert n μ T hT a).shape.cells = insertCell (insert n μ T hT a).newCell μ.cells := by
  have hc : (insert n μ T hT a).newCell.2 = μ.rowLen (insert n μ T hT a).newCell.1 := by
    rw [insert_newCell, newCell_column, old_row_length]
  have hl (r : ℕ) : ((runRows n (rows n T hT) a).output[r]?.getD []).length =
      μ.rowLen r + if r = (insert n μ T hT a).newCell.1 then 1 else 0 := by
    simpa only [old_row_length, insert_newCell, newCell] using run_length_at n (rows n T hT) a r
  constructor
  · change (insert n μ T hT a).newCell ∉ μ
    rw [YoungDiagram.mem_iff_lt_rowLen, hc]
    exact Nat.lt_irrefl _
  · ext p
    change p ∈ TableauOfRows.shape n (runRows n (rows n T hT) a).output
        (tableau_run_geometry n μ T hT a).2.1 ↔ p ∈ insertCell (insert n μ T hT a).newCell μ.cells
    rw [TableauOfRows.shape_mem, hl]
    simp only [insertCell, Finset.mem_insert]
    change p.2 < μ.rowLen p.1 + (if p.1 = (insert n μ T hT a).newCell.1 then 1 else 0) ↔
      p = (insert n μ T hT a).newCell ∨ p ∈ μ
    rw [YoungDiagram.mem_iff_lt_rowLen, Prod.ext_iff]
    by_cases hr : p.1 = (insert n μ T hT a).newCell.1
    · simp only [hr, if_pos, true_and]
      rw [← hc]
      omega
    · simp [hr]

theorem insert_card : (insert n μ T hT a).shape.card = μ.card + 1 := by
  have h := insert_cells n μ T hT a
  change (insert n μ T hT a).shape.cells.card = μ.cells.card + 1
  rw [h.2]
  exact Finset.card_insert_of_not_mem h.1

private theorem readRows_count (rs : List (List (Fin n))) (i : Fin n) :
    (readRows rs).count i = rs.flatten.count i := by
  unfold readRows
  exact List.Perm.count_eq (List.Perm.flatten (List.reverse_perm rs)) i

theorem insert_content (i : Fin n) :
    TableauContent.content (insert n μ T hT a).tableau (i.val + 1) =
      TableauContent.content T (i.val + 1) + if i = a then 1 else 0 := by
  change exponents n (insert n μ T hT a).tableau i = exponents n T i + _
  rw [← rowFinWord_count n _ (insert n μ T hT a).bounded i,
    ← rowFinWord_count n T hT i, insert_rowFinWord, ← readRows_rows n μ T hT]
  rw [readRows_count, readRows_count]
  exact runRows_count n (rows n T hT) a i

theorem insert_word : OddPlactic.word n (rowFinWord n T hT ++ [a]) =
    (-1 : ℤ) ^ (insert n μ T hT a).crossings •
      OddPlactic.word n (rowFinWord n (insert n μ T hT a).tableau (insert n μ T hT a).bounded) := by
  rw [insert_rowFinWord, insert_crossings]
  exact TableauRowTransport.tableau_word n μ T hT a

theorem insert_polynomial : rowPolynomial n T hT * PlacticEvaluation.tildeGenerator a =
    (-1 : ℤ) ^ (insert n μ T hT a).crossings •
      rowPolynomial n (insert n μ T hT a).tableau (insert n μ T hT a).bounded := by
  have h := congrArg (PlacticEvaluation.toSkew n) (insert_word n μ T hT a)
  simpa only [OddPlactic.word_append, OddPlactic.word_cons, OddPlactic.word_nil,
    mul_one, map_mul, PlacticEvaluation.toSkew_q, rowPolynomial, map_zsmul] using h

end OddMath.Frontier.TableauInsertion
