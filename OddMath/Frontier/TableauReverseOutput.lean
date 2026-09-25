import OddMath.Frontier.TableauReverseRun
import OddMath.Frontier.TableauOfRows

/-!
Genuine reverse insertion output on the erased YoungDiagram.
Fulton, Young Tableaux §1.1, printed p.8 / frozen preview PDF20, lines700–709:
reverse bump the rightmost STRICTLY smaller entry, starting at any outside corner.
The only choice here selects the installed successful reverse run. Its SAME output
is reconstructed by TableauOfRows and transported along exact cell-set equality.
No inverse law, content formula, or unchanged-entry restriction is assumed.
-/
namespace OddMath.Frontier.TableauReverseOutput
open TableauSign TableauEvaluation TableauRowStep TableauRowRecursion
  TableauBumpBoundary TableauCorner TableauReverseRun

structure Removed (n : ℕ) (μ : YoungDiagram) (p : ℕ × ℕ)
    (hp : IsCorner μ p) where
  tableau : PositiveTableau (eraseShape μ p hp)
  bounded : InAlphabet n tableau
  letter : Fin n
  columns : List ℕ

private theorem old_row_length (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (r : ℕ) :
    ((rows n T hT)[r]?.getD []).length = μ.rowLen r := by
  by_cases hr : r < μ.colLen 0
  · simp [rows, hr, row_length]
  · have hz : μ.rowLen r = 0 := by
      have hn : (r,0) ∉ μ := by simpa only [YoungDiagram.mem_iff_lt_colLen] using hr
      rw [YoungDiagram.mem_iff_lt_rowLen] at hn
      omega
    have ho : (List.range (μ.colLen 0))[r]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hr)
    simp [rows,ho,hz]

/-- Exact erased diagram, for any actual run and any proof of its output columns. -/
theorem output_shape (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) (q : ReverseRun n)
    (hq : reverseRows n (rows n T hT) p.1 p.2 = some q)
    (hc : ∀ j : ℕ, ColumnBelow (q.output[j]?.getD []) (q.output[j+1]?.getD [])) :
    TableauOfRows.shape n q.output hc = eraseShape μ p hp := by
  obtain ⟨q',hq',_,_,_,hl,_⟩ := tableau_reverseRows_geometry n μ T hT p hp
  have he : q' = q := Option.some.inj (hq'.symm.trans hq)
  subst q'
  apply YoungDiagram.ext
  ext ⟨r,c⟩
  change (r,c) ∈ TableauOfRows.shape n q.output hc ↔ (r,c) ∈ μ.cells.erase p
  rw [TableauOfRows.shape_mem, hl r, Finset.mem_erase]
  change c < (if r = p.1 then p.2 else ((rows n T hT)[r]?.getD []).length) ↔
    (r,c) ≠ p ∧ (r,c) ∈ μ
  rw [old_row_length, YoungDiagram.mem_iff_lt_rowLen]
  by_cases hr : r = p.1
  · simp only [hr, if_pos, Prod.ext_iff, true_and, ne_eq]
    rw [corner_rowLen μ p hp]
    omega
  · simp [Prod.ext_iff,hr]

-- Keep all dependent transport equations explicit, including off-shape entries.
private def transport {α β : YoungDiagram} (h : α = β) (T : PositiveTableau α) :
    PositiveTableau β := h ▸ T

private theorem transport_bounded {n : ℕ} {α β : YoungDiagram} (h : α = β)
    (T : PositiveTableau α) (hT : InAlphabet n T) : InAlphabet n (transport h T) := by
  cases h
  exact hT

private theorem transport_entry {α β : YoungDiagram} (h : α = β)
    (T : PositiveTableau α) (r c : ℕ) : (transport h T).entry r c = T.entry r c := by
  cases h
  rfl

private theorem transport_rows {n : ℕ} {α β : YoungDiagram} (h : α = β)
    (T : PositiveTableau α) (hT : InAlphabet n T) :
    rows n (transport h T) (transport_bounded h T hT) = rows n T hT := by
  cases h
  rfl

private noncomputable def chosen (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) : ReverseRun n :=
  Classical.choose (tableau_reverseRows_geometry n μ T hT p hp)

private theorem chosen_spec (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) :
    let q := chosen n μ T hT p hp
    reverseRows n (rows n T hT) p.1 p.2 = some q ∧
      (∀ w ∈ q.output, w.Sorted (· ≤ ·)) ∧
      (∀ j : ℕ, ColumnBelow (q.output[j]?.getD []) (q.output[j+1]?.getD [])) ∧
      (∀ w ∈ q.output, w ≠ []) ∧
      (∀ j : ℕ, (q.output[j]?.getD []).length =
        if j = p.1 then p.2 else ((rows n T hT)[j]?.getD []).length) ∧
      q.columns.length = p.1+1 ∧ q.columns.Sorted (· ≥ ·) ∧
      q.columns.getLast? = some p.2 ∧ q.output.drop (p.1+1) = (rows n T hT).drop (p.1+1) :=
  Classical.choose_spec (tableau_reverseRows_geometry n μ T hT p hp)

noncomputable def remove (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) : Removed n μ p hp :=
  let q := chosen n μ T hT p hp
  let hg := chosen_spec n μ T hT p hp
  let S := TableauOfRows.tableau n q.output hg.2.1 hg.2.2.1
  let hS := TableauOfRows.bounded n q.output hg.2.1 hg.2.2.1
  let he := output_shape n μ T hT p hp q hg.1 hg.2.2.1
  ⟨transport he S, transport_bounded he S hS, q.letter, q.columns⟩

variable (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ) (hT : InAlphabet n T)
  (p : ℕ × ℕ) (hp : IsCorner μ p)

private theorem chosen_eq (q : ReverseRun n)
    (hq : reverseRows n (rows n T hT) p.1 p.2 = some q) : chosen n μ T hT p hp = q :=
  Option.some.inj ((chosen_spec n μ T hT p hp).1.symm.trans hq)

private theorem remove_rows_chosen :
    rows n (remove n μ T hT p hp).tableau (remove n μ T hT p hp).bounded =
      (chosen n μ T hT p hp).output := by
  dsimp only [remove]
  rw [transport_rows]
  exact TableauOfRows.rows_tableau n _ (chosen_spec n μ T hT p hp).2.1
    (chosen_spec n μ T hT p hp).2.2.1 (chosen_spec n μ T hT p hp).2.2.2.1

theorem remove_run : reverseRows n (rows n T hT) p.1 p.2 =
    some { output := rows n (remove n μ T hT p hp).tableau (remove n μ T hT p hp).bounded,
           letter := (remove n μ T hT p hp).letter, columns := (remove n μ T hT p hp).columns } := by
  rw [remove_rows_chosen]
  exact (chosen_spec n μ T hT p hp).1

theorem remove_rows (q : ReverseRun n)
    (hq : reverseRows n (rows n T hT) p.1 p.2 = some q) :
    rows n (remove n μ T hT p hp).tableau (remove n μ T hT p hp).bounded = q.output := by
  rw [remove_rows_chosen, chosen_eq n μ T hT p hp q hq]

theorem remove_entry (q : ReverseRun n)
    (hq : reverseRows n (rows n T hT) p.1 p.2 = some q) (r c : ℕ) :
    (remove n μ T hT p hp).tableau.entry r c =
      (((q.output[r]?.getD [])[c]?).map (fun x : Fin n => x.val+1)).getD 0 := by
  dsimp only [remove]
  rw [transport_entry, TableauOfRows.tableau_entry, chosen_eq n μ T hT p hp q hq]

theorem remove_letter_columns (q : ReverseRun n)
    (hq : reverseRows n (rows n T hT) p.1 p.2 = some q) :
    (remove n μ T hT p hp).letter = q.letter ∧ (remove n μ T hT p hp).columns = q.columns := by
  change (chosen n μ T hT p hp).letter = q.letter ∧ (chosen n μ T hT p hp).columns = q.columns
  rw [chosen_eq n μ T hT p hp q hq]
  exact ⟨rfl,rfl⟩

theorem remove_rowFinWord (q : ReverseRun n)
    (hq : reverseRows n (rows n T hT) p.1 p.2 = some q) :
    rowFinWord n (remove n μ T hT p hp).tableau (remove n μ T hT p hp).bounded = readRows q.output := by
  rw [← readRows_rows, remove_rows n μ T hT p hp q hq]

theorem remove_path : (remove n μ T hT p hp).columns.length = p.1+1 ∧
    (remove n μ T hT p hp).columns.Sorted (· ≥ ·) ∧
    (remove n μ T hT p hp).columns.getLast? = some p.2 := by
  have hg := (chosen_spec n μ T hT p hp).2.2.2.2.2
  exact ⟨hg.1,hg.2.1,hg.2.2.1⟩

-- n,T,hT explicitly retained: this is the shape fixed by this output's type.
theorem remove_card (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (_hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) :
    (eraseShape μ p hp).card+1 = μ.card := by
  exact erase_card μ p hp

#print axioms Removed
#print axioms old_row_length
#print axioms output_shape
#print axioms transport
#print axioms transport_bounded
#print axioms transport_entry
#print axioms transport_rows
#print axioms chosen
#print axioms chosen_spec
#print axioms remove
#print axioms chosen_eq
#print axioms remove_rows_chosen
#print axioms remove_run
#print axioms remove_rows
#print axioms remove_entry
#print axioms remove_letter_columns
#print axioms remove_rowFinWord
#print axioms remove_path
#print axioms remove_card
#print axioms Removed.mk
#print axioms Removed.tableau
#print axioms Removed.bounded
#print axioms Removed.letter
#print axioms Removed.columns
#print axioms Removed.rec
#print axioms Removed.casesOn
#print axioms Removed.recOn
#print axioms Removed.noConfusionType
#print axioms Removed.noConfusion
end OddMath.Frontier.TableauReverseOutput
