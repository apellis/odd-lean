import OddMath.Frontier.TableauReverseOutput
import OddMath.Frontier.TableauReverseRunInverse

/-!
Complete dependent inverse laws for the installed public tableau operations.
Fulton, Young Tableaux §1.1, printed p8 / frozen preview PDF20, lines700–709.
The raw run inverse is consumed, then genuine reconstruction recovers BOTH
shape and all-coordinate entries. No algorithm or inverse certificate is added.
-/
namespace OddMath.Frontier.TableauInsertionInverse
open TableauSign TableauEvaluation TableauRowRecursion TableauCorner
  TableauReverseRun TableauReverseOutput TableauReverseRunInverse

private theorem sigma_eq_of_shape_entries (n : ℕ) (μ ν : YoungDiagram)
    (S : PositiveTableau μ) (hS : InAlphabet n S)
    (T : PositiveTableau ν) (hT : InAlphabet n T)
    (hshape : μ = ν) (he : ∀ r c, S.entry r c = T.entry r c) :
    (⟨μ, ⟨S,hS⟩⟩ : Σ ξ : YoungDiagram, {U : PositiveTableau ξ // InAlphabet n U}) =
      ⟨ν, ⟨T,hT⟩⟩ := by
  cases hshape
  have ht : S = T := TableauContent.ext_cells (fun p _ => he p.1 p.2)
  cases ht
  rfl

-- Injectivity of the existing genuine-row representation, including its index.
private theorem sigma_eq_of_rows (n : ℕ) (μ ν : YoungDiagram)
    (S : PositiveTableau μ) (hS : InAlphabet n S)
    (T : PositiveTableau ν) (hT : InAlphabet n T)
    (hr : rows n S hS = rows n T hT) :
    (⟨μ, ⟨S,hS⟩⟩ : Σ ξ : YoungDiagram, {U : PositiveTableau ξ // InAlphabet n U}) =
      ⟨ν, ⟨T,hT⟩⟩ := by
  obtain ⟨ss,sc,_,sh,se⟩ := TableauOfRows.genuine_roundtrip n μ S hS
  obtain ⟨ts,tc,_,th,te⟩ := TableauOfRows.genuine_roundtrip n ν T hT
  apply sigma_eq_of_shape_entries n μ ν S hS T hT
  · apply YoungDiagram.ext
    ext ⟨r,c⟩
    change (r,c) ∈ μ ↔ (r,c) ∈ ν
    rw [← sh, ← th, TableauOfRows.shape_mem, TableauOfRows.shape_mem, hr]
  · intro r c
    rw [← se r c, ← te r c, TableauOfRows.tableau_entry, TableauOfRows.tableau_entry, hr]

/-- Removing the actual added corner recovers the full original bounded tableau,
    inserted letter, and exact forward path. -/
theorem remove_after_insert (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (a : Fin n) :
  let I := TableauInsertion.insert n μ T hT a
  let hp := insert_newCell_corner n μ T hT a
  let R := remove n I.shape I.tableau I.bounded I.newCell hp
  (⟨eraseShape I.shape I.newCell hp, ⟨R.tableau, R.bounded⟩⟩ :
      Σ ν : YoungDiagram, {S : PositiveTableau ν // InAlphabet n S}) = ⟨μ, ⟨T,hT⟩⟩ ∧
    R.letter = a ∧ R.columns = (runRows n (rows n T hT) a).columns := by
  let I := TableauInsertion.insert n μ T hT a
  let hp := insert_newCell_corner n μ T hT a
  let q : ReverseRun n := ⟨rows n T hT, a, (runRows n (rows n T hT) a).columns⟩
  have hq : reverseRows n (rows n I.tableau I.bounded) I.newCell.1 I.newCell.2 = some q := by
    rw [TableauInsertion.insert_rows, TableauInsertion.insert_newCell]
    exact tableau_reverse_after_runRows n μ T hT a
  refine ⟨?_, remove_letter_columns n I.shape I.tableau I.bounded I.newCell hp q hq⟩
  apply sigma_eq_of_rows
  exact remove_rows n I.shape I.tableau I.bounded I.newCell hp q hq

/-- Reinserting the actual returned letter recovers the full original bounded
    tableau, chosen corner and exact reverse path, for every genuine corner. -/
theorem insert_after_remove (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) :
  let R := remove n μ T hT p hp
  let I := TableauInsertion.insert n (eraseShape μ p hp) R.tableau R.bounded R.letter
  (⟨I.shape, ⟨I.tableau,I.bounded⟩⟩ :
      Σ ν : YoungDiagram, {S : PositiveTableau ν // InAlphabet n S}) = ⟨μ, ⟨T,hT⟩⟩ ∧
    I.newCell = p ∧ (runRows n (rows n R.tableau R.bounded) R.letter).columns = R.columns := by
  let R := remove n μ T hT p hp
  let q : ReverseRun n := ⟨rows n R.tableau R.bounded, R.letter, R.columns⟩
  have h := tableau_runRows_after_reverse n μ T hT p hp q (remove_run n μ T hT p hp)
  refine ⟨?_, h.2.2, h.2.1⟩
  apply sigma_eq_of_rows
  rw [TableauInsertion.insert_rows]
  exact h.1

#print axioms sigma_eq_of_shape_entries
#print axioms sigma_eq_of_rows
#print axioms remove_after_insert
#print axioms insert_after_remove
end OddMath.Frontier.TableauInsertionInverse
