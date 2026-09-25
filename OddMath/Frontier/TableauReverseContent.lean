import OddMath.Frontier.TableauReverseOutput
import OddMath.Frontier.TableauReverseRunInverse

/-!
Exact content of the actual reverse insertion operation, for every natural label.
Fulton, Young Tableaux §1.1 p.8 (frozen preview PDF20, lines700–709) specifies
rightmost strictly-smaller upward bumps from any outside corner. Content is the
actual cell multiplicity in TableauContent (Ellis arXiv:1111.3932v1 §2.1).
No complete dependent inverse, positive-rank premise, or count certificate is used.
-/
namespace OddMath.Frontier.TableauReverseContent
open TableauSign TableauEvaluation TableauRowStep TableauRowRecursion
  TableauCorner TableauReverseRun

private theorem rows_count (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (i : Fin n) :
    (rows n T hT).flatten.count i = TableauContent.content T (i.val+1) := by
  have h := rowFinWord_count n T hT i
  rw [← readRows_rows n μ T hT] at h
  have hr : (readRows (rows n T hT)).count i = (rows n T hT).flatten.count i :=
    List.Perm.count_eq (List.Perm.flatten (List.reverse_perm (rows n T hT))) i
  exact hr.symm.trans h

private theorem row_length_getD (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
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

private theorem bounded_count (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) (i : Fin n) :
    let R := TableauReverseOutput.remove n μ T hT p hp
    TableauContent.content R.tableau (i.val+1) + (if i = R.letter then 1 else 0) =
      TableauContent.content T (i.val+1) := by
  let R := TableauReverseOutput.remove n μ T hT p hp
  have hq := TableauReverseOutput.remove_run n μ T hT p hp
  have hr : p.1 < (rows n T hT).length := by
    rw [rows_length]
    exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp hp.1)
      (μ.colLen_anti 0 p.2 (Nat.zero_le _))
  have he : ((rows n T hT)[p.1]?.getD []).length = p.2+1 := by
    rw [row_length_getD]
    exact corner_rowLen μ p hp
  have hb : ((rows n T hT)[p.1+1]?.getD []).length ≤ p.2 := by
    rw [row_length_getD]
    have h := hp.2.1
    rw [YoungDiagram.mem_iff_lt_rowLen] at h
    omega
  have h := TableauReverseRunInverse.reverseRows_count n (rows n T hT) p.1 p.2
    ⟨rows n R.tableau R.bounded, R.letter, R.columns⟩
    (rows_sorted n μ T hT) (TableauRunGeometry.rows_columns n μ T hT)
    (TableauRunGeometry.rows_nonempty n μ T hT) hr he hb hq i
  change (rows n R.tableau R.bounded).flatten.count i +
    (if i = R.letter then 1 else 0) = (rows n T hT).flatten.count i at h
  simpa only [rows_count] using h

private theorem content_above (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (k : ℕ) (hk : n < k) : TableauContent.content T k = 0 := by
  rw [TableauContent.content_apply]
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro p hp he
  have h := hT p hp
  omega

/-- Add back the returned letter: equality of the complete natural-label content. -/
theorem remove_content (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) :
    let R := TableauReverseOutput.remove n μ T hT p hp
    TableauContent.content R.tableau + Finsupp.single (R.letter.val+1) 1 =
      TableauContent.content T := by
  classical
  let R := TableauReverseOutput.remove n μ T hT p hp
  change TableauContent.content R.tableau + Finsupp.single (R.letter.val+1) 1 = _
  ext k
  rw [Finsupp.add_apply, Finsupp.single_apply]
  by_cases hk0 : k = 0
  · subst k
    simp
  · by_cases hkn : k ≤ n
    · let i : Fin n := ⟨k-1, by omega⟩
      have hi : i.val+1 = k := by dsimp [i]; omega
      have heq : R.letter.val+1 = k ↔ i = R.letter := by
        constructor
        · intro h; apply Fin.ext; dsimp [i]; omega
        · intro h; rw [← h, hi]
      simp only [heq]
      simpa only [hi] using bounded_count n μ T hT p hp i
    · have hk : n < k := by omega
      have hne : R.letter.val+1 ≠ k := by have h := R.letter.isLt; omega
      rw [content_above n _ R.tableau R.bounded k hk,
        content_above n μ T hT k hk, if_neg hne]
      rfl

/-- Evaluation at an arbitrary alphabet letter, derived from full content equality. -/
theorem remove_content_apply (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) (i : Fin n) :
    let R := TableauReverseOutput.remove n μ T hT p hp
    TableauContent.content R.tableau (i.val+1) + (if i = R.letter then 1 else 0) =
      TableauContent.content T (i.val+1) := by
  have h := congrArg (fun f : ℕ →₀ ℕ => f (i.val+1)) (remove_content n μ T hT p hp)
  simpa only [Finsupp.add_apply, Finsupp.single_apply, Nat.add_right_cancel_iff,
    Fin.val_inj, eq_comm] using h

#print axioms rows_count
#print axioms row_length_getD
#print axioms bounded_count
#print axioms content_above
#print axioms remove_content
#print axioms remove_content_apply
end OddMath.Frontier.TableauReverseContent
