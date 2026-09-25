import OddMath.Frontier.TableauContent
import Mathlib.Data.List.Sort

/-!
# Actual row words and their inversion sign

Ellis arXiv:1111.3932v1 §2.1: left to right, bottom to top; §2.2:
`sign(T) = (-1)^{N^<(T)}`. Also EK arXiv:1107.5610v2 §3.3, p.27.
The recursive list statistic is independent of the inherited all-pairs box count.
-/
namespace OddMath.Frontier.TableauRowWord

open TableauSign
open LrLegA

/-- English row reading: decreasing row, then increasing column. -/
def RowLE (a b : ℕ × ℕ) : Prop := b.1 < a.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

instance : DecidableRel RowLE := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

instance : IsTotal (ℕ × ℕ) RowLE := ⟨by intro a b; unfold RowLE; omega⟩
instance : IsTrans (ℕ × ℕ) RowLE := ⟨by intro a b c; unfold RowLE; omega⟩

/-- Sort the actual finite shape cells, not the arbitrary inherited box list. -/
noncomputable def rowCells (μ : YoungDiagram) : List (ℕ × ℕ) :=
  μ.cells.toList.mergeSort (fun a b => decide (RowLE a b))

/-- Actual tableau entries in source row-reading order. -/
noncomputable def rowWord {μ : YoungDiagram} (T : PositiveTableau μ) : List ℕ :=
  (rowCells μ).map (fun p => T.entry p.1 p.2)

/-- Strict inversions in a word; repeated letters are not inversions. -/
def inversions : List ℕ → ℕ
  | [] => 0
  | x :: xs => (xs.filter (fun y => y < x)).length + inversions xs

variable {μ : YoungDiagram}

theorem rowCells_perm (μ : YoungDiagram) : List.Perm (rowCells μ) μ.cells.toList :=
  List.mergeSort_perm _ _

theorem rowCells_nodup (μ : YoungDiagram) : (rowCells μ).Nodup :=
  (rowCells_perm μ).nodup_iff.mpr μ.cells.nodup_toList

@[simp] theorem mem_rowCells (μ : YoungDiagram) (p : ℕ × ℕ) :
    p ∈ rowCells μ ↔ p ∈ μ.cells := by
  rw [(rowCells_perm μ).mem_iff, Finset.mem_toList]

theorem rowCells_sorted (μ : YoungDiagram) : List.Sorted RowLE (rowCells μ) :=
  List.sorted_mergeSort' RowLE _

theorem rowWord_length (T : PositiveTableau μ) : (rowWord T).length = μ.card := by
  simp only [rowWord, List.length_map]
  rw [(rowCells_perm μ).length_eq]
  simp [YoungDiagram.card]

/-- Counting letters preserves multiplicity, including repeated entries. -/
theorem rowWord_count (T : PositiveTableau μ) (k : ℕ) :
    (rowWord T).count k = TableauContent.content T k := by
  classical
  rw [TableauContent.content_apply]
  simp only [rowWord, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  let l := (rowCells μ).filter (fun p => T.entry p.1 p.2 == k)
  have hn : l.Nodup := (rowCells_nodup μ).filter _
  have he : l.toFinset = μ.cells.filter (fun p => T.entry p.1 p.2 = k) := by
    ext p
    simp [l]
  rw [List.filter_map, List.length_map]
  change l.length = _
  rw [← List.toFinset_card_of_nodup hn, he]

/-- A per-box count is independent of the enumeration of its candidates. -/
theorem countNorthLt_perm {as bs : Tableau} (h : List.Perm as bs) (B : TBox) :
    countNorthLt as B = countNorthLt bs B := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [countNorthLt, ih]
  | swap a b l => simp only [countNorthLt]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Both arguments of the all-pairs count are permutation invariant. -/
theorem totalNorthLt_perm {as bs cs ds : Tableau}
    (h : List.Perm as bs) (k : List.Perm cs ds) :
    totalNorthLt as cs = totalNorthLt bs ds := by
  have left (l : Tableau) : totalNorthLt as l = totalNorthLt bs l := by
    induction l with
    | nil => rfl
    | cons B l ih => simp only [totalNorthLt, countNorthLt_perm h, ih]
  rw [left]
  induction k with
  | nil => rfl
  | cons B k ih => simp only [totalNorthLt, ih]
  | swap A B l => simp only [totalNorthLt]; omega
  | trans k₁ k₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Row weakness excludes a same-row inversion in a correctly ordered pair. -/
theorem entry_lt_iff_north (T : PositiveTableau μ) {a b : ℕ × ℕ}
    (hb : b ∈ μ.cells) (hab : RowLE a b) :
    T.entry b.1 b.2 < T.entry a.1 a.2 ↔
      b.1 < a.1 ∧ T.entry b.1 b.2 < T.entry a.1 a.2 := by
  constructor
  · intro h
    refine ⟨?_, h⟩
    rcases hab with hrow | ⟨hrow, hcol⟩
    · exact hrow
    · have hw := T.toSemistandardYoungTableau.row_weak_of_le hcol
        (show (b.1, b.2) ∈ μ from by simpa using hb)
      rw [hrow] at h
      change T.entry b.1 a.2 ≤ T.entry b.1 b.2 at hw
      omega
  · exact And.right

/-- In a sorted suffix, the recursive head-inversion count is exactly N^<. -/
theorem head_inversions (T : PositiveTableau μ) (a : ℕ × ℕ)
    (l : List (ℕ × ℕ))
    (hm : ∀ b ∈ l, b ∈ μ.cells) (ho : ∀ b ∈ l, RowLE a b) :
    ((l.map (fun p => T.entry p.1 p.2)).filter
      (fun y => y < T.entry a.1 a.2)).length =
      countNorthLt (l.map (box T)) (box T a) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb := hm b (by simp)
    have hab := ho b (by simp)
    have ht := ih (fun c hc => hm c (by simp [hc]))
      (fun c hc => ho c (by simp [hc]))
    have he := entry_lt_iff_north T hb hab
    simp only [List.map_cons, List.filter_cons, countNorthLt, isNorth, isLtEntry, box]
    by_cases hv : T.entry b.1 b.2 < T.entry a.1 a.2
    · have hn := (he.mp hv).1
      simp only [hv, hn, decide_true, ite_true, List.length_cons, ht, Nat.add_comm]
      rfl
    · simp only [hv, decide_false, Bool.false_eq_true, ite_false, ite_self, zero_add, ht]
      rfl

/-- A head at least as far south as every reference box adds no north pair. -/
theorem totalNorthLt_cons_of_no_north (A : TBox) (as bs : Tableau)
    (h : ∀ B ∈ bs, ¬ A.row < B.row) :
    totalNorthLt (A :: as) bs = totalNorthLt as bs := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    have hn := h B (by simp)
    have ht := ih (fun C hc => h C (by simp [hc]))
    simp [totalNorthLt, countNorthLt, isNorth, hn, ht]

/-- The list recursion agrees with the box statistic for any sorted cell sublist. -/
theorem inversions_sorted_cells (T : PositiveTableau μ) (l : List (ℕ × ℕ))
    (hm : ∀ p ∈ l, p ∈ μ.cells) (hs : List.Sorted RowLE l) :
    inversions (l.map (fun p => T.entry p.1 p.2)) =
      totalNorthLt (l.map (box T)) (l.map (box T)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨ho, hs⟩ := List.sorted_cons.mp hs
    have hm' : ∀ p ∈ l, p ∈ μ.cells := fun p hp => hm p (by simp [hp])
    have ht := ih hm' hs
    have hz : ∀ B ∈ l.map (box T), ¬ (box T a).row < B.row := by
      intro B hB
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
      have h := ho b hb
      simp only [box]
      unfold RowLE at h
      omega
    simp only [List.map_cons, inversions, totalNorthLt, countNorthLt,
      isNorth, box, Nat.lt_irrefl, decide_false, Bool.false_eq_true, ite_false, zero_add]
    rw [head_inversions T a l hm' ho, ht]
    exact congrArg (fun n => countNorthLt (l.map (box T)) (box T a) + n)
      (totalNorthLt_cons_of_no_north (box T a) (l.map (box T)) (l.map (box T)) hz).symm

/-- Exact, nondefinitional reading-word inversion / north-smaller-entry equality. -/
theorem rowWord_inversions (T : PositiveTableau μ) :
    inversions (rowWord T) = totalNorthLt (boxes T) (boxes T) := by
  have h := inversions_sorted_cells T (rowCells μ)
    (fun p hp => (mem_rowCells μ p).mp hp) (rowCells_sorted μ)
  have hp := (rowCells_perm μ).map (box T)
  exact h.trans (totalNorthLt_perm hp hp)

/-- The two source (-1)-power descriptions of the tableau sign agree. -/
theorem rowWord_sign (T : PositiveTableau μ) :
    (-1 : ℤ) ^ inversions (rowWord T) =
      (-1 : ℤ) ^ totalNorthLt (boxes T) (boxes T) := by
  rw [rowWord_inversions]

end OddMath.Frontier.TableauRowWord
