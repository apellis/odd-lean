import OddMath.Frontier.TableauBumpBoundary

/-!
Full-run geometry of the installed first-strictly-greater row recursion.
Fulton, Young Tableaux §1.1, printed pp. 7–8 / frozen PDF pp. 19–20:
the carry moves weakly left, preserving strict columns. This module composes
the installed adjacent boundary; it does not construct an output tableau.
-/
namespace OddMath.Frontier.TableauRunGeometry
open TableauSign TableauEvaluation TableauRowStep TableauRowRecursion TableauBumpBoundary

private theorem below_nil {n : ℕ} (w : List (Fin n)) : ColumnBelow w [] :=
  ⟨by simp, by simp⟩

private theorem append_upper {n : ℕ} (w lower : List (Fin n)) (a : Fin n)
    (hc : ColumnBelow w lower) : ColumnBelow (w ++ [a]) lower := by
  obtain ⟨hl, hp⟩ := hc
  refine ⟨by simp; omega, ?_⟩
  intro c h
  simpa only [List.getElem_append_left (lt_of_lt_of_le h hl)] using hp c h

private theorem rows_getD (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (r : ℕ) :
    (rows n T hT)[r]?.getD [] = row n T hT r := by
  by_cases hr : r < μ.colLen 0
  · simp [rows, hr]
  · have hz : μ.rowLen r = 0 := by
      have hn : ¬ (r, 0) ∈ μ := by simpa only [YoungDiagram.mem_iff_lt_colLen] using hr
      rw [YoungDiagram.mem_iff_lt_rowLen] at hn
      omega
    have he : row n T hT r = [] := List.length_eq_zero_iff.mp (by rw [row_length, hz])
    have ho : (List.range (μ.colLen 0))[r]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hr)
    simp [rows, ho, he]

theorem rows_columns (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) :
    ∀ r : ℕ, ColumnBelow ((rows n T hT)[r]?.getD [])
      ((rows n T hT)[r+1]?.getD []) := by
  intro r
  rw [rows_getD, rows_getD]
  exact rows_columnBelow n μ T hT r

theorem rows_nonempty (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) : ∀ w ∈ rows n T hT, w ≠ [] := by
  intro w hw
  have hm : w.length ∈ μ.rowLens := by
    rw [← rows_lengths n μ T hT]
    exact List.mem_map.mpr ⟨w, hw, rfl⟩
  have hp := μ.pos_of_mem_rowLens w.length hm
  intro he
  simp [he] at hp

-- The tail may be empty, append immediately, or bump again. In all three cases
-- its actual output head is exactly the row supplied by bump_boundary.
private theorem bump_head (n : ℕ) (u v : List (Fin n)) (a b : Fin n)
    (ws : List (List (Fin n)))
    (hc : ColumnBelow (u ++ (b :: v)) (ws[0]?.getD []))
    (hu : ∀ x ∈ u, x ≤ a) (hab : a < b) :
    ColumnBelow (u ++ (a :: v)) ((runRows n ws b).output[0]?.getD []) := by
  have hb := bump_boundary n u v a b (ws[0]?.getD []) hc hu hab
  cases ws with
  | nil => simpa [runRows, firstGreater] using hb.2
  | cons w ws =>
    simp only [List.getElem?_cons_zero, Option.getD_some] at hb
    cases he : firstGreater n w b with
    | append ha =>
      simp only [he] at hb
      simpa [runRows, he] using hb.2
    | bump p c q hs hp hbc =>
      simp only [he] at hb
      simpa [runRows, he] using hb.2

theorem runRows_columns (n : ℕ) (rs : List (List (Fin n))) (a : Fin n)
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) :
    ∀ r : ℕ, ColumnBelow ((runRows n rs a).output[r]?.getD [])
      ((runRows n rs a).output[r+1]?.getD []) := by
  induction rs generalizing a with
  | nil =>
    intro r
    cases r <;> simp [runRows, below_nil]
  | cons w ws ih =>
    have ht : ∀ r : ℕ, ColumnBelow (ws[r]?.getD []) (ws[r+1]?.getD []) := by
      intro r
      simpa using hc (r+1)
    have hh : ColumnBelow w (ws[0]?.getD []) := by simpa using hc 0
    simp only [runRows]
    split
    · intro r
      cases r with
      | zero => simpa using append_upper w (ws[0]?.getD []) a hh
      | succ r => simpa using ht r
    · rename_i u b v hs hu hab hdecision
      intro r
      cases r with
      | zero => simpa using bump_head n u v a b ws (hs ▸ hh) hu hab
      | succ r => simpa using ih b ht r

theorem runRows_nonempty (n : ℕ) (rs : List (List (Fin n))) (a : Fin n)
    (hn : ∀ w ∈ rs, w ≠ []) : ∀ w ∈ (runRows n rs a).output, w ≠ [] := by
  induction rs generalizing a with
  | nil => simp [runRows]
  | cons w ws ih =>
    have ht : ∀ z ∈ ws, z ≠ [] := fun z hz => hn z (List.mem_cons_of_mem w hz)
    simp only [runRows]
    split
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · simp
      · exact ht z hz
    · rename_i u b v hs hu hab hdecision
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · simp
      · exact ih b ht z hz

private theorem lengths_sorted (n : ℕ) (rs : List (List (Fin n)))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) :
    (rs.map List.length).Sorted (· ≥ ·) := by
  have hstep : ∀ r : ℕ, (rs[r+1]?.getD []).length ≤ (rs[r]?.getD []).length :=
    fun r => (hc r).1
  have hanti : Antitone (fun r => (rs[r]?.getD []).length) :=
    antitone_nat_of_succ_le hstep
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hi' : i < rs.length := by simpa using hi
  have hj' : j < rs.length := by simpa using hj
  simpa [List.getElem?_eq_getElem, hi', hj'] using hanti hij.le

theorem runRows_length_sorted (n : ℕ) (rs : List (List (Fin n))) (a : Fin n)
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) :
    ((runRows n rs a).output.map List.length).Sorted (· ≥ ·) :=
  lengths_sorted n _ (runRows_columns n rs a hc)

theorem newCell_column (n : ℕ) (rs : List (List (Fin n))) (a : Fin n) :
    (newCell n rs a).2 = (rs[(newCell n rs a).1]?.getD []).length := by
  induction rs generalizing a with
  | nil => simp [newCell, runRows]
  | cons w ws ih =>
    simp only [newCell, runRows]
    split
    · simp
    · rename_i u b v hs hu hab hdecision
      have hn := runRows_columns_nonempty n ws b
      have hp := List.length_pos_iff.mpr hn
      have he : (runRows n ws b).columns.length =
          ((runRows n ws b).columns.length - 1) + 1 := by omega
      have hl : (u.length :: (runRows n ws b).columns).getLast! =
          (runRows n ws b).columns.getLast! := by
        cases hq : (runRows n ws b).columns with
        | nil => exact False.elim (hn hq)
        | cons c cs => simp
      have hi : (w :: ws)[(runRows n ws b).columns.length]? =
          ws[(runRows n ws b).columns.length - 1]? := by
        conv_lhs => rw [he]
        rfl
      simp only [List.length_cons, Nat.add_sub_cancel, hl, hi]
      exact ih b

theorem tableau_run_geometry (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (a : Fin n) :
    let q := runRows n (rows n T hT) a
    (∀ w ∈ q.output, w.Sorted (· ≤ ·)) ∧
    (∀ r : ℕ, ColumnBelow (q.output[r]?.getD []) (q.output[r+1]?.getD [])) ∧
    (∀ w ∈ q.output, w ≠ []) ∧
    (q.output.map List.length).Sorted (· ≥ ·) := by
  exact ⟨runRows_sorted n _ a (rows_sorted n μ T hT),
    runRows_columns n _ a (rows_columns n μ T hT),
    runRows_nonempty n _ a (rows_nonempty n μ T hT),
    runRows_length_sorted n _ a (rows_columns n μ T hT)⟩

end OddMath.Frontier.TableauRunGeometry
