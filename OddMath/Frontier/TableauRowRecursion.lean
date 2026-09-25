import OddMath.Frontier.TableauRowStep

namespace OddMath.Frontier.TableauRowRecursion
open TableauSign TableauEvaluation TableauRowStep TableauRowWord

noncomputable def rows (n : ℕ) {μ : YoungDiagram} (T : PositiveTableau μ)
    (hT : InAlphabet n T) : List (List (Fin n)) :=
  (List.range (μ.colLen 0)).map (row n T hT)

def readRows {n : ℕ} (rs : List (List (Fin n))) : List (Fin n) := rs.reverse.flatten

structure RowRun (n : ℕ) where
  output : List (List (Fin n))
  columns : List ℕ
  crossings : ℕ

def runRows (n : ℕ) (rs : List (List (Fin n))) (a : Fin n) : RowRun n :=
  match rs with
  | [] => ⟨[[a]], [0], 0⟩
  | w :: ws => match firstGreater n w a with
    | .append _ => ⟨(w ++ [a]) :: ws, [w.length], 0⟩
    | .bump u b v _ _ _ =>
      let q := runRows n ws b
      ⟨(u ++ (a :: v)) :: q.output, u.length :: q.columns,
        (u.length + v.length) + q.crossings⟩
termination_by structural rs

def newCell (n : ℕ) (rs : List (List (Fin n))) (a : Fin n) : ℕ × ℕ :=
  ((runRows n rs a).columns.length - 1, (runRows n rs a).columns.getLast!)

theorem rows_length (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) : (rows n T hT).length = μ.colLen 0 := by simp [rows]

theorem rows_lengths (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) : (rows n T hT).map List.length = μ.rowLens := by
  simp [rows, List.map_map, row_length, YoungDiagram.rowLens]

theorem rows_get (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (r : ℕ) (hr : r < μ.colLen 0) :
    (rows n T hT)[r]'(by rw [rows_length]; exact hr) = row n T hT r := by
  simp [rows]

theorem rows_sorted (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) : ∀ w ∈ rows n T hT, w.Sorted (· ≤ ·) := by
  intro w hw
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hw
  exact row_sorted n μ T hT r

private theorem partition_top (l : List (ℕ × ℕ)) (k : ℕ)
    (hs : l.Sorted RowLE) (hb : ∀ c ∈ l, c.1 ≤ k) :
    l = l.filter (fun c => decide (c.1 = k)) ++
      l.filter (fun c => decide (c.1 < k)) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    obtain ⟨ho, ht⟩ := List.sorted_cons.mp hs
    have hc := hb c (by simp)
    have hi := ih ht (fun d hd => hb d (by simp [hd]))
    by_cases he : c.1 = k
    · have hn : ¬ c.1 < k := by omega
      simpa [he, hn] using congrArg (List.cons c) hi
    · have hc' : c.1 < k := by omega
      have hl : ∀ d ∈ l, d.1 < k := by
        intro d hd
        have hh := ho d hd
        unfold RowLE at hh
        omega
      have hz : l.filter (fun d => decide (d.1 = k)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro d hd
        have := hl d hd
        simp only [decide_eq_true_eq]
        omega
      simpa [he, hc', hz] using congrArg (List.cons c) hi

private theorem reconstruct_cells (k : ℕ) (l : List (ℕ × ℕ))
    (hs : l.Sorted RowLE) (hb : ∀ c ∈ l, c.1 < k) :
    ((List.range k).reverse.map (fun r => l.filter (fun c => decide (c.1 = r)))).flatten = l := by
  induction k generalizing l with
  | zero =>
    have hz : l = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro c hc
      have := hb c hc
      omega
    simp [hz]
  | succ k ih =>
    have hp := partition_top l k hs (by intro c hc; have := hb c hc; omega)
    have hi := ih (l.filter (fun c => decide (c.1 < k))) (hs.filter _)
      (by intro c hc; simpa using (List.mem_filter.mp hc).2)
    have hm : (List.range k).reverse.map
        (fun r => (l.filter (fun c => decide (c.1 < k))).filter
          (fun c => decide (c.1 = r))) =
        (List.range k).reverse.map (fun r => l.filter (fun c => decide (c.1 = r))) := by
      apply List.map_congr_left
      intro r hr
      have hr' : r < k := List.mem_range.mp (List.mem_reverse.mp hr)
      rw [List.filter_filter]
      congr 1
      funext c
      by_cases he : c.1 = r <;> simp [he, hr']
    rw [hm] at hi
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, List.flatten_cons]
    rw [hi]
    exact hp.symm

theorem readRows_rows (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) : readRows (rows n T hT) = rowFinWord n T hT := by
  have hc := reconstruct_cells (μ.colLen 0) (rowCells μ) (rowCells_sorted μ) (by
    intro c hc
    have hm := (mem_rowCells μ c).mp hc
    have hl := (YoungDiagram.mem_iff_lt_colLen).mp hm
    exact lt_of_lt_of_le hl (μ.colLen_anti 0 c.2 (Nat.zero_le _)))
  apply (List.map_inj_right (f := fun i : Fin n => i.val + 1)
    (by intro a b h; apply Fin.ext; change a.val + 1 = b.val + 1 at h; omega)).mp
  rw [rowFinWord_labels]
  unfold readRows rows
  rw [← List.map_reverse, List.map_flatten, List.map_map]
  have he : (List.range (μ.colLen 0)).reverse.map
      (fun r => (row n T hT r).map (fun i => i.val + 1)) =
      (List.range (μ.colLen 0)).reverse.map
        (fun r => ((rowCells μ).filter (fun c => decide (c.1 = r))).map
          (fun c => T.entry c.1 c.2)) := by
    apply List.map_congr_left
    intro r _
    rw [row_labels, rowCells_row, List.map_map]
    rfl
  change (List.map (fun r => (row n T hT r).map (fun i => i.val + 1))
    (List.range (μ.colLen 0)).reverse).flatten = rowWord T
  rw [he]
  simpa only [List.map_flatten, List.map_map, Function.comp_def, rowWord] using
    congrArg (List.map (fun c : ℕ × ℕ => T.entry c.1 c.2)) hc

theorem runRows_columns_nonempty (n : ℕ) (rs : List (List (Fin n))) (a : Fin n) :
    (runRows n rs a).columns ≠ [] := by
  cases rs with
  | nil => simp [runRows]
  | cons w ws => simp only [runRows]; split <;> simp

theorem runRows_columns_bound (n : ℕ) (rs : List (List (Fin n))) (a : Fin n) :
    (runRows n rs a).columns.length ≤ rs.length + 1 := by
  induction rs generalizing a with
  | nil => simp [runRows]
  | cons w ws ih =>
    simp only [runRows]
    split
    · simp
    · simpa using Nat.succ_le_succ (ih _)

theorem runRows_count (n : ℕ) (rs : List (List (Fin n))) (a i : Fin n) :
    (runRows n rs a).output.flatten.count i = rs.flatten.count i + if i = a then 1 else 0 := by
  induction rs generalizing a with
  | nil =>
    simp only [runRows, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.count_cons, List.count_nil, beq_iff_eq, Nat.zero_add]
    by_cases h : a = i <;> simp [h, Ne.symm, eq_comm]
  | cons w ws ih =>
    simp only [runRows]
    split
    · simp only [List.flatten_cons, List.count_append, List.count_cons, List.count_nil,
        beq_iff_eq, Nat.zero_add, Nat.add_zero]
      split_ifs <;> omega
    · rename_i u b v hs hu hab hdecision
      simp only [List.flatten_cons, List.count_append, List.count_cons, hs, ih]
      simp only [beq_iff_eq]
      split_ifs <;> omega

theorem runRows_lengths (n : ℕ) (rs : List (List (Fin n))) (a : Fin n) :
    let q := runRows n rs a
    let p := q.columns.length - 1
    q.output.map List.length = (rs.take p).map List.length ++
      [(rs[p]?.getD []).length + 1] ++ (rs.drop (p+1)).map List.length := by
  induction rs generalizing a with
  | nil => simp [runRows]
  | cons w ws ih =>
    simp only [runRows]
    split
    · simp
    · rename_i u b v hs hu hab hdecision
      have hn := List.length_pos_iff.mpr (runRows_columns_nonempty n ws b)
      have he : (runRows n ws b).columns.length =
          ((runRows n ws b).columns.length - 1) + 1 := by omega
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [he]
      simpa [List.take_succ_cons, List.drop_succ_cons, hs,
        Nat.add_assoc] using congrArg (List.cons (u.length + (v.length + 1))) (ih b)

theorem runRows_suffix (n : ℕ) (rs : List (List (Fin n))) (a : Fin n) :
    let q := runRows n rs a
    let p := q.columns.length - 1
    q.output.drop (p+1) = rs.drop (p+1) := by
  induction rs generalizing a with
  | nil => simp [runRows]
  | cons w ws ih =>
    simp only [runRows]
    split
    · simp
    · rename_i u b v hs hu hab hdecision
      have hn := List.length_pos_iff.mpr (runRows_columns_nonempty n ws b)
      have he : (runRows n ws b).columns.length - 1 + 1 =
          (runRows n ws b).columns.length := by omega
      simpa [he] using ih b

theorem runRows_sorted (n : ℕ) (rs : List (List (Fin n))) (a : Fin n)
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·)) :
    ∀ w ∈ (runRows n rs a).output, w.Sorted (· ≤ ·) := by
  induction rs generalizing a with
  | nil => simp [runRows]
  | cons w ws ih =>
    have hw := hs w (by simp)
    have ht := fun z hz => hs z (List.mem_cons_of_mem w hz)
    simp only [runRows]
    split
    · rename_i ha hdecision
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact RowBump.row_append_sorted n w a hw ha
      · exact ht z hz
    · rename_i u b v hsplit hu hab hdecision
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact RowBump.row_bump_sorted n u v a b (hsplit ▸ hw) hu hab
      · exact ih b ht z hz

theorem runRows_crossings (n : ℕ) (rs : List (List (Fin n))) (a : Fin n) :
    let q := runRows n rs a
    let p := q.columns.length - 1
    q.crossings = ((rs.take p).map (fun w => w.length - 1)).sum := by
  induction rs generalizing a with
  | nil => simp [runRows]
  | cons w ws ih =>
    simp only [runRows]
    split
    · simp
    · rename_i u b v hs hu hab hdecision
      have hn := List.length_pos_iff.mpr (runRows_columns_nonempty n ws b)
      have he : (runRows n ws b).columns.length =
          ((runRows n ws b).columns.length - 1) + 1 := by omega
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [he]
      simpa [hs, List.take_succ_cons, Nat.add_assoc] using
        congrArg (fun x => (u.length + v.length) + x) (ih b)

end OddMath.Frontier.TableauRowRecursion
