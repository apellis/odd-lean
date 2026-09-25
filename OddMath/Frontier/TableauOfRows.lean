import OddMath.Frontier.TableauBumpBoundary

/-!
Representation of arbitrary valid finite rows, not insertion-output validity.
The shape is Mathlib's actual ofRowLens; entries are positive labels, zero off shape.
Fulton §1.1, pp. 7–8 supplies the tableau convention, not a separate reconstruction claim.
-/
namespace OddMath.Frontier.TableauOfRows
open TableauSign TableauEvaluation TableauRowStep TableauRowRecursion TableauBumpBoundary

private theorem lengths_anti (n : ℕ) (rs : List (List (Fin n)))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) :
    Antitone (fun r : ℕ => (rs[r]?.getD []).length) :=
  antitone_nat_of_succ_le (fun r => (hc r).choose)

theorem lengths_sorted (n : ℕ) (rs : List (List (Fin n)))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) :
    (rs.map List.length).Sorted (· ≥ ·) := by
  apply List.pairwise_iff_get.mpr
  intro i j hij
  have hi : i.val < rs.length := by simpa using i.isLt
  have hj : j.val < rs.length := by simpa using j.isLt
  have h := lengths_anti n rs hc (le_of_lt hij)
  simpa [List.getElem?_eq_getElem, hi, hj] using h

noncomputable def shape (n : ℕ) (rs : List (List (Fin n)))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) : YoungDiagram :=
  YoungDiagram.ofRowLens (rs.map List.length) (lengths_sorted n rs hc)

theorem shape_mem (n : ℕ) (rs : List (List (Fin n)))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) (r c : ℕ) :
    (r,c) ∈ shape n rs hc ↔ c < (rs[r]?.getD []).length := by
  rw [shape, YoungDiagram.mem_ofRowLens]
  by_cases hr : r < rs.length
  · simp [List.getElem?_eq_getElem, hr]
  · simp [List.getElem?_eq_none (by omega : rs.length ≤ r), hr]

private def label {n : ℕ} (rs : List (List (Fin n))) (r c : ℕ) : ℕ :=
  (((rs[r]?.getD [])[c]?).map (fun x : Fin n => x.val + 1)).getD 0

private theorem label_at {n : ℕ} (rs : List (List (Fin n))) (r c : ℕ)
    (h : c < (rs[r]?.getD []).length) :
    label rs r c = (rs[r]?.getD [])[c].val + 1 := by
  simp [label, List.getElem?_eq_getElem, h]

private theorem all_columns (n : ℕ) (rs : List (List (Fin n)))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD []))
    (i j c : ℕ) (hij : i < j) (hcell : c < (rs[j]?.getD []).length) :
    label rs i c < label rs j c := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hj : c < (rs[j]?.getD []).length := lt_of_lt_of_le hcell (hc j).choose
    have hadj := (hc j).choose_spec c hcell
    have hl : label rs j c < label rs (j+1) c := by
      rw [label_at rs j c hj, label_at rs (j+1) c hcell]
      exact Nat.add_lt_add_right hadj 1
    by_cases he : i = j
    · subst i; exact hl
    · exact lt_trans (ih (by omega) hj) hl

noncomputable def tableau (n : ℕ) (rs : List (List (Fin n)))
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) :
    PositiveTableau (shape n rs hc) where
  entry := label rs
  row_weak' := by
    intro r c d hcd hd
    have hd' := (shape_mem n rs hc r d).mp hd
    have hc' : c < (rs[r]?.getD []).length := lt_trans hcd hd'
    have hr : r < rs.length := by
      by_contra h
      simp [List.getElem?_eq_none (by omega : rs.length ≤ r)] at hd'
    have hs' : (rs[r]?.getD []).Sorted (· ≤ ·) := by
      simpa [List.getElem?_eq_getElem, hr] using hs rs[r] (List.getElem_mem hr)
    have hle := List.pairwise_iff_get.mp hs' ⟨c, hc'⟩ ⟨d, hd'⟩ hcd
    rw [label_at rs r c hc', label_at rs r d hd']
    exact Nat.add_le_add_right hle 1
  col_strict' := by
    intro i j c hij hj
    exact all_columns n rs hc i j c hij ((shape_mem n rs hc j c).mp hj)
  zeros' := by
    intro r c h
    have hc' : (rs[r]?.getD []).length ≤ c := by
      have := (shape_mem n rs hc r c).not.mp h
      omega
    simp [label, List.getElem?_eq_none hc']
  positive := by
    intro r c h
    rw [label_at rs r c ((shape_mem n rs hc r c).mp h)]
    omega

theorem tableau_entry (n : ℕ) (rs : List (List (Fin n)))
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) (r c : ℕ) :
    (tableau n rs hs hc).entry r c =
      (((rs[r]?.getD [])[c]?).map (fun x : Fin n => x.val + 1)).getD 0 := rfl

theorem bounded (n : ℕ) (rs : List (List (Fin n)))
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) :
    InAlphabet n (tableau n rs hs hc) := by
  intro p hp
  have h := (shape_mem n rs hc p.1 p.2).mp hp
  change label rs p.1 p.2 ≤ n
  rw [label_at rs p.1 p.2 h]
  exact (rs[p.1]?.getD [])[p.2].isLt

theorem shape_rowLens (n : ℕ) (rs : List (List (Fin n)))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD []))
    (hn : ∀ w ∈ rs, w ≠ []) : (shape n rs hc).rowLens = rs.map List.length := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact List.length_pos_iff.mpr (hn w hw)

private theorem shape_rowLen (n : ℕ) (rs : List (List (Fin n)))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) (r : ℕ) :
    (shape n rs hc).rowLen r = (rs[r]?.getD []).length := by
  have hh : ∀ c, c < (shape n rs hc).rowLen r ↔ c < (rs[r]?.getD []).length := by
    intro c
    rw [← YoungDiagram.mem_iff_lt_rowLen, shape_mem]
  have h₁ := hh ((shape n rs hc).rowLen r)
  have h₂ := hh ((rs[r]?.getD []).length)
  omega

private theorem extracted_row (n : ℕ) (rs : List (List (Fin n)))
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) (r : ℕ) :
    row n (tableau n rs hs hc) (bounded n rs hs hc) r = rs[r]?.getD [] := by
  apply (List.map_inj_right (f := fun i : Fin n => i.val + 1)
    (by intro a b h; apply Fin.ext; change a.val+1 = b.val+1 at h; omega)).mp
  rw [row_labels]
  apply List.ext_get
  · simp [shape_rowLen]
  · intro c hc₁ hc₂
    have hc' : c < (rs[r]?.getD []).length := by simpa using hc₂
    simpa [List.get_eq_getElem, tableau] using label_at rs r c hc'

theorem rows_tableau (n : ℕ) (rs : List (List (Fin n)))
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD []))
    (hn : ∀ w ∈ rs, w ≠ []) :
    rows n (tableau n rs hs hc) (bounded n rs hs hc) = rs := by
  have hl : (shape n rs hc).colLen 0 = rs.length := by
    simpa using congrArg List.length (shape_rowLens n rs hc hn)
  apply List.ext_get
  · simp [rows_length, hl]
  · intro r hr₁ hr₂
    have hr : r < (shape n rs hc).colLen 0 := by simpa only [rows_length] using hr₁
    simpa [List.get_eq_getElem, rows_get, hr, List.getElem?_eq_getElem, hr₂] using
      extracted_row n rs hs hc r

theorem rowFinWord_tableau (n : ℕ) (rs : List (List (Fin n)))
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD []))
    (hn : ∀ w ∈ rs, w ≠ []) :
    rowFinWord n (tableau n rs hs hc) (bounded n rs hs hc) = readRows rs := by
  rw [← readRows_rows, rows_tableau n rs hs hc hn]

private theorem genuine_row_default (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (r : ℕ) :
    (rows n T hT)[r]?.getD [] = row n T hT r := by
  by_cases hr : r < μ.colLen 0
  · have hr' : r < (rows n T hT).length := by simpa only [rows_length] using hr
    simp [List.getElem?_eq_getElem, hr', rows_get n μ T hT r hr]
  · have hzero : μ.rowLen r = 0 := by
      have hm : (r,0) ∉ μ := by simpa only [YoungDiagram.mem_iff_lt_colLen] using hr
      rw [YoungDiagram.mem_iff_lt_rowLen] at hm
      omega
    have he : row n T hT r = [] := List.length_eq_zero_iff.mp (by rw [row_length, hzero])
    have hb : (rows n T hT).length ≤ r := by rw [rows_length]; omega
    simp [he, List.getElem?_eq_none hb]

private theorem genuine_columns (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) :
    ∀ r : ℕ, ColumnBelow ((rows n T hT)[r]?.getD []) ((rows n T hT)[r+1]?.getD []) := by
  intro r
  rw [genuine_row_default, genuine_row_default]
  exact rows_columnBelow n μ T hT r

private theorem genuine_nonempty (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) :
    ∀ w ∈ rows n T hT, w ≠ [] := by
  intro w hw
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
  have hm : (r,0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (List.mem_range.mp hr)
  have hl := YoungDiagram.mem_iff_lt_rowLen.mp hm
  apply List.length_pos_iff.mp
  simpa only [row_length] using hl

private theorem genuine_label (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (r c : ℕ) :
    label (rows n T hT) r c = T.entry r c := by
  unfold label
  rw [genuine_row_default]
  by_cases hc : c < μ.rowLen r
  · have hc' : c < (row n T hT r).length := by simpa only [row_length] using hc
    have h := congrArg (fun l : List ℕ => l[c]?) (row_labels n μ T hT r)
    simpa [List.getElem?_eq_getElem, hc, hc'] using congrArg (fun x => x.getD 0) h
  · have hc' : (row n T hT r).length ≤ c := by rw [row_length]; omega
    have hz := T.toSemistandardYoungTableau.zeros
      ((YoungDiagram.mem_iff_lt_rowLen).not.mpr hc)
    simpa [List.getElem?_eq_none hc'] using hz.symm

theorem genuine_roundtrip (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) :
    ∃ (hs : ∀ w ∈ rows n T hT, w.Sorted (· ≤ ·))
      (hc : ∀ r : ℕ, ColumnBelow ((rows n T hT)[r]?.getD []) ((rows n T hT)[r+1]?.getD []))
      (_hn : ∀ w ∈ rows n T hT, w ≠ []),
      shape n (rows n T hT) hc = μ ∧
      ∀ r c, (tableau n (rows n T hT) hs hc).entry r c = T.entry r c := by
  refine ⟨rows_sorted n μ T hT, genuine_columns n μ T hT,
    genuine_nonempty n μ T hT, ?_, ?_⟩
  · unfold shape
    simp only [rows_lengths]
    exact YoungDiagram.ofRowLens_to_rowLens_eq_self
  · intro r c
    exact genuine_label n μ T hT r c

end OddMath.Frontier.TableauOfRows
