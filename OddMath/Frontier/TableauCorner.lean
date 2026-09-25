import OddMath.Frontier.TableauInsertion

/-!
Genuine outside-corner restriction. Fulton, Young Tableaux §1.1, printed p.8
(PDF20): an outside corner has no cell immediately below or right.
This removes a cell, not a reverse bumping path; insertion recovery is SHAPE only.
-/
namespace OddMath.Frontier.TableauCorner
open TableauSign TableauEvaluation TableauRowStep TableauRowRecursion

def IsCorner (μ : YoungDiagram) (p : ℕ × ℕ) : Prop :=
  p ∈ μ ∧ (p.1 + 1, p.2) ∉ μ ∧ (p.1, p.2 + 1) ∉ μ

private theorem corner_maximal (μ : YoungDiagram) (p : ℕ × ℕ)
    (hp : IsCorner μ p) (q : ℕ × ℕ) (hq : q ∈ μ) (hle : p ≤ q) : q = p := by
  have hr : q.1 = p.1 := by
    by_contra hn
    exact hp.2.1 (μ.up_left_mem (by have := hle.1; omega) hle.2 hq)
  have hc : q.2 = p.2 := by
    by_contra hn
    exact hp.2.2 (μ.up_left_mem hle.1 (by have := hle.2; omega) hq)
  exact Prod.ext hr hc

noncomputable def eraseShape (μ : YoungDiagram) (p : ℕ × ℕ)
    (hp : IsCorner μ p) : YoungDiagram where
  cells := μ.cells.erase p
  isLowerSet := by
    intro q s hqs hs
    have hs' := Finset.mem_erase.mp hs
    apply Finset.mem_erase.mpr
    refine ⟨?_, μ.isLowerSet hqs hs'.2⟩
    intro he
    subst s
    exact hs'.1 (corner_maximal μ p hp q hs'.2 hqs)

theorem erase_cells (μ : YoungDiagram) (p : ℕ × ℕ) (hp : IsCorner μ p) :
    (eraseShape μ p hp).cells = μ.cells.erase p := rfl

private theorem erase_mem (μ : YoungDiagram) (p : ℕ × ℕ) (hp : IsCorner μ p)
    (q : ℕ × ℕ) : q ∈ eraseShape μ p hp ↔ q ≠ p ∧ q ∈ μ :=
  Finset.mem_erase

noncomputable def eraseTableau (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (_hT : InAlphabet n T) (p : ℕ × ℕ)
    (hp : IsCorner μ p) : PositiveTableau (eraseShape μ p hp) where
  entry r c := if (r,c)=p then 0 else T.entry r c
  row_weak' := by
    intro r c d hcd hd
    have hc := (eraseShape μ p hp).up_left_mem le_rfl hcd.le hd
    rw [if_neg ((erase_mem μ p hp _).mp hc).1,
      if_neg ((erase_mem μ p hp _).mp hd).1]
    exact T.row_weak' hcd ((erase_mem μ p hp _).mp hd).2
  col_strict' := by
    intro r s c hrs hs
    have hr := (eraseShape μ p hp).up_left_mem hrs.le le_rfl hs
    rw [if_neg ((erase_mem μ p hp _).mp hr).1,
      if_neg ((erase_mem μ p hp _).mp hs).1]
    exact T.col_strict' hrs ((erase_mem μ p hp _).mp hs).2
  zeros' := by
    intro r c hc
    by_cases he : (r,c)=p
    · simp [he]
    · rw [if_neg he]
      apply T.zeros'
      intro hm
      exact hc ((erase_mem μ p hp _).mpr ⟨he,hm⟩)
  positive := by
    intro r c hc
    rw [if_neg ((erase_mem μ p hp _).mp hc).1]
    exact T.positive ((erase_mem μ p hp _).mp hc).2

theorem erase_entry (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) (r c : ℕ) :
    (eraseTableau n μ T hT p hp).entry r c = if (r,c)=p then 0 else T.entry r c := rfl

theorem erase_bounded (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) :
    InAlphabet n (eraseTableau n μ T hT p hp) := by
  intro q hq
  rw [erase_entry, if_neg ((erase_mem μ p hp q).mp hq).1]
  exact hT q ((erase_mem μ p hp q).mp hq).2

theorem erase_card (μ : YoungDiagram) (p : ℕ × ℕ) (hp : IsCorner μ p) :
    (eraseShape μ p hp).card + 1 = μ.card := by
  exact Finset.card_erase_add_one hp.1

theorem corner_rowLen (μ : YoungDiagram) (p : ℕ × ℕ) (hp : IsCorner μ p) :
    μ.rowLen p.1 = p.2 + 1 := by
  have hl := YoungDiagram.mem_iff_lt_rowLen.mp hp.1
  have hu := (YoungDiagram.mem_iff_lt_rowLen).not.mp hp.2.2
  omega

private theorem erase_rowLen (μ : YoungDiagram) (p : ℕ × ℕ)
    (hp : IsCorner μ p) (r : ℕ) :
    (eraseShape μ p hp).rowLen r = if r = p.1 then p.2 else μ.rowLen r := by
  have hc (c : ℕ) : c < (eraseShape μ p hp).rowLen r ↔
      c < (if r = p.1 then p.2 else μ.rowLen r) := by
    rw [← YoungDiagram.mem_iff_lt_rowLen, erase_mem]
    rw [YoungDiagram.mem_iff_lt_rowLen]
    by_cases hr : r = p.1
    · simp only [hr, if_pos, ne_eq, Prod.ext_iff, Prod.fst, Prod.snd, true_and,
        corner_rowLen μ p hp, eq_self]
      omega
    · simp [Prod.ext_iff, hr]
  have h₁ := hc ((eraseShape μ p hp).rowLen r)
  have h₂ := hc (if r = p.1 then p.2 else μ.rowLen r)
  omega

theorem erase_row (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) (r : ℕ) :
    row n (eraseTableau n μ T hT p hp) (erase_bounded n μ T hT p hp) r =
      if r = p.1 then (row n T hT r).take p.2 else row n T hT r := by
  apply (List.map_inj_right (f := fun i : Fin n => i.val + 1)
    (by intro a b h; apply Fin.ext; change a.val+1 = b.val+1 at h; omega)).mp
  rw [row_labels]
  by_cases hr : r = p.1
  · rw [if_pos hr, List.map_take, row_labels, ← List.map_take]
    rw [List.take_range, hr, corner_rowLen μ p hp]
    simp only [erase_rowLen, hr, if_pos, Nat.min_eq_left (Nat.le_succ _)]
    apply List.map_congr_left
    intro c hc
    rw [erase_entry, if_neg]
    have hc' := List.mem_range.mp hc
    intro he
    have he' := congrArg Prod.snd he
    simp only [Prod.snd] at he'
    omega
  · rw [if_neg hr, row_labels, erase_rowLen, if_neg hr]
    apply List.map_congr_left
    intro c _
    rw [erase_entry, if_neg]
    intro he
    exact hr (congrArg Prod.fst he)

-- Any longer enumeration is harmless only after proving its extra rows empty.
private theorem rows_filter_range (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (k : ℕ) (hk : μ.colLen 0 ≤ k) :
    (((List.range k).map (row n T hT)).filter (fun w => !w.isEmpty)) = rows n T hT := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero =>
    simp only [Nat.add_zero]
    change (rows n T hT).filter (fun w => !w.isEmpty) = rows n T hT
    apply List.filter_eq_self.mpr
    intro w hw
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
    have hm : (r,0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (List.mem_range.mp hr)
    have hl : 0 < (row n T hT r).length := by
      rw [row_length]
      exact YoungDiagram.mem_iff_lt_rowLen.mp hm
    have hn := List.ne_nil_of_length_pos hl
    simpa using hn
  | succ d ih =>
    have he : row n T hT (μ.colLen 0 + d) = [] := by
      apply List.length_eq_zero_iff.mp
      rw [row_length]
      have hn : (μ.colLen 0 + d,0) ∉ μ := by
        rw [YoungDiagram.mem_iff_lt_colLen]
        omega
      rw [YoungDiagram.mem_iff_lt_rowLen] at hn
      omega
    rw [Nat.add_succ, List.range_succ, List.map_append, List.filter_append]
    simpa only [List.map_cons, List.map_nil, he, List.filter_cons, List.isEmpty_nil,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil] using ih

theorem erase_rows (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) :
    rows n (eraseTableau n μ T hT p hp) (erase_bounded n μ T hT p hp) =
      (((rows n T hT).mapIdx (fun r w => if r = p.1 then w.take p.2 else w)).filter
        (fun w => !w.isEmpty)) := by
  have hh : (eraseShape μ p hp).colLen 0 ≤ μ.colLen 0 := by
    by_contra hn
    have hc : (μ.colLen 0,0) ∈ eraseShape μ p hp :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hm := ((erase_mem μ p hp _).mp hc).2
    rw [YoungDiagram.mem_iff_lt_colLen] at hm
    exact (Nat.lt_irrefl _) hm
  have he : (rows n T hT).mapIdx (fun r w => if r = p.1 then w.take p.2 else w) =
      (List.range (μ.colLen 0)).map
        (row n (eraseTableau n μ T hT p hp) (erase_bounded n μ T hT p hp)) := by
    apply List.ext_get
    · simp [rows]
    · intro r hr₁ hr₂
      simp [List.get_eq_getElem, rows, erase_row]
  rw [he]
  exact (rows_filter_range n _ _ _ _ hh).symm

theorem insert_newCell_corner (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (a : Fin n) :
    IsCorner (TableauInsertion.insert n μ T hT a).shape
      (TableauInsertion.insert n μ T hT a).newCell := by
  let I := TableauInsertion.insert n μ T hT a
  have hc := TableauInsertion.insert_cells n μ T hT a
  change I.newCell ∉ μ.cells ∧ I.shape.cells = TableauInsertion.insertCell I.newCell μ.cells at hc
  have hm (q : ℕ × ℕ) : q ∈ I.shape ↔ q = I.newCell ∨ q ∈ μ := by
    change q ∈ I.shape.cells ↔ _
    rw [hc.2]
    exact Finset.mem_insert
  refine ⟨(hm _).mpr (Or.inl rfl), ?_, ?_⟩
  · intro h
    rcases (hm _).mp h with he | he
    · have he' := congrArg Prod.fst he
      change I.newCell.1 + 1 = I.newCell.1 at he'
      omega
    · exact hc.1 (μ.up_left_mem (Nat.le_succ _) le_rfl he)
  · intro h
    rcases (hm _).mp h with he | he
    · have he' := congrArg Prod.snd he
      change I.newCell.2 + 1 = I.newCell.2 at he'
      omega
    · exact hc.1 (μ.up_left_mem le_rfl (Nat.le_succ _) he)

theorem erase_insert_shape (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (a : Fin n) :
    eraseShape (TableauInsertion.insert n μ T hT a).shape
      (TableauInsertion.insert n μ T hT a).newCell (insert_newCell_corner n μ T hT a) = μ := by
  apply YoungDiagram.ext
  rw [erase_cells, (TableauInsertion.insert_cells n μ T hT a).2]
  exact Finset.erase_insert (TableauInsertion.insert_cells n μ T hT a).1

#print axioms corner_maximal
#print axioms erase_mem
#print axioms erase_rowLen
#print axioms rows_filter_range
end OddMath.Frontier.TableauCorner
