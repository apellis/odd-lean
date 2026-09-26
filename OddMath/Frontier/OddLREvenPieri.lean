import OddMath.Frontier.OddLREvenRule

/-!
# The even Pieri rules

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), §4.1, Example 4.2 and
display (4.3), p.12, in the ring of symmetric functions `Λ₁` (`OddLREven.Sym`):

* `hk_eq_sE_row`: `h_k = s_{(k)}`;
* `pieri_row` (4.3): `s_μ s_{(k)} = Σ_{λ/μ horizontal strip} s_λ`;
* `card_lr_row`: "on any skew shape `λ/μ` there is exactly one [Littlewood–Richardson] tableau of
  content `(k)`" if `λ/μ` is a horizontal strip, and none otherwise, so
  `c^λ_{μ(k)} = 1` for horizontal strips and `0` otherwise (`evenLR_row`);
* `card_lr_column`, `evenLR_column`, `pieri_column`: the same with `(1^k)` and vertical strips
  ("the same is true if `(k)` is replaced by `(1^k)` and 'horizontal' is replaced by
  'vertical'"). Here the Littlewood–Richardson tableaux of content `(1^k)` are exactly the
  fillings of a vertical strip by `1, …, k` from top to bottom (row word `k ⋯ 2 1`).
-/

namespace OddMath.Frontier.OddLREven

open scoped BigOperators
open DegreeShapes TableauSign TableauContent OddLRTableau OddLRRule TableauStripCorners
open TableauExtremal (rowShape columnShape)
open OddLRVerticalPieri (Vertical)

noncomputable section

attribute [local instance] degreeFintype Classical.propDecidable

/-! ## Rows: `h_k = s_{(k)}` and the horizontal Pieri rule -/

theorem card_row (k : ℕ) : (rowShape k).card = k := by
  simp [YoungDiagram.card, TableauExtremal.rowShape]

theorem card_column (k : ℕ) : (columnShape k).card = k := by
  simp [YoungDiagram.card, TableauExtremal.columnShape]

theorem rowLens_row {k : ℕ} (hk : 0 < k) : (rowShape k).rowLens = [k] := by
  have hc : (rowShape k).colLen 0 = 1 := by
    have h1 : 0 < (rowShape k).colLen 0 :=
      YoungDiagram.mem_iff_lt_colLen.mp ((TableauExtremal.mem_rowShape k 0 0).mpr ⟨rfl, hk⟩)
    have h2 : ¬ 1 < (rowShape k).colLen 0 := fun h => by
      have := (TableauExtremal.mem_rowShape k 1 0).mp (YoungDiagram.mem_iff_lt_colLen.mpr h)
      omega
    omega
  have hr : (rowShape k).rowLen 0 = k := by
    apply le_antisymm
    · by_contra h
      push_neg at h
      have := (TableauExtremal.mem_rowShape k 0 k).mp (YoungDiagram.mem_iff_lt_rowLen.mpr h)
      omega
    · by_contra h
      push_neg at h
      have := (TableauExtremal.mem_rowShape k 0 ((rowShape k).rowLen 0)).mpr ⟨rfl, h⟩
      exact lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp this)
  unfold YoungDiagram.rowLens
  rw [hc]; simp [List.range_succ, hr]

theorem rowLens_row_zero : (rowShape 0).rowLens = [] := by
  have hc : (rowShape 0).colLen 0 = 0 := by
    by_contra h
    have := (TableauExtremal.mem_rowShape 0 0 0).mp
      (YoungDiagram.mem_iff_lt_colLen.mpr (show 0 < (rowShape 0).colLen 0 by omega))
    omega
  unfold YoungDiagram.rowLens
  rw [hc]; rfl

theorem hE_row (k : ℕ) : hE (rowShape k) = hk k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [hE, rowLens_row_zero, hk_zero]; simp [EKGeneralQ.hWord]
  · rw [hE, rowLens_row hk0]; simp [EKGeneralQ.hWord, hk]

/-- A diagram of size `k` with `k` cells in its first row is the row `(k)`. -/
theorem eq_row_of_prefix {nu : YoungDiagram} {k : ℕ} (hc : nu.card = k)
    (h : k ≤ TableauDominance.shapePrefix nu 1) : nu = rowShape k := by
  have hsub : nu.cells.filter (fun p => p.1 < 1) = nu.cells := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    change nu.card ≤ _
    rw [hc]; exact h
  have hrow : ∀ p ∈ nu.cells, p.1 = 0 := by
    intro p hp
    rw [← hsub] at hp
    have := (Finset.mem_filter.mp hp).2
    omega
  have hle : nu.cells ⊆ (rowShape k).cells := by
    intro p hp
    have h0 := hrow p hp
    rw [YoungDiagram.mem_cells, show p = (p.1, p.2) from rfl, TableauExtremal.mem_rowShape]
    refine ⟨h0, ?_⟩
    have hp' : (0, p.2) ∈ nu := by rw [← h0]; simpa using hp
    have h1 := YoungDiagram.mem_iff_lt_rowLen.mp hp'
    have h2 : nu.rowLen 0 ≤ nu.card := by
      rw [YoungDiagram.rowLen_eq_card]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    omega
  apply YoungDiagram.ext
  apply Finset.eq_of_subset_of_card_le hle
  change (rowShape k).card ≤ nu.card
  rw [card_row, hc]

theorem K_row (k : ℕ) (nu : DegreeShape k) :
    K k nu ⟨rowShape k, card_row k⟩ = if nu.val = rowShape k then 1 else 0 := by
  rw [K_apply]
  dsimp only
  split_ifs with h
  · rw [h, TableauDominance.diagonal_fiber]; simp
  · rw [TableauDominance.fiber_empty_of_prefix]
    · simp
    · refine ⟨1, ?_⟩
      rw [TableauDominance.shapeContent_prefix]
      by_contra hn
      push_neg at hn
      apply h
      apply eq_row_of_prefix nu.property
      have : TableauDominance.shapePrefix (rowShape k) 1 = k := by
        unfold TableauDominance.shapePrefix
        rw [Finset.filter_true_of_mem (fun p hp => by
          have := (TableauExtremal.mem_rowShape k p.1 p.2).mp (by simpa using hp)
          omega)]
        exact card_row k
      omega

/-- `h_k = s_{(k)}` in `Λ₁`. -/
theorem hk_eq_sE_row (k : ℕ) : hk k = sE (rowShape k) := by
  rw [← hE_row, hE_expand k ⟨rowShape k, card_row k⟩]
  rw [Fintype.sum_eq_single (α := DegreeShape k) ⟨rowShape k, card_row k⟩]
  · rw [K_row, if_pos rfl, one_smul]
  · intro nu hnu
    rw [K_row, if_neg (fun h => hnu (Subtype.ext h)), zero_smul]

/-- **E (4.3), the even Pieri rule**: `s_μ s_{(k)} = Σ_{λ/μ horizontal strip} s_λ`. -/
theorem pieri_row (mu : YoungDiagram) (k : ℕ) :
    sE mu * sE (rowShape k) = ∑ lam : DegreeShape (mu.card + k),
      if Horizontal mu lam.val then sE lam.val else 0 := by
  rw [← hk_eq_sE_row]
  exact sE_mul_hk mu.card k ⟨mu, rfl⟩

theorem repr_sum_ite {d : ℕ} (P : YoungDiagram → Prop) (lam : YoungDiagram) :
    sBasisE.repr (∑ w : DegreeShape d, if P w.val then sE w.val else 0) lam =
      if P lam ∧ lam.card = d then 1 else 0 := by
  rw [map_sum, Finset.sum_apply']
  have e : ∀ w : DegreeShape d, sBasisE.repr (if P w.val then sE w.val else 0) lam =
      if w.val = lam ∧ P lam then 1 else 0 := by
    intro w
    split_ifs with h1 h2 h2
    · rw [← sBasisE_apply, Basis.repr_self, Finsupp.single_apply, if_pos h2.1]
    · rw [← sBasisE_apply, Basis.repr_self, Finsupp.single_apply, if_neg]
      intro h
      exact h2 ⟨h, by rw [← h]; exact h1⟩
    · exact absurd (by rw [h2.1]; exact h2.2) h1
    · simp
  simp_rw [e]
  by_cases hd : lam.card = d
  · rw [Fintype.sum_eq_single (α := DegreeShape d) ⟨lam, hd⟩]
    · simp [hd]
    · intro w hw
      rw [if_neg (fun h => hw (Subtype.ext h.1))]
  · rw [if_neg (fun h => hd h.2)]
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg (fun h => hd (by rw [← h.1]; exact w.property))]

/-- E Example 4.2: `c^λ_{μ(k)} = 1` if `λ/μ` is a horizontal strip of size `k`, else `0`. -/
theorem evenLR_row (lam mu : YoungDiagram) (k : ℕ) :
    evenLR lam mu (rowShape k) = if Horizontal mu lam ∧ lam.card = mu.card + k then 1 else 0 := by
  unfold evenLR
  rw [pieri_row, repr_sum_ite]

/-- E Example 4.2: on a skew shape `λ/μ` there is exactly one Littlewood–Richardson tableau of
content `(k)` if `λ/μ` is a horizontal strip with `k` cells, and none otherwise. -/
theorem card_lr_row (lam mu : YoungDiagram) (k : ℕ) :
    (lrTableaux lam mu (rowShape k)).card =
      if Horizontal mu lam ∧ lam.card = mu.card + k then 1 else 0 := by
  have := evenLR_row lam mu k
  rw [thm_4_1] at this
  split_ifs at this ⊢ <;> exact_mod_cast this

/-! ## Columns: the vertical Pieri rule -/

/-- `[m, m-1, …, 1]`. -/
def desc (m : ℕ) : List ℕ := (List.range m).reverse.map (· + 1)

theorem desc_succ (m : ℕ) : desc (m + 1) = (m + 1) :: desc m := by
  simp [desc, List.range_succ]

theorem length_desc (m : ℕ) : (desc m).length = m := by simp [desc]

theorem mem_desc {m a : ℕ} : a ∈ desc m ↔ 0 < a ∧ a ≤ m := by
  simp only [desc, List.mem_map, List.mem_reverse, List.mem_range]
  constructor
  · rintro ⟨b, hb, rfl⟩; omega
  · intro h; exact ⟨a - 1, by omega, by omega⟩

theorem nodup_desc (m : ℕ) : (desc m).Nodup := by
  unfold desc
  exact (List.nodup_reverse.mpr List.nodup_range).map (fun a b h => by omega)

theorem count_desc (m a : ℕ) : (desc m).count a = if 0 < a ∧ a ≤ m then 1 else 0 := by
  rw [List.count_eq_of_nodup (nodup_desc m)]
  simp [mem_desc]

theorem getElem_desc (m i : ℕ) (h : i < (desc m).length) : (desc m)[i] = m - i := by
  simp only [desc, List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
  simp only [length_desc] at h
  omega

theorem yamanouchi_desc (m : ℕ) : Yamanouchi (desc m) := by
  intro t ht a b ha hab
  obtain ⟨u, hu⟩ := ht
  -- every suffix of `desc m` is some `desc j`
  have key : ∀ m u t, u ++ t = desc m → t = desc t.length := by
    intro m
    induction m with
    | zero => intro u t h; simp [desc] at h; rw [h.2]; simp [desc]
    | succ m ih =>
      intro u t h
      rw [desc_succ] at h
      rcases u with _ | ⟨x, u⟩
      · simp only [List.nil_append] at h
        rw [h, List.length_cons, length_desc, desc_succ]
      · simp only [List.cons_append, List.cons.injEq] at h
        exact ih u t h.2
  rw [key m u t hu, count_desc, count_desc]
  split_ifs <;> omega

/-- A repetition-free positive Yamanouchi word is `[m, m-1, …, 1]`. -/
theorem eq_desc : ∀ (w : List ℕ), w.Nodup → (∀ a ∈ w, 0 < a) → Yamanouchi w → w = desc w.length
  | [], _, _, _ => by simp [desc]
  | a :: w, hn, hp, hy => by
    have hw : w = desc w.length := eq_desc w (List.nodup_cons.mp hn).2
      (fun b hb => hp b (List.mem_cons_of_mem _ hb))
      (fun t ht => hy t (ht.trans (List.suffix_cons a w)))
    have hnot : a ∉ w := (List.nodup_cons.mp hn).1
    have ha := hp a List.mem_cons_self
    have hmem : ∀ x, x ∈ w ↔ 0 < x ∧ x ≤ w.length := fun x => by
      conv_lhs => rw [hw]
      exact mem_desc
    have hle : a ≤ w.length + 1 := by
      by_contra hlt
      push_neg at hlt
      have h1 := hy (a :: w) (List.suffix_refl _) (w.length + 1) a (by omega) hlt
      have h2 : (a :: w).count a = 1 := by
        simp [List.count_cons_self, List.count_eq_zero_of_not_mem hnot]
      have h3 : (a :: w).count (w.length + 1) = 0 := by
        apply List.count_eq_zero_of_not_mem
        intro hm
        rcases List.mem_cons.mp hm with h | h
        · omega
        · have := (hmem _).mp h; omega
      omega
    have hgt : w.length < a := by
      by_contra hle'
      exact hnot ((hmem a).mpr ⟨ha, by omega⟩)
    rw [List.length_cons, desc_succ, show a = w.length + 1 by omega]
    exact congrArg _ hw

/-- The cells of `λ/μ` in reading order. -/
def cellsL (lam mu : YoungDiagram) : List (ℕ × ℕ) :=
  (TableauRowWord.rowCells lam).filter (fun p => p ∉ mu.cells)

theorem cellsL_nodup (lam mu : YoungDiagram) : (cellsL lam mu).Nodup :=
  (TableauRowWord.rowCells_nodup lam).filter _

theorem cellsL_sorted (lam mu : YoungDiagram) : (cellsL lam mu).Sorted TableauRowWord.RowLE :=
  (TableauRowWord.rowCells_sorted lam).filter _

theorem mem_cellsL {lam mu : YoungDiagram} {p : ℕ × ℕ} : p ∈ cellsL lam mu ↔ p ∈ lam ∧ p ∉ mu := by
  simp [cellsL, TableauRowWord.mem_rowCells]

theorem length_cellsL {lam mu : YoungDiagram} (h : mu ≤ lam) :
    (cellsL lam mu).length = lam.card - mu.card := by
  rw [← List.toFinset_card_of_nodup (cellsL_nodup lam mu)]
  have : (cellsL lam mu).toFinset = skewCells lam mu := by
    ext p; simp [mem_cellsL, mem_skewCells]
  rw [this, skewCells, Finset.card_sdiff (YoungDiagram.cells_subset_iff.mpr h)]

theorem rowWord_eq_map (S : SkewTableau lam mu) :
    S.rowWord = (cellsL lam mu).map (fun p => S.entry p.1 p.2) := rfl

/-- Position of a cell in a list of cells. -/
def idx (l : List (ℕ × ℕ)) (p : ℕ × ℕ) : ℕ :=
  letI : BEq (ℕ × ℕ) := instBEqOfDecidableEq
  l.idxOf p

theorem idx_lt {l : List (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p ∈ l) : idx l p < l.length :=
  List.idxOf_lt_length_iff.mpr hp

theorem getElem_idx {l : List (ℕ × ℕ)} {p : ℕ × ℕ} (h : idx l p < l.length) :
    l[idx l p] = p :=
  List.getElem_idxOf h

theorem idx_getElem {l : List (ℕ × ℕ)} (hn : l.Nodup) (i : ℕ) (h : i < l.length) :
    idx l l[i] = i :=
  List.idxOf_getElem hn i h

theorem idxOf_lt_of_rowLE {l : List (ℕ × ℕ)} (hs : l.Sorted TableauRowWord.RowLE)
    {p q : ℕ × ℕ} (hp : p ∈ l) (hq : q ∈ l) (hpq : TableauRowWord.RowLE p q)
    (hne : p ≠ q) : idx l p < idx l q := by
  have hip := idx_lt hp
  have hiq := idx_lt hq
  by_contra h
  rcases lt_or_eq_of_le (not_lt.mp h) with h' | h'
  · have := hs.rel_get_of_lt (a := ⟨idx l q, hiq⟩) (b := ⟨idx l p, hip⟩) h'
    simp only [List.get_eq_getElem, getElem_idx] at this
    exact hne (antisymm hpq this)
  · apply hne
    have e1 := getElem_idx hip
    have e2 := getElem_idx hiq
    rw [← e1, ← e2]
    simp only [h']

theorem entry_eq_getElem (S : SkewTableau lam mu) {p : ℕ × ℕ} (hp : p ∈ cellsL lam mu) :
    S.entry p.1 p.2 = S.rowWord[idx (cellsL lam mu) p]'(by
      rw [rowWord_eq_map, List.length_map]; exact idx_lt hp) := by
  simp only [rowWord_eq_map, List.getElem_map, getElem_idx]

theorem content_column (k a : ℕ) :
    TableauDominance.shapeContent (columnShape k) a = if 0 < a ∧ a ≤ k then 1 else 0 := by
  simp only [TableauDominance.shapeContent, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [← Finset.card_filter]
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨(a - 1, 0), ?_⟩
    ext p
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, he⟩
      rw [show p = (p.1, p.2) from rfl, TableauExtremal.mem_columnShape] at hp
      exact Prod.ext (by show p.1 = a - 1; omega) (by show p.2 = 0; omega)
    · rintro rfl
      exact ⟨(TableauExtremal.mem_columnShape k _ _).mpr ⟨rfl, by omega⟩, by omega⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp
    have := (TableauExtremal.mem_columnShape k p.1 p.2).mp (by simpa using hp)
    omega

/-- The row word of a Littlewood–Richardson tableau of content `(1^k)` is `[k, …, 1]`. -/
theorem rowWord_of_lr_column {S : SkewTableau lam mu} (hS : S ∈ lrTableaux lam mu (columnShape k)) :
    S.rowWord = desc S.rowWord.length := by
  obtain ⟨hc, hy⟩ := mem_lrTableaux.mp hS
  apply eq_desc _ _ _ hy
  · rw [List.nodup_iff_count_le_one]
    intro a
    rw [← skew_content_eq_count, hc, content_column]
    split_ifs <;> omega
  · intro a ha
    rw [rowWord_eq_map] at ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    obtain ⟨h1, h2⟩ := mem_cellsL.mp hp
    exact S.positive h1 h2

theorem vertical_of_lr_column {S : SkewTableau lam mu}
    (hS : S ∈ lrTableaux lam mu (columnShape k)) : Vertical mu lam := by
  refine ⟨YoungDiagram.cells_subset_iff.mpr S.sub, ?_⟩
  have hw := rowWord_of_lr_column hS
  -- two cells in the same row, the first strictly left of the second, are impossible
  have key : ∀ p q : ℕ × ℕ, p ∈ lam → p ∉ mu → q ∈ lam → q ∉ mu → p.1 = q.1 → p.2 < q.2 → False := by
    intro p q hp hp' hq hq' h1 h2
    have hr := S.row_weak (i := p.1) h2 (by rw [h1]; exact hq) hp'
    have hpl : p ∈ cellsL lam mu := mem_cellsL.mpr ⟨hp, hp'⟩
    have hql : q ∈ cellsL lam mu := mem_cellsL.mpr ⟨hq, hq'⟩
    have hlt := idxOf_lt_of_rowLE (cellsL_sorted lam mu) hpl hql
      (Or.inr ⟨h1, h2.le⟩) (fun h => by rw [h] at h2; exact lt_irrefl _ h2)
    have ep := entry_eq_getElem S hpl
    have eq := entry_eq_getElem S hql
    have hql' : idx (cellsL lam mu) q < S.rowWord.length := by
      rw [rowWord_eq_map, List.length_map]; exact idx_lt hql
    have hval : ∀ i (h : i < S.rowWord.length), S.rowWord[i] = S.rowWord.length - i := by
      intro i h
      rw [List.getElem_of_eq hw h, getElem_desc]
    rw [hval] at ep eq
    rw [← h1] at eq
    rw [ep, eq] at hr
    omega
  intro p hp q hq hpq
  simp only [Finset.mem_sdiff, YoungDiagram.mem_cells] at hp hq
  rcases lt_trichotomy p.2 q.2 with h | h | h
  · exact (key p q hp.1 hp.2 hq.1 hq.2 hpq h).elim
  · exact Prod.ext hpq h
  · exact (key q p hq.1 hq.2 hp.1 hp.2 hpq.symm h).elim

/-- The filling of a vertical strip by `1, …, k` from top to bottom. -/
def colEntry (lam mu : YoungDiagram) (k i j : ℕ) : ℕ :=
  if (i, j) ∈ lam ∧ (i, j) ∉ mu then k - idx (cellsL lam mu) (i, j) else 0

theorem idxOf_lt_k {lam mu : YoungDiagram} {k : ℕ} (hsub : mu ≤ lam)
    (hk : lam.card = mu.card + k) {p : ℕ × ℕ} (hp : p ∈ cellsL lam mu) :
    idx (cellsL lam mu) p < k := by
  have := idx_lt hp
  rw [length_cellsL hsub] at this
  omega

/-- The unique Littlewood–Richardson tableau of content `(1^k)` on a vertical strip. -/
def colTab (lam mu : YoungDiagram) (k : ℕ) (hv : Vertical mu lam) (hk : lam.card = mu.card + k) :
    SkewTableau lam mu where
  entry := colEntry lam mu k
  sub := YoungDiagram.cells_subset_iff.mp hv.1
  row_weak := by
    intro i j₁ j₂ hj h h1
    exfalso
    have h1' : (i, j₁) ∈ lam := lam.up_left_mem le_rfl hj.le h
    have h2' : (i, j₂) ∉ mu := fun hm => h1 (mu.up_left_mem le_rfl hj.le hm)
    have := hv.2 (i, j₁) (by simp [h1', h1]) (i, j₂) (by simp [h, h2']) rfl
    simp at this; omega
  col_strict := by
    intro i₁ i₂ j hi h h1
    have hsub := YoungDiagram.cells_subset_iff.mp hv.1
    have h1' : (i₁, j) ∈ lam := lam.up_left_mem hi.le le_rfl h
    have h2' : (i₂, j) ∉ mu := fun hm => h1 (mu.up_left_mem hi.le le_rfl hm)
    have hp1 : (i₁, j) ∈ cellsL lam mu := mem_cellsL.mpr ⟨h1', h1⟩
    have hp2 : (i₂, j) ∈ cellsL lam mu := mem_cellsL.mpr ⟨h, h2'⟩
    have hlt := idxOf_lt_of_rowLE (cellsL_sorted lam mu) hp2 hp1
      (Or.inl hi) (fun h => by simp only [Prod.mk.injEq] at h; omega)
    have := idxOf_lt_k hsub hk hp1
    simp only [colEntry, if_pos (And.intro h1' h1), if_pos (And.intro h h2')]
    omega
  zeros_out := by
    intro i j h
    simp [colEntry, h]
  zeros_in := by
    intro i j h
    simp [colEntry, h]
  positive := by
    intro i j h h'
    have := idxOf_lt_k (YoungDiagram.cells_subset_iff.mp hv.1) hk (mem_cellsL.mpr ⟨h, h'⟩)
    simp only [colEntry, if_pos (And.intro h h')]
    omega

theorem rowWord_colTab (lam mu : YoungDiagram) (k : ℕ) (hv : Vertical mu lam)
    (hk : lam.card = mu.card + k) : (colTab lam mu k hv hk).rowWord = desc k := by
  have hsub : mu ≤ lam := YoungDiagram.cells_subset_iff.mp hv.1
  have hlen : (cellsL lam mu).length = k := by rw [length_cellsL hsub]; omega
  apply List.ext_getElem
  · rw [rowWord_eq_map, List.length_map, hlen, length_desc]
  · intro i h1 h2
    rw [getElem_desc]
    simp only [rowWord_eq_map, List.getElem_map]
    have hm : (cellsL lam mu)[i]'(by rw [rowWord_eq_map, List.length_map] at h1; exact h1) ∈
        cellsL lam mu := List.getElem_mem _
    obtain ⟨hl, hm'⟩ := mem_cellsL.mp hm
    change colEntry lam mu k _ _ = _
    rw [colEntry, if_pos ⟨hl, hm'⟩, idx_getElem (cellsL_nodup lam mu)]

theorem colTab_mem (lam mu : YoungDiagram) (k : ℕ) (hv : Vertical mu lam)
    (hk : lam.card = mu.card + k) : colTab lam mu k hv hk ∈ lrTableaux lam mu (columnShape k) := by
  rw [mem_lrTableaux]
  refine ⟨?_, ?_⟩
  · ext a
    rw [skew_content_eq_count, rowWord_colTab, count_desc, content_column]
  · unfold IsLR
    rw [rowWord_colTab]
    exact yamanouchi_desc k

theorem eq_of_lr_column {S S' : SkewTableau lam mu} (hS : S ∈ lrTableaux lam mu (columnShape k))
    (hS' : S' ∈ lrTableaux lam mu (columnShape k)) : S = S' := by
  have hw := rowWord_of_lr_column hS
  have hw' := rowWord_of_lr_column hS'
  have hl : S.rowWord.length = S'.rowWord.length := by
    rw [rowWord_eq_map, rowWord_eq_map, List.length_map, List.length_map]
  have he : S.rowWord = S'.rowWord := by rw [hw, hw', hl]
  rw [rowWord_eq_map, rowWord_eq_map, List.map_inj_left] at he
  apply SkewTableau.ext_skew
  intro p hp
  exact he p (mem_cellsL.mpr (mem_skewCells.mp hp))

/-- E Example 4.2, vertical form: on a skew shape `λ/μ` there is exactly one
Littlewood–Richardson tableau of content `(1^k)` if `λ/μ` is a vertical strip with `k` cells,
and none otherwise. -/
theorem card_lr_column (lam mu : YoungDiagram) (k : ℕ) :
    (lrTableaux lam mu (columnShape k)).card =
      if Vertical mu lam ∧ lam.card = mu.card + k then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    exact ⟨colTab lam mu k h.1 h.2, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨colTab_mem lam mu k h.1 h.2, fun S hS => eq_of_lr_column hS (colTab_mem lam mu k h.1 h.2)⟩⟩
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
    intro S hS
    apply h
    refine ⟨vertical_of_lr_column hS, ?_⟩
    by_contra hc
    rw [lrTableaux_eq_empty (by rw [card_column]; exact hc)] at hS
    simp at hS

/-- `c^λ_{μ(1^k)} = 1` if `λ/μ` is a vertical strip of size `k`, else `0`. -/
theorem evenLR_column (lam mu : YoungDiagram) (k : ℕ) :
    evenLR lam mu (columnShape k) = if Vertical mu lam ∧ lam.card = mu.card + k then 1 else 0 := by
  rw [thm_4_1, card_lr_column]
  split_ifs <;> simp

/-- **E (4.3), vertical form**: `s_μ s_{(1^k)} = Σ_{λ/μ vertical strip} s_λ`. -/
theorem pieri_column (mu : YoungDiagram) (k : ℕ) :
    sE mu * sE (columnShape k) = ∑ lam : DegreeShape (mu.card + k),
      if Vertical mu lam.val then sE lam.val else 0 := by
  apply sBasisE.repr.injective
  ext lam
  rw [repr_sum_ite]
  change evenLR lam mu (columnShape k) = _
  rw [evenLR_column]

end

end OddMath.Frontier.OddLREven
