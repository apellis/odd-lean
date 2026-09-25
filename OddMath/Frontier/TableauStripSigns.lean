import OddMath.Frontier.TableauWordInsertion

namespace OddMath.Frontier.TableauStripSigns
open scoped BigOperators
abbrev State (n : ℕ) := TableauWordInsertion.State n

def north (μ : YoungDiagram) : ℕ :=
  ∑ p ∈ μ.cells, (μ.cells.filter (fun q => q.1 < p.1)).card
def directNorth (μ : YoungDiagram) : ℕ :=
  ∑ p ∈ μ.cells, (μ.cells.filter (fun q => q.1 < p.1 ∧ q.2 = p.2)).card
def northEast (μ : YoungDiagram) : ℕ :=
  ∑ p ∈ μ.cells, (μ.cells.filter (fun q => q.1 < p.1 ∧ p.2 < q.2)).card
def northWest (μ : YoungDiagram) : ℕ :=
  ∑ p ∈ μ.cells, (μ.cells.filter (fun q => q.1 < p.1 ∧ q.2 < p.2)).card
def rightCount (μ : YoungDiagram) (c : ℕ) : ℕ :=
  (μ.cells.filter (fun q => c < q.2)).card
noncomputable def crossings (n : ℕ) : State n → List (Fin n) → ℕ
  | _, [] => 0
  | S, a :: w =>
    let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
    I.crossings + crossings n ⟨I.shape, ⟨I.tableau, I.bounded⟩⟩ w
def stripRight (μ : YoungDiagram) (ps : List (ℕ × ℕ)) : ℕ :=
  (ps.map (fun p => rightCount μ p.2)).sum

/-! Ellis 1111.3932v1 §2.2 and Prop. 3.7 proof (3.8), pointwise only.
English cells; strict directional comparisons; chronological weak row.
No aggregate Pieri, kernel, or source-ledger promotion is asserted. -/
private theorem count_partition (s : Finset (ℕ × ℕ)) (p : ℕ × ℕ) :
    (s.filter (fun q => q.1 < p.1)).card =
      (s.filter (fun q => q.1 < p.1 ∧ q.2 < p.2)).card +
      (s.filter (fun q => q.1 < p.1 ∧ q.2 = p.2)).card +
      (s.filter (fun q => q.1 < p.1 ∧ p.2 < q.2)).card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> omega

theorem shape_partition (μ : YoungDiagram) :
    directNorth μ + north μ + northEast μ =
      northWest μ + 2 * (directNorth μ + northEast μ) := by
  have h : north μ = northWest μ + directNorth μ + northEast μ := by
    unfold north northWest directNorth northEast
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => count_partition μ.cells p)
  omega

private theorem corner_above (μ ν : YoungDiagram) (p : ℕ × ℕ)
    (_hf : p ∉ μ.cells) (he : ν.cells = insert p μ.cells)
    (i : ℕ) (hi : i < p.1) : (i,p.2) ∈ μ := by
  have hp : p ∈ ν := by change p ∈ ν.cells; rw [he]; simp
  have hm := ν.up_left_mem hi.le le_rfl hp
  change (i,p.2) ∈ ν.cells at hm
  rw [he, Finset.mem_insert] at hm
  rcases hm with hh | hh
  · have := congrArg Prod.fst hh; omega
  · exact hh

private theorem corner_no_southeast (μ : YoungDiagram) (p : ℕ × ℕ)
    (hf : p ∉ μ.cells) (q : ℕ × ℕ) (hq : q ∈ μ.cells) :
    ¬ (p.1 ≤ q.1 ∧ p.2 ≤ q.2) := by
  rintro ⟨hr,hc⟩
  exact hf (μ.up_left_mem hr hc hq)

private theorem corner_direct (μ ν : YoungDiagram) (p : ℕ × ℕ)
    (hf : p ∉ μ.cells) (he : ν.cells = insert p μ.cells) :
    (μ.cells.filter (fun q => q.1 < p.1 ∧ q.2 = p.2)).card = p.1 := by
  have hh : μ.cells.filter (fun q => q.1 < p.1 ∧ q.2 = p.2) =
      (Finset.range p.1).image (fun i => (i,p.2)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨_,hr,hc⟩; exact ⟨q.1,hr, Prod.ext rfl hc.symm⟩
    · rintro ⟨i,hi,rfl⟩; exact ⟨corner_above μ ν p hf he i hi,hi,rfl⟩
  rw [hh, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro i j h; exact congrArg Prod.fst h

private theorem corner_right (μ : YoungDiagram) (p : ℕ × ℕ)
    (hf : p ∉ μ.cells) :
    (μ.cells.filter (fun q => q.1 < p.1 ∧ p.2 < q.2)).card = rightCount μ p.2 := by
  unfold rightCount
  congr 1
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hm,_,hc⟩; exact ⟨hm,hc⟩
  · rintro ⟨hm,hc⟩
    have hn := corner_no_southeast μ p hf q hm
    exact ⟨hm, by omega, hc⟩

private theorem corner_northWest (μ ν : YoungDiagram) (p : ℕ × ℕ)
    (hf : p ∉ μ.cells) (he : ν.cells = insert p μ.cells) :
    northWest ν = northWest μ +
      (μ.cells.filter (fun q => q.1 < p.1 ∧ q.2 < p.2)).card := by
  unfold northWest
  rw [he, Finset.sum_insert hf]
  have hp : (insert p μ.cells).filter (fun q => q.1 < p.1 ∧ q.2 < p.2) =
      μ.cells.filter (fun q => q.1 < p.1 ∧ q.2 < p.2) := by simp [Finset.filter_insert]
  rw [hp, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hn : ¬ (p.1 < q.1 ∧ p.2 < q.2) := by
    have := corner_no_southeast μ p hf q hq
    omega
  simp [Finset.filter_insert, hn]

private theorem above_card (μ : YoungDiagram) (r : ℕ) :
    (μ.cells.filter (fun q => q.1 < r)).card = ∑ i ∈ Finset.range r, μ.rowLen i := by
  have h := Finset.sum_card_fiberwise_eq_card_filter μ.cells (Finset.range r) Prod.fst
  simpa only [Finset.mem_range, YoungDiagram.rowLen_eq_card, YoungDiagram.row] using h.symm

set_option maxHeartbeats 1600000 in
private theorem crossing_above (n : ℕ) (S : State n) (a : Fin n) :
    let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
    I.crossings + I.newCell.1 = (S.1.cells.filter (fun q => q.1 < I.newCell.1)).card := by
  dsimp only
  let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
  have hb : I.newCell.1 ≤ S.1.colLen 0 := by
    have h := TableauRowRecursion.runRows_columns_bound n (TableauRowRecursion.rows n S.2.1 S.2.2) a
    rw [TableauRowRecursion.rows_length] at h
    change (TableauRowRecursion.runRows n (TableauRowRecursion.rows n S.2.1 S.2.2) a).columns.length - 1 ≤ _
    omega
  have hc := TableauInsertion.insert_cells n S.1 S.2.1 S.2.2 a
  have hpos (i : ℕ) (hi : i ∈ Finset.range I.newCell.1) : 1 ≤ S.1.rowLen i := by
    have h := corner_above S.1 I.shape I.newCell hc.1 hc.2 i (Finset.mem_range.mp hi)
    rw [YoungDiagram.mem_iff_lt_rowLen] at h
    omega
  rw [TableauInsertion.insert_crossings_sum, above_card]
  change (((TableauRowRecursion.rows n S.2.1 S.2.2).take I.newCell.1).map (fun w => w.length-1)).sum + I.newCell.1 = _
  simp only [TableauRowRecursion.rows, ← List.map_take, List.take_range, min_eq_left hb,
    List.map_map, Function.comp_def, TableauRowStep.row_length]
  rw [← List.sum_toFinset _ (List.nodup_range)]
  have ht : (List.range I.newCell.1).toFinset = Finset.range I.newCell.1 := by
    ext i; simp
  rw [ht]
  have he : (∑ i ∈ Finset.range I.newCell.1, (S.1.rowLen i - 1)) +
      ∑ _i ∈ Finset.range I.newCell.1, 1 = ∑ i ∈ Finset.range I.newCell.1, S.1.rowLen i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi; have := hpos i hi; omega
  simpa using he

theorem insert_crossings_shape (n : ℕ) (S : State n) (a : Fin n) :
    let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
    northWest S.1 + I.crossings = northWest I.shape + rightCount S.1 I.newCell.2 := by
  let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
  have hc := TableauInsertion.insert_cells n S.1 S.2.1 S.2.2 a
  have hd := corner_direct S.1 I.shape I.newCell hc.1 hc.2
  have hr := corner_right S.1 I.newCell hc.1
  have hn := corner_northWest S.1 I.shape I.newCell hc.1 hc.2
  have hp := count_partition S.1.cells I.newCell
  have hb := crossing_above n S a
  change I.crossings + I.newCell.1 = (S.1.cells.filter (fun q => q.1 < I.newCell.1)).card at hb
  change northWest S.1 + I.crossings = northWest I.shape + rightCount S.1 I.newCell.2
  omega

theorem run_word (n : ℕ) (S : State n) (w : List (Fin n)) :
    let R := TableauWordInsertion.run n S w
    OddPlactic.word n (TableauEvaluation.rowFinWord n S.2.1 S.2.2 ++ w) =
      (-1 : ℤ) ^ crossings n S w •
        OddPlactic.word n (TableauEvaluation.rowFinWord n R.1.2.1 R.1.2.2) := by
  induction w generalizing S with
  | nil => simp [TableauWordInsertion.run, crossings]
  | cons a w ih =>
    let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
    let S' : State n := ⟨I.shape, ⟨I.tableau,I.bounded⟩⟩
    have hi := TableauInsertion.insert_word n S.1 S.2.1 S.2.2 a
    have ht := ih S'
    change OddPlactic.word n (TableauEvaluation.rowFinWord n S.2.1 S.2.2 ++ (a::w)) =
      (-1 : ℤ) ^ (I.crossings + crossings n S' w) • _
    rw [show TableauEvaluation.rowFinWord n S.2.1 S.2.2 ++ (a::w) =
      (TableauEvaluation.rowFinWord n S.2.1 S.2.2 ++ [a]) ++ w by simp]
    rw [OddPlactic.word_append, hi, smul_mul_assoc]
    rw [← OddPlactic.word_append, ht, smul_smul, ← pow_add]
    rfl

private theorem rightCount_insert (μ ν : YoungDiagram) (p : ℕ × ℕ)
    (he : ν.cells = insert p μ.cells) (c : ℕ) (hc : p.2 ≤ c) :
    rightCount ν c = rightCount μ c := by
  unfold rightCount
  rw [he]
  simp [Finset.filter_insert, show ¬ c < p.2 by omega]

set_option maxHeartbeats 1600000 in
theorem run_crossings_shape (n : ℕ) (S : State n) (w : List (Fin n))
    (hw : w.Sorted (· ≤ ·)) :
    let R := TableauWordInsertion.run n S w
    northWest S.1 + crossings n S w = northWest R.1.1 + stripRight S.1 R.2 := by
  induction w generalizing S with
  | nil => simp [TableauWordInsertion.run, crossings, stripRight]
  | cons a w ih =>
    let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
    let S' : State n := ⟨I.shape, ⟨I.tableau,I.bounded⟩⟩
    let R := TableauWordInsertion.run n S' w
    have hi := insert_crossings_shape n S a
    have ht := ih S' (List.pairwise_cons.mp hw).2
    have hh := (TableauWordInsertion.run_horizontal n S (a::w) hw).1
    change (I.newCell :: R.2).Pairwise (fun p q => p.2 < q.2) at hh
    have he : stripRight S'.1 R.2 = stripRight S.1 R.2 := by
      unfold stripRight
      congr 1
      apply List.map_congr_left
      intro p hp
      exact rightCount_insert S.1 I.shape I.newCell
        (TableauInsertion.insert_cells n S.1 S.2.1 S.2.2 a).2 p.2
        ((List.pairwise_cons.mp hh).1 p hp).le
    change northWest S'.1 + crossings n S' w = northWest R.1.1 + stripRight S'.1 R.2 at ht
    rw [he] at ht
    change northWest S.1 + I.crossings = northWest S'.1 + rightCount S.1 I.newCell.2 at hi
    change northWest S.1 + (I.crossings + crossings n S' w) =
      northWest R.1.1 + stripRight S.1 (I.newCell :: R.2)
    simp only [stripRight, List.map_cons, List.sum_cons] at *
    omega

private theorem shape_sign (μ : YoungDiagram) :
    (-1 : ℤ) ^ (directNorth μ + north μ + northEast μ) = (-1 : ℤ) ^ northWest μ := by
  rw [shape_partition, pow_add, pow_mul]
  norm_num

theorem run_polynomial (n : ℕ) (S : State n) (w : List (Fin n))
    (hw : w.Sorted (· ≤ ·)) :
    let R := TableauWordInsertion.run n S w
    (-1 : ℤ) ^ (directNorth S.1 + north S.1 + northEast S.1) •
      (TableauEvaluation.rowPolynomial n S.2.1 S.2.2 *
        PlacticEvaluation.toSkew n (OddPlactic.word n w)) =
    (-1 : ℤ) ^ (directNorth R.1.1 + north R.1.1 + northEast R.1.1 + stripRight S.1 R.2) •
      TableauEvaluation.rowPolynomial n R.1.2.1 R.1.2.2 := by
  dsimp only
  have h := congrArg (PlacticEvaluation.toSkew n) (run_word n S w)
  simp only [OddPlactic.word_append, map_mul, map_zsmul] at h
  change TableauEvaluation.rowPolynomial n S.2.1 S.2.2 *
    PlacticEvaluation.toSkew n (OddPlactic.word n w) =
    (-1 : ℤ) ^ crossings n S w • TableauEvaluation.rowPolynomial n
      (TableauWordInsertion.run n S w).1.2.1 (TableauWordInsertion.run n S w).1.2.2 at h
  rw [h, smul_smul, shape_sign, ← pow_add, run_crossings_shape n S w hw,
    pow_add, pow_add, shape_sign]

end OddMath.Frontier.TableauStripSigns
