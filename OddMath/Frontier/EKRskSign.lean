import OddMath.Frontier.TableauWordInsertion
import OddMath.Frontier.TableauDominance
import OddMath.Frontier.EKPairingMatrices

/-!
# EK Thm 3.7 (3.8): entrywise sign refinement of the odd RSK map

EK arXiv:1107.5610v2.  Printed statement (p.27-28, Theorem 3.7, (3.8)):
the RSK map `A ↦ (P,Q)` from ℕ-matrices with `row(A)=µ`, `col(A)=ρ` to pairs of
semistandard tableaux of the same shape is a bijection "under which the sign of `A` as in
the computation of `M'_{µρ}` equals `(-1)^{binom(λ^T,2)} sign(P) sign(Q)`, where
`λ = shape(P) = shape(Q)`".

* Sign of `A` in `M'` (p.24, Prop. 3.1(2)): `(-1)^{ab}` for every pair of entries in which
  an `a` is strictly below and strictly to the left of a `b`; this is the existing
  `EKPairingMatrices.crossing` (the sign summed in `EKDualBases.proposition_3_1_Mh`).
* `sign(T)` (p.27): sign of the minimal sorting permutation of the row word (rows read
  left to right, bottom to top) = existing `TableauDominance.tableauSign`.
* RSK map (Sec. 4.1, p.32; frozen definition, the fixed specification): the two-line array is
  read in book order (`u` = row, `v` = column, entry `k` repeated `k` times);
  `P_k := TableauInsertion.insert P_{k-1} v_k` (existing row insertion) and
  `Q_k := Q_{k-1}` with `u_k` placed in the unique new cell of `P_k`.
  Letters are zero-based `Fin` values; the tableau label is `value + 1`.
* Shape sign: `binom(λ^T,2) := Σ_j binom(λ^T_j, 2)`; we use the equal statistic
  `shapeExp λ = Σ_{cells (i,j)} i` (zero-based row index) and prove the equality with the
  printed column-binomial form in `shapeExp_eq_choose`.

Only the map is used: no bijectivity, no (3.9).
The proof follows Sec. 4.2 (pp.34-35): `sign(u) = 1`, `sign(v) = sign(A)`, and the box-by-box
comparison (4.5): each bump in old row `j` contributes `λ_j - 1` transpositions, the new `Q` label
crosses the `λ_1+...+λ_s` letters above it, and the shape sign changes by `(-1)^s`.
-/

namespace OddMath.Frontier.EKRskSign

open TableauSign TableauEvaluation TableauRowWord EKPairingMatrices
open scoped BigOperators

/-! ## Generic list statistics -/

/-- Cross inversions of a concatenation. -/
def crossL (xs ys : List ℕ) : ℕ := (xs.map fun x => (ys.filter (fun y => y < x)).length).sum

theorem inversions_append (xs ys : List ℕ) :
    inversions (xs ++ ys) = inversions xs + inversions ys + crossL xs ys := by
  induction xs with
  | nil => simp [inversions, crossL]
  | cons x xs ih =>
    simp only [List.cons_append, inversions, List.filter_append, List.length_append, ih, crossL,
      List.map_cons, List.sum_cons]
    omega

theorem inversions_append_single (xs : List ℕ) (a : ℕ) :
    inversions (xs ++ [a]) = inversions xs + (xs.filter (fun x => a < x)).length := by
  rw [inversions_append]
  have h : crossL xs [a] = (xs.filter (fun x => a < x)).length := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [crossL, List.map_cons, List.sum_cons, List.filter_cons] at ih ⊢
      rw [ih]
      by_cases hx : a < x <;> simp [hx]
      omega
  simp [inversions, h]

theorem crossL_cons_of_ge (xs ys : List ℕ) (x : ℕ) (h : ∀ y ∈ xs, y ≤ x) :
    crossL xs (x :: ys) = crossL xs ys := by
  induction xs with
  | nil => rfl
  | cons y xs ih =>
    have hy := h y (by simp)
    have ht := ih (fun z hz => h z (by simp [hz]))
    simp only [crossL, List.map_cons, List.sum_cons, List.filter_cons] at ht ⊢
    rw [ht]
    simp [not_lt.mpr hy]

/-- Inserting a letter that is `≥` everything before it and `>` everything after it. -/
theorem inversions_middle (L1 L2 : List ℕ) (x : ℕ) (h1 : ∀ y ∈ L1, y ≤ x)
    (h2 : ∀ y ∈ L2, y < x) :
    inversions (L1 ++ x :: L2) = inversions (L1 ++ L2) + L2.length := by
  rw [inversions_append, inversions_append, crossL_cons_of_ge _ _ _ h1]
  have hf : L2.filter (fun y => y < x) = L2 := List.filter_eq_self.mpr (by simpa using h2)
  simp only [inversions, hf]
  omega

theorem inversions_of_sorted (l : List ℕ) (h : l.Pairwise (· ≤ ·)) : inversions l = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hx, hs⟩ := List.pairwise_cons.mp h
    have hf : xs.filter (fun y => y < x) = [] :=
      List.filter_eq_nil_iff.mpr (fun y hy => by simpa using hx y hy)
    simp [inversions, hf, ih hs]

theorem neg_one_pow_eq_iff {a b : ℕ} : (-1 : ℤ) ^ a = (-1) ^ b ↔ a % 2 = b % 2 := by
  constructor
  · intro h
    rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := b)] at h
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp_all
  · intro h
    rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

/-! ## Counting over `Fin c` -/

theorem sum_map_eq_count {c : ℕ} (xs : List (Fin c)) (g : Fin c → ℕ) :
    (xs.map g).sum = ∑ j, xs.count j * g j := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.count_cons, add_mul,
      Finset.sum_add_distrib]
    simp [beq_iff_eq, Finset.sum_ite_eq', Nat.add_comm]

theorem length_filter_lt_eq {c : ℕ} (ys : List (Fin c)) (x : Fin c) :
    (ys.filter (fun y => y < x)).length = ∑ l, if l < x then ys.count l else 0 := by
  have h : (ys.filter (fun y => y < x)).length = (ys.map (fun y => if y < x then 1 else 0)).sum := by
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      by_cases hy : y < x <;> simp [List.filter_cons, hy, ih, Nat.add_comm]
  rw [h, sum_map_eq_count]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

def lab {c : ℕ} (j : Fin c) : ℕ := j.val + 1

theorem crossL_map_lab {c : ℕ} (xs ys : List (Fin c)) :
    crossL (xs.map lab) (ys.map lab) =
      ∑ j, ∑ l, if l < j then xs.count j * ys.count l else 0 := by
  have hf (x : Fin c) : ((ys.map lab).filter (fun y => y < lab x)).length =
      (ys.filter (fun y => y < x)).length := by
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro y _
    simp only [Function.comp_apply, lab, Fin.lt_def, Nat.add_lt_add_iff_right]
  unfold crossL
  rw [List.map_map]
  simp only [Function.comp_def, hf, length_filter_lt_eq]
  rw [sum_map_eq_count]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

/-! ## The two-line array and `sign(v) = sign(A)` -/

variable {r c : ℕ}

/-- Book-order two-line array of an ℕ-matrix: `(u,v) = (row, column)`, entry `k` repeated. -/
def twoLine (A : Raw r c) : List (Fin r × Fin c) :=
  (List.finRange r).flatMap fun i =>
    (List.finRange c).flatMap fun j => List.replicate (A i j) (i, j)

/-- The column word of one row. -/
def rowV (a : Fin c → ℕ) : List (Fin c) :=
  (List.finRange c).flatMap fun j => List.replicate (a j) j

theorem twoLine_snd (A : Raw r c) :
    (twoLine A).map Prod.snd = (List.finRange r).flatMap fun i => rowV (A i) := by
  simp [twoLine, rowV, List.map_flatMap, List.map_replicate]

theorem rowV_sorted (a : Fin c → ℕ) : (rowV a).Pairwise (· ≤ ·) := by
  unfold rowV
  rw [List.pairwise_flatMap]
  refine ⟨fun j _ => ?_, ?_⟩
  · exact List.pairwise_replicate.mpr (Or.inr le_rfl)
  · refine (List.pairwise_lt_finRange c).imp ?_
    intro j k hjk x hx y hy
    rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
    exact le_of_lt hjk

theorem count_rowV (a : Fin c → ℕ) (j : Fin c) : (rowV a).count j = a j := by
  unfold rowV
  rw [List.count_flatMap, ← Fin.sum_univ_def]
  simp [List.count_replicate, beq_iff_eq]

theorem count_flatMap_rowV (A : Raw r c) (l : Fin c) :
    ((List.finRange r).flatMap fun i => rowV (A i)).count l = ∑ k, A k l := by
  rw [List.count_flatMap, ← Fin.sum_univ_def]
  simp [Function.comp_def, count_rowV]

theorem crossing_succ (A : Raw (r + 1) c) :
    crossing A = crossing (fun i => A i.succ) +
      ∑ k : Fin r, ∑ j, ∑ l, if l < j then A 0 j * A k.succ l else 0 := by
  unfold crossing
  simp only [Fin.sum_univ_succ, lt_irrefl, if_false, Fin.succ_pos, if_true,
    Fin.not_lt_zero, Fin.succ_lt_succ_iff, Finset.sum_const_zero, zero_add]
  omega

theorem inversions_flatMap_rowV (A : Raw r c) :
    inversions (((List.finRange r).flatMap fun i => rowV (A i)).map lab) = crossing A := by
  induction r with
  | zero => simp [crossing, inversions]
  | succ r ih =>
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map, List.map_append,
      inversions_append, ih (fun i => A i.succ), crossing_succ,
      inversions_of_sorted _ ((rowV_sorted (A 0)).map _ (fun a b h => by
        simp only [lab]; exact Nat.succ_le_succ h)),
      crossL_map_lab]
    simp only [count_rowV, count_flatMap_rowV, zero_add]
    congr 1
    calc (∑ j : Fin c, ∑ l : Fin c, if l < j then A 0 j * ∑ k : Fin r, A k.succ l else 0)
        = ∑ j : Fin c, ∑ l : Fin c, ∑ k : Fin r,
            (if l < j then A 0 j * A k.succ l else 0) := by
          apply Finset.sum_congr rfl; intro j _
          apply Finset.sum_congr rfl; intro l _
          split_ifs <;> simp [Finset.mul_sum]
      _ = ∑ j : Fin c, ∑ k : Fin r, ∑ l : Fin c,
            (if l < j then A 0 j * A k.succ l else 0) := by
          apply Finset.sum_congr rfl; intro j _
          exact Finset.sum_comm
      _ = ∑ k : Fin r, ∑ j : Fin c, ∑ l : Fin c,
            (if l < j then A 0 j * A k.succ l else 0) := Finset.sum_comm

/-- `sign(v) = sign(A)` (EK p.34): inversions of the column word are the SW-NE count. -/
theorem inversions_twoLine (A : Raw r c) :
    inversions ((twoLine A).map (fun x => lab x.2)) = crossing A := by
  have hmap : (twoLine A).map (fun x => lab x.2) =
      ((List.finRange r).flatMap fun i => rowV (A i)).map lab := by
    rw [← twoLine_snd, List.map_map]
    rfl
  rw [hmap, inversions_flatMap_rowV]

/-- Lexicographic order on the two-line array. -/
def LexLE (x y : Fin r × Fin c) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)

theorem twoLine_sorted (A : Raw r c) : (twoLine A).Pairwise LexLE := by
  unfold twoLine
  rw [List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun j _ => ?_, ?_⟩
    · exact List.pairwise_replicate.mpr (Or.inr (Or.inr ⟨rfl, le_rfl⟩))
    · refine (List.pairwise_lt_finRange c).imp ?_
      intro j k hjk x hx y hy
      rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
      exact Or.inr ⟨rfl, le_of_lt hjk⟩
  · refine (List.pairwise_lt_finRange r).imp ?_
    intro i k hik x hx y hy
    obtain ⟨j, _, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨l, _, hy⟩ := List.mem_flatMap.mp hy
    rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
    exact Or.inl hik


/-! ## Row-reading cells: inserting an outer corner -/

instance rowLE_antisymm : IsAntisymm (ℕ × ℕ) RowLE := ⟨by
  intro a b h1 h2
  unfold RowLE at h1 h2
  exact Prod.ext (by omega) (by omega)⟩

/-- Cells of `μ` read before a new corner `N`, then `N`, then the cells of the rows above. -/
theorem rowCells_insert (μ ν : YoungDiagram) (N : ℕ × ℕ) (hN : N ∉ μ.cells)
    (hν : ν.cells = insert N μ.cells) :
    rowCells ν = (rowCells μ).filter (fun q => decide (RowLE q N)) ++
      N :: (rowCells μ).filter (fun q => !decide (RowLE q N)) := by
  classical
  apply List.eq_of_perm_of_sorted (r := RowLE)
  · refine (rowCells_perm ν).trans ?_
    rw [hν]
    refine (Finset.toList_insert hN).trans ?_
    refine List.Perm.trans ?_ List.perm_middle.symm
    exact List.Perm.cons _ ((List.filter_append_perm _ _).trans (rowCells_perm μ)).symm
  · exact rowCells_sorted ν
  · have hs := rowCells_sorted μ
    unfold List.Sorted at hs ⊢
    rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨hs.filter _, ⟨?_, hs.filter _⟩, ?_⟩
    · intro b hb
      have := (List.mem_filter.mp hb).2
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
      unfold RowLE at this ⊢
      omega
    · intro a ha b hb
      have h1 := (List.mem_filter.mp ha).2
      simp only [decide_eq_true_eq] at h1
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h1
      · have h2 := (List.mem_filter.mp hb).2
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h2
        unfold RowLE at h1 h2 ⊢
        omega

theorem rowCells_split (μ : YoungDiagram) (N : ℕ × ℕ) :
    rowCells μ = (rowCells μ).filter (fun q => decide (RowLE q N)) ++
      (rowCells μ).filter (fun q => !decide (RowLE q N)) := by
  apply List.eq_of_perm_of_sorted (r := RowLE)
  · exact (List.filter_append_perm _ _).symm
  · exact rowCells_sorted μ
  · have hs := rowCells_sorted μ
    unfold List.Sorted at hs ⊢
    rw [List.pairwise_append]
    refine ⟨hs.filter _, hs.filter _, ?_⟩
    intro a ha b hb
    have h1 := (List.mem_filter.mp ha).2
    have h2 := (List.mem_filter.mp hb).2
    simp only [decide_eq_true_eq] at h1
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h2
    unfold RowLE at h1 h2 ⊢
    omega

/-- For an outer corner `N` of `μ`, a cell of `μ` is read after `N` iff it lies in a row above. -/
theorem not_rowLE_iff (μ : YoungDiagram) (N : ℕ × ℕ) (hN : N ∉ μ.cells) {q : ℕ × ℕ} (hq : q ∈ μ.cells) :
    ¬ RowLE q N ↔ q.1 < N.1 := by
  unfold RowLE
  constructor
  · intro h
    by_contra h'
    apply h
    by_cases he : q.1 = N.1
    · refine Or.inr ⟨he, ?_⟩
      by_contra hc
      apply hN
      rw [YoungDiagram.mem_cells] at hq ⊢
      exact μ.up_left_mem (le_of_eq he.symm) (by omega) hq
    · exact Or.inl (by omega)
  · intro h
    omega

theorem card_row (μ : YoungDiagram) (i : ℕ) :
    (μ.cells.filter (fun q => q.1 = i)).card = μ.rowLen i := by
  classical
  have h : μ.cells.filter (fun q => q.1 = i) = (Finset.range (μ.rowLen i)).image (fun j => (i, j)) := by
    ext q
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hq, rfl⟩
      exact ⟨q.2, YoungDiagram.mem_iff_lt_rowLen.mp hq, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨YoungDiagram.mem_iff_lt_rowLen.mpr hj, rfl⟩
  rw [h, Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), Finset.card_range]

theorem card_rows_below (μ : YoungDiagram) (p : ℕ) (hp : ∀ i < p, (i, 0) ∈ μ) :
    ((List.range p).map (fun i => μ.rowLen i - 1)).sum + p =
      (μ.cells.filter (fun q => q.1 < p)).card := by
  classical
  induction p with
  | zero => simp
  | succ p ih =>
    have hsplit : μ.cells.filter (fun q => q.1 < p + 1) =
        μ.cells.filter (fun q => q.1 < p) ∪ μ.cells.filter (fun q => q.1 = p) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_union, ← and_or_left]
      exact and_congr_right (fun _ => Nat.lt_succ_iff_lt_or_eq)
    rw [hsplit, Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr
      (fun q _ h1 h2 => by omega)), card_row, ← ih (fun i hi => hp i (by omega)),
      List.range_succ, List.map_append, List.sum_append]
    have hpos : 0 < μ.rowLen p := YoungDiagram.mem_iff_lt_rowLen.mp (hp p (by omega))
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-! ## One insertion step: the three sign changes of Sec. 4.2 -/

section Step
variable (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ) (hT : InAlphabet n T) (a : Fin n)

theorem newCell_mem : (TableauInsertion.insert n μ T hT a).newCell ∈
    (TableauInsertion.insert n μ T hT a).shape.cells := by
  rw [(TableauInsertion.insert_cells n μ T hT a).2]
  exact Finset.mem_insert_self _ _

theorem rows_above_mem : ∀ i < (TableauInsertion.insert n μ T hT a).newCell.1, (i, 0) ∈ μ := by
  intro i hi
  have hc := TableauInsertion.insert_cells n μ T hT a
  have hm := newCell_mem n μ T hT a
  rw [YoungDiagram.mem_cells] at hm
  have h0 : (i, 0) ∈ (TableauInsertion.insert n μ T hT a).shape :=
    (TableauInsertion.insert n μ T hT a).shape.up_left_mem (le_of_lt hi) (Nat.zero_le _) hm
  rw [← YoungDiagram.mem_cells, hc.2] at h0
  rcases Finset.mem_insert.mp h0 with he | h0
  · exact absurd (congrArg Prod.fst he) (by simp only; omega)
  · exact (YoungDiagram.mem_cells _).mp h0

/-- Bumping transpositions (EK p.35): `Kn(v_{k+1}) - Kn(v_k) = Σ_{j ≤ s} (λ_j - 1)`,
recorded as `crossings + s = #cells in the rows above the new cell`. -/
theorem crossings_add_row :
    (TableauInsertion.insert n μ T hT a).crossings + (TableauInsertion.insert n μ T hT a).newCell.1 =
      (μ.cells.filter (fun q => q.1 < (TableauInsertion.insert n μ T hT a).newCell.1)).card := by
  set p := (TableauInsertion.insert n μ T hT a).newCell.1 with hp
  have habove := rows_above_mem n μ T hT a
  rw [← hp] at habove
  have hle : p ≤ μ.colLen 0 := by
    rcases Nat.eq_zero_or_pos p with h0 | hpos
    · omega
    · have := habove (p - 1) (by omega)
      have := YoungDiagram.mem_iff_lt_colLen.mp this
      omega
  rw [TableauInsertion.insert_crossings_sum, ← hp, ← card_rows_below μ p habove]
  congr 2
  have hl := TableauRowRecursion.rows_lengths n μ T hT
  calc ((TableauRowRecursion.rows n T hT).take p).map (fun w => w.length - 1)
      = (((TableauRowRecursion.rows n T hT).map List.length).map (· - 1)).take p := by
        rw [List.map_map, List.map_take]; rfl
    _ = (List.range p).map (fun i => μ.rowLen i - 1) := by
        rw [hl, YoungDiagram.rowLens, List.map_map, ← List.map_take, List.take_range,
          Nat.min_eq_left hle]
        rfl

/-- `sign(v_k) = (-1)^{Kn(v_k)} sign(P_k)` for one step, from the existing odd-plactic
row transport (`TableauInsertion.insert_word`) and the skew-polynomial evaluation. -/
theorem insert_inversions :
    (inversions (rowWord T ++ [a.val + 1])) % 2 =
      ((TableauInsertion.insert n μ T hT a).crossings +
        inversions (rowWord (TableauInsertion.insert n μ T hT a).tableau)) % 2 := by
  have h := congrArg (PlacticEvaluation.toSkew n) (TableauInsertion.insert_word n μ T hT a)
  rw [map_zsmul, TableauEvaluation.wordPolynomial_eq, TableauEvaluation.wordPolynomial_eq] at h
  simp only [OddMath.SkewPolynomial.monomial, Finsupp.smul_single, smul_eq_mul] at h
  rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h with ⟨he, hc⟩ | ⟨h0, _⟩
  · have hs : ((rowFinWord n T hT ++ [a]).map Fin.val).sum =
        ((rowFinWord n _ (TableauInsertion.insert n μ T hT a).bounded).map Fin.val).sum := by
      rw [sum_vals_eq_counts, sum_vals_eq_counts]
      exact Finset.sum_congr rfl (fun i _ => by rw [congrFun he i])
    rw [← pow_add] at hc
    have hp := neg_one_pow_eq_iff.mp hc
    have hl : inversions ((rowFinWord n T hT ++ [a]).map Fin.val) =
        inversions (rowWord T ++ [a.val + 1]) := by
      rw [← inversions_map_succ ((rowFinWord n T hT ++ [a]).map Fin.val), List.map_map]
      congr 1
      rw [List.map_append, ← rowFinWord_labels n T hT]
      simp [Function.comp_def]
    rw [hl, rowFinWord_inversions, hs] at hp
    omega
  · exact absurd h0 (pow_ne_zero _ (by norm_num))

theorem rowFinWord_insert_perm :
    List.Perm (rowWord (TableauInsertion.insert n μ T hT a).tableau) (rowWord T ++ [a.val + 1]) := by
  rw [← rowFinWord_labels n T hT, ← rowFinWord_labels n _ (TableauInsertion.insert n μ T hT a).bounded]
  have : List.Perm (rowFinWord n _ (TableauInsertion.insert n μ T hT a).bounded)
      (rowFinWord n T hT ++ [a]) := by
    rw [List.perm_iff_count]
    intro i
    rw [rowFinWord_count, List.count_append, rowFinWord_count]
    simp only [exponents, TableauInsertion.insert_content, List.count_singleton, beq_iff_eq]
    by_cases h : i = a
    · simp [h]
    · simp [h, Ne.symm h]
  simpa using this.map (fun i : Fin n => i.val + 1)

end Step

/-! ## The RSK map (frozen definition) -/

/-- RSK state: `P` is a genuine bounded tableau, `Q` a filling of the same shape. -/
structure St (r c : ℕ) where
  shape : YoungDiagram
  P : PositiveTableau shape
  hP : InAlphabet c P
  Q : ℕ → ℕ → ℕ

/-- One RSK step on `(u, v)`: row-insert `v` into `P`, put `u` into the new cell of `Q`. -/
noncomputable def step (s : St r c) (x : Fin r × Fin c) : St r c :=
  let I := TableauInsertion.insert c s.shape s.P s.hP x.2
  { shape := I.shape, P := I.tableau, hP := I.bounded,
    Q := fun i j => if (i, j) = I.newCell then x.1.val + 1 else s.Q i j }

def init : St r c :=
  { shape := ⊥, P := TableauContent.emptyTableau,
    hP := fun p hp => absurd hp (by simp [YoungDiagram.cells_bot]),
    Q := fun _ _ => 0 }

noncomputable def rskState (A : Raw r c) : St r c := (twoLine A).foldl step init

/-- `Q` is a genuine bounded semistandard filling of the current shape. -/
def GoodQ (s : St r c) : Prop :=
  (∀ i j, (i, j) ∉ s.shape → s.Q i j = 0) ∧ (∀ i j, (i, j) ∈ s.shape → 0 < s.Q i j) ∧
  (∀ i j1 j2, j1 < j2 → (i, j2) ∈ s.shape → s.Q i j1 ≤ s.Q i j2) ∧
  (∀ i1 i2 j, i1 < i2 → (i2, j) ∈ s.shape → s.Q i1 j < s.Q i2 j) ∧
  (∀ i j, s.Q i j ≤ r)

/-- After inserting `x`: `Q` is good, bounded by `u+1`, and every `u+1` label lies weakly
below the new cell. -/
def Good2 (s : St r c) (x : Fin r × Fin c) : Prop :=
  GoodQ (step s x) ∧
  (∀ p ∈ (step s x).shape.cells, (step s x).Q p.1 p.2 ≤ x.1.val + 1) ∧
  (∀ p ∈ (step s x).shape.cells, (step s x).Q p.1 p.2 = x.1.val + 1 →
    (TableauInsertion.insert c s.shape s.P s.hP x.2).newCell.1 ≤ p.1)

theorem mem_step (s : St r c) (x : Fin r × Fin c) (p : ℕ × ℕ) :
    p ∈ (step s x).shape ↔
      p = (TableauInsertion.insert c s.shape s.P s.hP x.2).newCell ∨ p ∈ s.shape := by
  rw [← YoungDiagram.mem_cells, ← YoungDiagram.mem_cells]
  change p ∈ (TableauInsertion.insert c s.shape s.P s.hP x.2).shape.cells ↔ _
  rw [(TableauInsertion.insert_cells c s.shape s.P s.hP x.2).2]
  simp [TableauInsertion.insertCell]

theorem good2_of (s : St r c) (x : Fin r × Fin c) (hs : GoodQ s)
    (hb : ∀ p ∈ s.shape.cells, s.Q p.1 p.2 ≤ x.1.val + 1)
    (hr : ∀ p ∈ s.shape.cells, s.Q p.1 p.2 = x.1.val + 1 →
      (TableauInsertion.insert c s.shape s.P s.hP x.2).newCell.1 ≤ p.1) : Good2 s x := by
  set N := (TableauInsertion.insert c s.shape s.P s.hP x.2).newCell with hNdef
  have hNnot : N ∉ s.shape := by
    rw [← YoungDiagram.mem_cells]
    exact (TableauInsertion.insert_cells c s.shape s.P s.hP x.2).1
  have hmem := mem_step s x
  rw [← hNdef] at hmem
  have hQ (i j : ℕ) : (step s x).Q i j = if (i, j) = N then x.1.val + 1 else s.Q i j := rfl
  have habove : ∀ i j, (i, j) ∈ s.shape → i < N.1 → s.Q i j < x.1.val + 1 := by
    intro i j hij hi
    have h1 : s.Q i j ≤ x.1.val + 1 := hb (i, j) ((YoungDiagram.mem_cells _).mpr hij)
    have h2 : s.Q i j = x.1.val + 1 → N.1 ≤ i := hr (i, j) ((YoungDiagram.mem_cells _).mpr hij)
    by_contra hc
    have := h2 (by omega)
    omega
  have hne {p : ℕ × ℕ} (hp : p ∈ s.shape) : p ≠ N := fun h => hNnot (h ▸ hp)
  -- a cell strictly left of / above a member of the new shape is an old cell
  have hold_left {i j1 j2 : ℕ} (hj : j1 < j2) (h2 : (i, j2) ∈ (step s x).shape) :
      (i, j1) ∈ s.shape := by
    rcases (hmem (i, j1)).mp ((step s x).shape.up_left_mem le_rfl (le_of_lt hj) h2) with he | h
    · rcases (hmem (i, j2)).mp h2 with he2 | h2'
      · rw [← he2] at he; simp at he; omega
      · exact absurd (he ▸ s.shape.up_left_mem le_rfl (le_of_lt hj) h2') hNnot
    · exact h
  have hold_up {i1 i2 j : ℕ} (hi : i1 < i2) (h2 : (i2, j) ∈ (step s x).shape) :
      (i1, j) ∈ s.shape := by
    rcases (hmem (i1, j)).mp ((step s x).shape.up_left_mem (le_of_lt hi) le_rfl h2) with he | h
    · rcases (hmem (i2, j)).mp h2 with he2 | h2'
      · rw [← he2] at he; simp at he; omega
      · exact absurd (he ▸ s.shape.up_left_mem (le_of_lt hi) le_rfl h2') hNnot
    · exact h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j hij
    have h1 : (i, j) ≠ N := fun h => hij ((hmem _).mpr (Or.inl h))
    have h2 : (i, j) ∉ s.shape := fun h => hij ((hmem _).mpr (Or.inr h))
    rw [hQ, if_neg h1]
    exact hs.1 i j h2
  · intro i j hij
    rw [hQ]
    split_ifs with h
    · omega
    · rcases (hmem _).mp hij with h' | h'
      · exact absurd h' h
      · exact hs.2.1 i j h'
  · intro i j1 j2 hj h2
    have h1 := hold_left hj h2
    rw [hQ, hQ, if_neg (hne h1)]
    split_ifs with he
    · exact hb (i, j1) ((YoungDiagram.mem_cells _).mpr h1)
    · rcases (hmem _).mp h2 with h' | h'
      · exact absurd h' he
      · exact hs.2.2.1 i j1 j2 hj h'
  · intro i1 i2 j hi h2
    have h1 := hold_up hi h2
    rw [hQ, hQ, if_neg (hne h1)]
    split_ifs with he
    · apply habove i1 j h1
      have := congrArg Prod.fst he
      simp only at this
      omega
    · rcases (hmem _).mp h2 with h' | h'
      · exact absurd h' he
      · exact hs.2.2.2.1 i1 i2 j hi h'
  · intro i j
    rw [hQ]
    split_ifs
    · exact x.1.isLt
    · exact hs.2.2.2.2 i j
  · intro p hp
    rw [YoungDiagram.mem_cells] at hp
    rw [hQ]
    split_ifs with he
    · exact le_rfl
    · rcases (hmem _).mp hp with h' | h'
      · exact absurd h' he
      · exact hb p ((YoungDiagram.mem_cells _).mpr h')
  · intro p hp hpq
    rw [YoungDiagram.mem_cells] at hp
    rw [hQ] at hpq
    split_ifs at hpq with he
    · have := congrArg Prod.fst he
      simp only at this
      rw [← hNdef]
      omega
    · rcases (hmem _).mp hp with h' | h'
      · exact absurd h' he
      · exact hr p ((YoungDiagram.mem_cells _).mpr h') hpq

theorem good2_next (s : St r c) (x y : Fin r × Fin c) (h : Good2 s x) (hxy : LexLE x y) :
    Good2 (step s x) y := by
  obtain ⟨hg, hb, hr⟩ := h
  apply good2_of (step s x) y hg
  · intro p hp
    have := hb p hp
    rcases hxy with h1 | ⟨h1, _⟩
    · have : x.1.val < y.1.val := h1
      omega
    · rw [h1] at this; exact this
  · intro p hp hpq
    have hle := hb p hp
    rcases hxy with h1 | ⟨h1, h2⟩
    · have : x.1.val < y.1.val := h1
      omega
    · rw [← h1] at hpq
      have hrow := hr p hp hpq
      have hbump := (TableauBumpMonotone.insert_pair_le c s.shape s.P s.hP x.2 y.2 h2).2.2.2
      exact le_trans hbump hrow

/-! ## The sign invariant -/

/-- `shapeExp λ = Σ_{cells} (zero-based row) = Σ_j binom(λ^T_j, 2)` (see `shapeExp_eq_choose`). -/
noncomputable def shapeExp (μ : YoungDiagram) : ℕ := ∑ p ∈ μ.cells, p.1

/-- Row word of the `Q` filling (row cells, bottom to top, left to right). -/
noncomputable def qWord (s : St r c) : List ℕ := (rowCells s.shape).map (fun p => s.Q p.1 p.2)

noncomputable def sgnExp (s : St r c) : ℕ :=
  shapeExp s.shape + inversions (rowWord s.P) + inversions (qWord s)

def Inv (s : St r c) (pre : List (Fin r × Fin c)) : Prop :=
  List.Perm (rowWord s.P) (pre.map (fun x => lab x.2)) ∧
    inversions (pre.map (fun x => lab x.2)) % 2 = sgnExp s % 2

theorem inv_step (s : St r c) (x : Fin r × Fin c) (pre : List (Fin r × Fin c))
    (h2 : Good2 s x) (hi : Inv s pre) : Inv (step s x) (pre ++ [x]) := by
  set I := TableauInsertion.insert c s.shape s.P s.hP x.2 with hIdef
  set N := I.newCell with hNdef
  have hc : N ∉ s.shape.cells ∧ I.shape.cells = insert N s.shape.cells :=
    TableauInsertion.insert_cells c s.shape s.P s.hP x.2
  have hQ (i j : ℕ) : (step s x).Q i j = if (i, j) = N then x.1.val + 1 else s.Q i j := rfl
  have hperm : List.Perm (rowWord I.tableau) (rowWord s.P ++ [x.2.val + 1]) :=
    rowFinWord_insert_perm c s.shape s.P s.hP x.2
  -- bounds on the old Q labels
  have hb : ∀ p ∈ s.shape.cells, s.Q p.1 p.2 ≤ x.1.val + 1 := by
    intro p hp
    have hp' : p ∈ (step s x).shape.cells := by
      change p ∈ I.shape.cells; rw [hc.2]; exact Finset.mem_insert_of_mem hp
    have := h2.2.1 p hp'
    rwa [hQ, if_neg (fun h : (p.1, p.2) = N => hc.1 (by rw [← h]; exact hp))] at this
  have habove : ∀ p ∈ s.shape.cells, p.1 < N.1 → s.Q p.1 p.2 < x.1.val + 1 := by
    intro p hp hlt
    have hp' : p ∈ (step s x).shape.cells := by
      change p ∈ I.shape.cells; rw [hc.2]; exact Finset.mem_insert_of_mem hp
    have h1 : (step s x).Q p.1 p.2 ≤ x.1.val + 1 := h2.2.1 p hp'
    have h3 : (step s x).Q p.1 p.2 = x.1.val + 1 → N.1 ≤ p.1 := h2.2.2 p hp'
    rw [hQ, if_neg (fun h : (p.1, p.2) = N => hc.1 (by rw [← h]; exact hp))] at h1 h3
    by_contra hcon
    have := h3 (by omega)
    omega
  -- Q word
  have hsplitν := rowCells_insert s.shape I.shape N hc.1 hc.2
  have hsplitμ := rowCells_split s.shape N
  set L1 := (rowCells s.shape).filter (fun q => decide (RowLE q N))
  set L2 := (rowCells s.shape).filter (fun q => !decide (RowLE q N))
  have hmemL (q) (hq : q ∈ rowCells s.shape) : q ≠ N := fun h => hc.1 ((mem_rowCells _ _).mp (h ▸ hq))
  have hqword : qWord (step s x) = L1.map (fun p => s.Q p.1 p.2) ++
      (x.1.val + 1) :: L2.map (fun p => s.Q p.1 p.2) := by
    unfold qWord
    change (rowCells I.shape).map _ = _
    rw [hsplitν, List.map_append, List.map_cons]
    congr 1
    · apply List.map_congr_left
      intro q hq
      rw [hQ, if_neg (hmemL q (List.mem_filter.mp hq).1)]
    · rw [hQ, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro q hq
      rw [hQ, if_neg (hmemL q (List.mem_filter.mp hq).1)]
  have hqold : qWord s = L1.map (fun p => s.Q p.1 p.2) ++ L2.map (fun p => s.Q p.1 p.2) := by
    unfold qWord
    conv_lhs => rw [hsplitμ]
    rw [List.map_append]
  have hL2len : L2.length = (s.shape.cells.filter (fun q => q.1 < N.1)).card := by
    classical
    have hn : L2.Nodup := (rowCells_nodup _).filter _
    rw [← List.toFinset_card_of_nodup hn]
    congr 1
    ext q
    simp only [L2, List.mem_toFinset, List.mem_filter, mem_rowCells, Finset.mem_filter,
      Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · rintro ⟨hq, h⟩
      exact ⟨hq, (not_rowLE_iff s.shape N hc.1 hq).mp h⟩
    · rintro ⟨hq, h⟩
      exact ⟨hq, (not_rowLE_iff s.shape N hc.1 hq).mpr h⟩
  have hQinv : inversions (qWord (step s x)) = inversions (qWord s) + L2.length := by
    rw [hqword, hqold, inversions_middle]
    · simp
    · intro y hy
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      exact hb q ((mem_rowCells _ _).mp (List.mem_filter.mp hq).1)
    · intro y hy
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      have hq' := List.mem_filter.mp hq
      have hqc := (mem_rowCells _ _).mp hq'.1
      apply habove q hqc
      have := hq'.2
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
      exact (not_rowLE_iff s.shape N hc.1 hqc).mp this
  -- shape
  have hshape : shapeExp I.shape = shapeExp s.shape + N.1 := by
    unfold shapeExp
    rw [hc.2, Finset.sum_insert hc.1, Nat.add_comm]
  -- P word
  have hP : (inversions (rowWord s.P ++ [x.2.val + 1])) % 2 =
      (I.crossings + inversions (rowWord I.tableau)) % 2 :=
    insert_inversions c s.shape s.P s.hP x.2
  have hcr : I.crossings + N.1 = (s.shape.cells.filter (fun q => q.1 < N.1)).card :=
    crossings_add_row c s.shape s.P s.hP x.2
  have hfilter : ((pre.map (fun x => lab x.2)).filter (fun y => lab x.2 < y)).length =
      ((rowWord s.P).filter (fun y => x.2.val + 1 < y)).length :=
    ((hi.1.symm).filter _).length_eq
  refine ⟨?_, ?_⟩
  · change List.Perm (rowWord I.tableau) _
    rw [List.map_append]
    exact hperm.trans (hi.1.append_right _)
  · rw [List.map_append]
    change inversions (_ ++ [lab x.2]) % 2 = (shapeExp I.shape + inversions (rowWord I.tableau) +
      inversions (qWord (step s x))) % 2
    rw [inversions_append_single, hfilter, hshape, hQinv, hL2len]
    rw [inversions_append_single] at hP
    have hold := hi.2
    unfold sgnExp at hold
    simp only [lab] at hold ⊢
    omega

theorem main_ind (w : List (Fin r × Fin c)) : ∀ (s : St r c) (x : Fin r × Fin c)
    (pre : List (Fin r × Fin c)), (x :: w).Pairwise LexLE → Good2 s x → Inv s pre →
    GoodQ (w.foldl step (step s x)) ∧ Inv (w.foldl step (step s x)) (pre ++ x :: w) := by
  induction w with
  | nil =>
    intro s x pre _ h2 hi
    exact ⟨h2.1, inv_step s x pre h2 hi⟩
  | cons y w ih =>
    intro s x pre hs h2 hi
    have hxy : LexLE x y := (List.pairwise_cons.mp hs).1 y (by simp)
    have h := ih (step s x) y (pre ++ [x]) (List.pairwise_cons.mp hs).2
      (good2_next s x y h2 hxy) (inv_step s x pre h2 hi)
    simpa using h

theorem init_good : GoodQ (init : St r c) := by
  refine ⟨fun _ _ _ => rfl, ?_, ?_, ?_, fun _ _ => Nat.zero_le _⟩
  · intro i j h; exact absurd h (YoungDiagram.not_mem_bot _)
  · intro i j1 j2 _ h; exact absurd h (YoungDiagram.not_mem_bot _)
  · intro i1 i2 j _ h; exact absurd h (YoungDiagram.not_mem_bot _)

theorem init_inv : Inv (init : St r c) [] := by
  have hc : rowCells (⊥ : YoungDiagram) = [] := by
    simp [rowCells, YoungDiagram.cells_bot]
  refine ⟨?_, ?_⟩
  · change List.Perm ((rowCells ⊥).map _) []
    rw [hc]; rfl
  · simp [sgnExp, shapeExp, qWord, rowWord, hc, init, inversions, YoungDiagram.cells_bot]

theorem rskState_spec (A : Raw r c) :
    GoodQ (rskState A) ∧ Inv (rskState A) (twoLine A) := by
  unfold rskState
  cases hw : twoLine A with
  | nil => exact ⟨init_good, init_inv⟩
  | cons x w =>
    have hs := twoLine_sorted A
    rw [hw] at hs
    have h2 : Good2 (init : St r c) x := good2_of init x init_good
      (fun p hp => absurd hp (by simp [init, YoungDiagram.cells_bot]))
      (fun p hp => absurd hp (by simp [init, YoungDiagram.cells_bot]))
    simpa using main_ind w init x [] hs h2 init_inv

/-! ## The RSK pair and the entrywise sign identity (3.8) -/

noncomputable def rskShape (A : Raw r c) : YoungDiagram := (rskState A).shape

/-- `P = P_n`: the existing row insertion of the column word. -/
noncomputable def rskP (A : Raw r c) : PositiveTableau (rskShape A) := (rskState A).P

/-- `Q = Q_n`: row indices placed in the new cells; semistandard by the Row Bumping Lemma. -/
noncomputable def rskQ (A : Raw r c) : PositiveTableau (rskShape A) where
  entry := (rskState A).Q
  row_weak' := fun {i j1 j2} hj h => (rskState_spec A).1.2.2.1 i j1 j2 hj h
  col_strict' := fun {i1 i2 j} hi h => (rskState_spec A).1.2.2.2.1 i1 i2 j hi h
  zeros' := fun {i j} h => (rskState_spec A).1.1 i j h
  positive := fun {i j} h => (rskState_spec A).1.2.1 i j h

theorem rskP_bounded (A : Raw r c) : InAlphabet c (rskP A) := (rskState A).hP

theorem rskQ_bounded (A : Raw r c) : InAlphabet r (rskQ A) :=
  fun p _ => (rskState_spec A).1.2.2.2.2 p.1 p.2

/-- EK Thm 3.7, (3.8), entrywise sign: `sign(A)` as in `M'` (SW-NE pairs) equals
`(-1)^{binom(λ^T,2)} sign(P) sign(Q)` with `λ = shape(P) = shape(Q)`. -/
theorem thm_3_7_sign (A : Raw r c) :
    (-1 : ℤ) ^ crossing A =
      (-1 : ℤ) ^ shapeExp (rskShape A) * TableauDominance.tableauSign (rskP A) *
        TableauDominance.tableauSign (rskQ A) := by
  have h := (rskState_spec A).2.2
  rw [inversions_twoLine] at h
  unfold TableauDominance.tableauSign
  rw [← pow_add, ← pow_add]
  apply neg_one_pow_eq_iff.mpr
  rw [h]
  rfl

/-- The same identity for every matrix in the index set of `M'_{νμ}` (`EKDualBases.Mh`). -/
theorem thm_3_7_sign_mat {β : Fin r → ℕ} {α : Fin c → ℕ} (A : Mat β α) :
    (-1 : ℤ) ^ crossing A.val =
      (-1 : ℤ) ^ shapeExp (rskShape A.val) * TableauDominance.tableauSign (rskP A.val) *
        TableauDominance.tableauSign (rskQ A.val) :=
  thm_3_7_sign A.val


/-! ## Printed forms of the shape sign and reconciliation with the existing word insertion -/

/-- `Σ_{cells} row = Σ_j binom(λ^T_j, 2)`: the printed exponent `binom(λ^T, 2)` of (3.8). -/
theorem shapeExp_eq_choose (μ : YoungDiagram) :
    shapeExp μ = ∑ j ∈ Finset.range (μ.rowLen 0), (μ.colLen j).choose 2 := by
  classical
  unfold shapeExp
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.snd) (t := Finset.range (μ.rowLen 0))]
  · apply Finset.sum_congr rfl
    intro j _
    have h : μ.cells.filter (fun p => p.2 = j) =
        (Finset.range (μ.colLen j)).image (fun i => (i, j)) := by
      ext q
      simp only [Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hq, rfl⟩
        exact ⟨q.1, YoungDiagram.mem_iff_lt_colLen.mp hq, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr hi, rfl⟩
    rw [h, Finset.sum_image (fun a _ b _ hab => by simpa using hab), Finset.sum_range_id,
      Nat.choose_two_right]
  · intro p hp
    rw [Finset.mem_range, ← YoungDiagram.mem_iff_lt_rowLen]
    rw [YoungDiagram.mem_cells] at hp
    exact μ.up_left_mem (Nat.zero_le _) le_rfl hp

/-- Parity form `(-1)^{λ_2 + λ_4 + ...}` (one-based rows; zero-based odd rows). -/
theorem shapeExp_mod_two (μ : YoungDiagram) :
    shapeExp μ % 2 = (μ.cells.filter (fun p => p.1 % 2 = 1)).card % 2 := by
  classical
  unfold shapeExp
  rw [Finset.sum_nat_mod, Finset.card_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rcases Nat.mod_two_eq_zero_or_one p.1 with h | h <;> simp [h]

/-- The `P` of the RSK state is literally the existing chronological word insertion
(`TableauWordInsertion.run`) of the column word: reconciliation lemma. -/
theorem foldl_step_P (w : List (Fin r × Fin c)) (s : St r c) :
    (⟨(w.foldl step s).shape, ⟨(w.foldl step s).P, (w.foldl step s).hP⟩⟩ :
      TableauWordInsertion.State c) =
      (TableauWordInsertion.run c ⟨s.shape, ⟨s.P, s.hP⟩⟩ (w.map Prod.snd)).1 := by
  induction w generalizing s with
  | nil => rfl
  | cons x w ih => exact ih (step s x)

theorem rskP_eq_run (A : Raw r c) :
    (⟨rskShape A, ⟨rskP A, rskP_bounded A⟩⟩ : TableauWordInsertion.State c) =
      (TableauWordInsertion.run c ⟨⊥, ⟨TableauContent.emptyTableau, (init : St r c).hP⟩⟩
        ((twoLine A).map Prod.snd)).1 :=
  foldl_step_P (twoLine A) init

/-- The printed statement with the printed shape exponent `binom(λ^T,2) = Σ_j binom(λ^T_j,2)`. -/
theorem thm_3_7_sign_printed (A : Raw r c) :
    (-1 : ℤ) ^ crossing A =
      (-1 : ℤ) ^ (∑ j ∈ Finset.range ((rskShape A).rowLen 0), ((rskShape A).colLen j).choose 2) *
        TableauDominance.tableauSign (rskP A) * TableauDominance.tableauSign (rskQ A) := by
  rw [← shapeExp_eq_choose]
  exact thm_3_7_sign A

end OddMath.Frontier.EKRskSign
