import OddMath.Frontier.CompleteTableauExpansion
import OddMath.Frontier.TableauBumpStrict

/-!
# Ellis 1111.3932v1, equation (3.10): e-right Pieri rule for plactic odd Schur functions

Source (Ellis, *The odd Littlewood–Richardson rule*, arXiv:1111.3932v1, Sec. 3.2, verbatim
notation): "For a partition λ, let i/λ be the Young diagram obtained by removing rows 1 through i
from the diagram corresponding to λ. [...] We say that a skew shape is a vertical strip
(respectively horizontal strip) if no two of its boxes are in the same row (respectively column).
We say that a diagram μ is obtained from λ by adding a vertical strip if λ ⊂ μ and μ/λ is a
vertical strip."

(3.10), in the proof of Theorem 3.8:
  s^p_λ s^p_(1^k) = ∑_μ (-1)^{|i_1/λ| + … + |i_k/λ|} s^p_μ,
the sum over μ obtained from λ by adding a vertical strip of size k, i_1, …, i_k the rows of λ to
which a box was added (notation of Prop. 3.6).

Carrier: `CompleteTableauExpansion.sp n` (= s^p via `sp_recovered`) in
`OddMath.SkewPolynomial.SkewPolynomial n`; shapes with more than n rows are included in the sum
and vanish exactly as the existing `sp` does (no bounded-alphabet tableaux).

English zero-based cells.  A new box p lies in the 1-based row i = p.1 + 1, so
|i/λ| = #{q ∈ λ | p.1 < q.1} = `belowCount λ p.1`.

Proof: a DIRECT plactic argument (not Ellis's ψ₁ψ₂ route, which needs s^K = s^p on the EK
side).  The row word of a column tableau is strictly decreasing; row-inserting a strictly
decreasing word adds a vertical strip top-to-bottom (strict half of the Row Bumping Lemma,
existing `TableauBumpStrict.insert_pair_gt`); reverse bumping along a bottom-to-top peel of a
vertical strip (existing `TableauReverseWord`) inverts it, and strict decrease of the recovered
word follows from the weak half (`TableauBumpMonotone.insert_pair_le`).  Signs: the existing
single-insertion crossing count (`TableauStripSigns.insert_crossings_shape`) plus a new
northeast-count increment lemma telescope to exactly the printed exponent.
No s^s comparison, no h-right re-proof, no hives/Thm 4.8/EKL.
-/
namespace OddMath.Frontier.OddLRVerticalPieri
open scoped BigOperators
open OddMath.SkewPolynomial
open TableauStripSigns TableauEvaluation TableauPolynomial DegreeShapes TableauSign
open CompleteTableauExpansion
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev State (n : ℕ) := TableauWordInsertion.State n
abbrev Tab (n : ℕ) (μ : YoungDiagram) := {T : PositiveTableau μ // InAlphabet n T}

/-! ## Definitions (transcription of the printed notation) -/

/-- μ/λ is a vertical strip: λ ⊆ μ and no two boxes of μ/λ lie in the same row. -/
def Vertical (lam mu : YoungDiagram) : Prop :=
  lam.cells ⊆ mu.cells ∧
    (∀ p ∈ mu.cells \ lam.cells, ∀ q ∈ mu.cells \ lam.cells, p.1 = q.1 → p = q)

/-- |i/λ| for the 1-based row i = r + 1: boxes of λ in rows strictly below row r. -/
def belowCount (lam : YoungDiagram) (r : ℕ) : ℕ := (lam.cells.filter (fun q => r < q.1)).card

/-- The printed exponent |i_1/λ| + … + |i_k/λ|, one term per box of μ/λ. -/
def stripBelow (lam mu : YoungDiagram) : ℕ := ∑ p ∈ mu.cells \ lam.cells, belowCount lam p.1

/-- Chronological version on an insertion history. -/
def histBelow (lam : YoungDiagram) (ps : List (ℕ × ℕ)) : ℕ :=
  (ps.map (fun p => belowCount lam p.1)).sum

/-- The one-column diagram (1^k). -/
def column (k : ℕ) : YoungDiagram where
  cells := (Finset.range k) ×ˢ ({0} : Finset ℕ)
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.coe_product, Finset.coe_range, Finset.coe_singleton, Set.mem_prod,
      Set.mem_Iio, Set.mem_singleton_iff] at hb ⊢
    exact ⟨lt_of_le_of_lt hab.1 hb.1, Nat.le_zero.mp (hb.2 ▸ hab.2)⟩

theorem mem_column (k : ℕ) (p : ℕ × ℕ) : p ∈ column k ↔ p.1 < k ∧ p.2 = 0 := by
  change p ∈ (Finset.range k) ×ˢ ({0} : Finset ℕ) ↔ _
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_singleton]

theorem mem_column_cells (k : ℕ) (p : ℕ × ℕ) : p ∈ (column k).cells ↔ p.1 < k ∧ p.2 = 0 :=
  mem_column k p

theorem column_colLen (k : ℕ) : (column k).colLen 0 = k := by
  apply le_antisymm
  · by_contra h
    push_neg at h
    have hm : (k, 0) ∈ column k := YoungDiagram.mem_iff_lt_colLen.mpr h
    exact lt_irrefl k ((mem_column k _).mp hm).1
  · by_contra h
    push_neg at h
    have hm : ((column k).colLen 0, 0) ∈ column k := (mem_column k _).mpr ⟨h, rfl⟩
    exact lt_irrefl _ (YoungDiagram.mem_iff_lt_colLen.mp hm)

theorem column_rowLen (k r : ℕ) (hr : r < k) : (column k).rowLen r = 1 := by
  apply le_antisymm
  · by_contra h
    push_neg at h
    have hm : (r, 1) ∈ column k := YoungDiagram.mem_iff_lt_rowLen.mpr h
    exact one_ne_zero ((mem_column k (r, 1)).mp hm).2
  · have hm : (r, 0) ∈ column k := (mem_column k _).mpr ⟨hr, rfl⟩
    exact YoungDiagram.mem_iff_lt_rowLen.mp hm

/-! ## Column tableaux and strictly decreasing words -/

theorem flatten_singletons {α β : Type*} (l : List α) (f : α → β) :
    (l.map (fun r => [f r])).flatten = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem column_word_labels (n k : ℕ) (V : PositiveTableau (column k)) (hV : InAlphabet n V) :
    (rowFinWord n V hV).map (fun i => i.val + 1) =
      ((List.range k).map (fun r => V.entry r 0)).reverse := by
  rw [← TableauRowRecursion.readRows_rows]
  unfold TableauRowRecursion.readRows TableauRowRecursion.rows
  rw [List.map_flatten, List.map_reverse, List.map_map, column_colLen]
  have h : (List.range k).map ((List.map (fun i : Fin n => i.val + 1)) ∘
      TableauRowStep.row n V hV) = (List.range k).map (fun r => [V.entry r 0]) := by
    apply List.map_congr_left
    intro r hr
    simp only [Function.comp_apply, TableauRowStep.row_labels,
      column_rowLen k r (List.mem_range.mp hr)]
    rfl
  rw [h, ← List.map_reverse, flatten_singletons, List.map_reverse]

theorem column_entries_sorted (k : ℕ) (V : PositiveTableau (column k)) :
    ((List.range k).map (fun r => V.entry r 0)).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ (List.pairwise_lt_range (n := k))
  intro a b _ hb hab
  exact V.col_strict' hab ((mem_column k _).mpr ⟨List.mem_range.mp hb, rfl⟩)

theorem column_word_decreasing (n k : ℕ) (V : PositiveTableau (column k)) (hV : InAlphabet n V) :
    (rowFinWord n V hV).Pairwise (· > ·) := by
  have h := column_entries_sorted k V
  have h2 : (((List.range k).map (fun r => V.entry r 0)).reverse).Pairwise (· > ·) := by
    rw [List.pairwise_reverse]; exact h
  rw [← column_word_labels n k V hV, List.pairwise_map] at h2
  apply h2.imp
  intro a b hab
  change b.val < a.val
  omega

theorem column_word_length (n k : ℕ) (V : PositiveTableau (column k)) (hV : InAlphabet n V) :
    (rowFinWord n V hV).length = k := by
  have h := congrArg List.length (column_word_labels n k V hV)
  simpa using h

theorem map_succ_injective (n : ℕ) :
    Function.Injective (List.map (fun i : Fin n => i.val + 1)) := by
  apply List.map_injective_iff.mpr
  intro a b h
  apply Fin.ext
  change a.val + 1 = b.val + 1 at h
  omega

theorem column_ext (n k : ℕ) (V W : Tab n (column k))
    (h : rowFinWord n V.1 V.2 = rowFinWord n W.1 W.2) : V = W := by
  apply Subtype.ext
  apply TableauContent.ext_cells
  intro p hp
  obtain ⟨hpk, hp0⟩ := (mem_column k p).mp hp
  have hl := congrArg (List.map (fun i : Fin n => i.val + 1)) h
  rw [column_word_labels, column_word_labels] at hl
  have hr := List.reverse_injective hl
  have he := congrArg (fun l : List ℕ => l[p.1]?) hr
  simp only [List.getElem?_map, List.getElem?_range hpk, Option.map_some'] at he
  rw [hp0]
  exact Option.some.inj he

/-- The column tableau with (zero-based) row r holding the r-th letter of the reversed word. -/
def columnEntry {n : ℕ} (w : List (Fin n)) (r c : ℕ) : ℕ :=
  if c = 0 then ((w.reverse[r]?).map (fun x : Fin n => x.val + 1)).getD 0 else 0

def columnTableau (n k : ℕ) (w : List (Fin n)) (hw : w.Pairwise (· > ·)) (hk : w.length = k) :
    PositiveTableau (column k) where
  entry := columnEntry w
  row_weak' := by
    intro i j1 j2 hj hm
    have := ((mem_column k _).mp hm).2
    omega
  col_strict' := by
    intro i1 i2 j hi hm
    obtain ⟨hi2, hj⟩ := (mem_column k _).mp hm
    simp only at hi2 hj
    subst j
    have hl : i2 < w.reverse.length := by simpa [hk] using hi2
    have hl1 : i1 < w.reverse.length := lt_trans hi hl
    have hp : w.reverse.Pairwise (· < ·) := by
      rw [List.pairwise_reverse]; exact hw
    have hlt := List.pairwise_iff_getElem.mp hp i1 i2 hl1 hl hi
    simp only [columnEntry, ↓reduceIte, List.getElem?_eq_getElem hl1, List.getElem?_eq_getElem hl,
      Option.map_some', Option.getD_some]
    change w.reverse[i1].val < w.reverse[i2].val at hlt
    omega
  zeros' := by
    intro i j hm
    unfold columnEntry
    split_ifs with hj
    · have hi : ¬ i < k := fun hi => hm ((mem_column k _).mpr ⟨hi, hj⟩)
      rw [List.getElem?_eq_none (by simp [hk]; omega)]
      rfl
    · rfl
  positive := by
    intro i j hm
    obtain ⟨hi, hj⟩ := (mem_column k _).mp hm
    simp only at hi hj
    have hl : i < w.reverse.length := by simpa [hk] using hi
    simp [columnEntry, hj, List.getElem?_eq_getElem hl]

theorem columnTableau_bounded (n k : ℕ) (w : List (Fin n)) (hw : w.Pairwise (· > ·))
    (hk : w.length = k) : InAlphabet n (columnTableau n k w hw hk) := by
  intro p hp
  obtain ⟨hi, hj⟩ := (mem_column k _).mp hp
  have hl : p.1 < w.reverse.length := by simpa [hk] using hi
  change columnEntry w p.1 p.2 ≤ n
  simp only [columnEntry, hj, ↓reduceIte, List.getElem?_eq_getElem hl, Option.map_some',
    Option.getD_some]
  exact w.reverse[p.1].isLt

theorem range_getD {α : Type*} (l : List α) (g : α → ℕ) :
    (List.range l.length).map (fun r => ((l[r]?).map g).getD 0) = l.map g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [List.getElem?_eq_getElem h1]

theorem columnTableau_word (n k : ℕ) (w : List (Fin n)) (hw : w.Pairwise (· > ·))
    (hk : w.length = k) :
    rowFinWord n (columnTableau n k w hw hk) (columnTableau_bounded n k w hw hk) = w := by
  apply map_succ_injective n
  rw [column_word_labels]
  change ((List.range k).map (fun r => columnEntry w r 0)).reverse = _
  simp only [columnEntry, ↓reduceIte]
  have hk' : k = w.reverse.length := by simp [hk]
  rw [hk', range_getD, List.map_reverse, List.reverse_reverse]

/-! ## The (3.4) prefactor of the column is +1 -/

theorem column_directNorth (k : ℕ) : directNorth (column k) = north (column k) := by
  unfold directNorth north
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.filter_congr
  intro q hq
  have h1 := ((mem_column_cells k p).mp hp).2
  have h2 := ((mem_column_cells k q).mp hq).2
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by rw [h1, h2]⟩

theorem sp_column (n k : ℕ) : sp n (column k) = tableauPolynomial n (column k) := by
  unfold sp
  rw [column_directNorth, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-! ## Strictly decreasing insertion adds a vertical strip, top to bottom -/

theorem run_rows (n : ℕ) (S : State n) (w : List (Fin n)) (hw : w.Pairwise (· > ·)) :
    (TableauWordInsertion.run n S w).2.Pairwise (fun p q => p.1 < q.1) := by
  induction w generalizing S with
  | nil => simp [TableauWordInsertion.run]
  | cons a w ih =>
    let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
    let S' : State n := ⟨I.shape, ⟨I.tableau, I.bounded⟩⟩
    have hs := List.pairwise_cons.mp hw
    have ht := ih S' hs.2
    change (I.newCell :: (TableauWordInsertion.run n S' w).2).Pairwise (fun p q => p.1 < q.1)
    apply List.pairwise_cons.mpr
    refine ⟨?_, ht⟩
    cases w with
    | nil => simp [TableauWordInsertion.run]
    | cons b v =>
      let J := TableauInsertion.insert n S'.1 S'.2.1 S'.2.2 b
      let S'' : State n := ⟨J.shape, ⟨J.tableau, J.bounded⟩⟩
      have hba : b < a := hs.1 b (by simp)
      have hij : I.newCell.1 < J.newCell.1 :=
        (TableauBumpStrict.insert_pair_gt n S.1 S.2.1 S.2.2 a b hba).2.2.2
      change (J.newCell :: (TableauWordInsertion.run n S'' v).2).Pairwise
        (fun p q => p.1 < q.1) at ht
      intro p hp
      change p ∈ J.newCell :: (TableauWordInsertion.run n S'' v).2 at hp
      rcases List.mem_cons.mp hp with he | hm
      · subst p; exact hij
      · exact lt_trans hij ((List.pairwise_cons.mp ht).1 p hm)

theorem rows_injective (ps : List (ℕ × ℕ))
    (hs : ps.Pairwise (fun p q => p.1 < q.1)) :
    ∀ p ∈ ps, ∀ q ∈ ps, p.1 = q.1 → p = q := by
  induction ps with
  | nil => simp
  | cons a ps ih =>
    have hh := List.pairwise_cons.mp hs
    intro p hp q hq he
    rcases List.mem_cons.mp hp with hp_eq | hp_tail
    · subst p
      rcases List.mem_cons.mp hq with hq_eq | hq_tail
      · exact hq_eq.symm
      · have := hh.1 q hq_tail; omega
    · rcases List.mem_cons.mp hq with hq_eq | hq_tail
      · subst q
        have := hh.1 p hp_tail; omega
      · exact ih hh.2 p hp_tail q hq_tail he

theorem run_vertical (n : ℕ) (S : State n) (w : List (Fin n)) (hw : w.Pairwise (· > ·)) :
    Vertical S.1 (TableauWordInsertion.run n S w).1.1 := by
  have hs := TableauWordInsertion.run_spec n S w
  have hc := run_rows n S w hw
  refine ⟨hs.2.2.1, ?_⟩
  intro p hp q hq he
  rw [← hs.2.2.2] at hp hq
  exact rows_injective _ hc p (List.mem_toFinset.mp hp) q (List.mem_toFinset.mp hq) he

theorem run_card (n : ℕ) (S : State n) (w : List (Fin n)) :
    ((TableauWordInsertion.run n S w).1.1.cells \ S.1.cells).card = w.length := by
  have hs := TableauWordInsertion.run_spec n S w
  rw [← hs.2.2.2, List.toFinset_card_of_nodup hs.2.1]
  exact hs.1

/-- Conversely, a top-to-bottom history forces a strictly decreasing word (weak Row Bumping). -/
theorem word_chain_of_rows (n : ℕ) (S : State n) (w : List (Fin n))
    (h : (TableauWordInsertion.run n S w).2.Pairwise (fun p q => p.1 < q.1)) :
    w.Chain' (· > ·) := by
  induction w generalizing S with
  | nil => exact List.chain'_nil
  | cons a w ih =>
    let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
    let S' : State n := ⟨I.shape, ⟨I.tableau, I.bounded⟩⟩
    change (I.newCell :: (TableauWordInsertion.run n S' w).2).Pairwise
      (fun p q => p.1 < q.1) at h
    have ht := ih S' (List.pairwise_cons.mp h).2
    cases w with
    | nil => exact List.chain'_singleton a
    | cons b v =>
      let J := TableauInsertion.insert n S'.1 S'.2.1 S'.2.2 b
      let S'' : State n := ⟨J.shape, ⟨J.tableau, J.bounded⟩⟩
      change (I.newCell :: J.newCell :: (TableauWordInsertion.run n S'' v).2).Pairwise
        (fun p q => p.1 < q.1) at h
      have hij : I.newCell.1 < J.newCell.1 := (List.pairwise_cons.mp h).1 J.newCell (by simp)
      apply List.chain'_cons.mpr
      refine ⟨?_, ht⟩
      by_contra hab
      have hab' : a ≤ b := le_of_not_lt hab
      have hle := (TableauBumpMonotone.insert_pair_le n S.1 S.2.1 S.2.2 a b hab').2.2.2
      change J.newCell.1 ≤ I.newCell.1 at hle
      omega

theorem word_decreasing_of_rows (n : ℕ) (S : State n) (w : List (Fin n))
    (h : (TableauWordInsertion.run n S w).2.Pairwise (fun p q => p.1 < q.1)) :
    w.Pairwise (· > ·) :=
  List.chain'_iff_pairwise.mp (word_chain_of_rows n S w h)

/-! ## Uniqueness of the preimage -/

theorem row_enumeration_unique (ps qs : List (ℕ × ℕ))
    (hp : ps.Pairwise (fun p q => p.1 < q.1)) (hq : qs.Pairwise (fun p q => p.1 < q.1))
    (he : ps.toFinset = qs.toFinset) : ps = qs := by
  classical
  induction ps generalizing qs with
  | nil =>
    cases qs with
    | nil => rfl
    | cons q qs =>
      have hm : q ∈ ([] : List (ℕ × ℕ)).toFinset :=
        he.symm ▸ List.mem_toFinset.mpr List.mem_cons_self
      simp at hm
  | cons p ps ih =>
    cases qs with
    | nil => simp at he
    | cons q qs =>
      have hpm : p ∈ q :: qs := List.mem_toFinset.mp
        (he ▸ List.mem_toFinset.mpr List.mem_cons_self)
      have hqm : q ∈ p :: ps := List.mem_toFinset.mp
        (he.symm ▸ List.mem_toFinset.mpr List.mem_cons_self)
      have hp' := List.pairwise_cons.mp hp
      have hq' := List.pairwise_cons.mp hq
      have hpq : p = q := by
        rcases List.mem_cons.mp hpm with heq | hpt
        · exact heq
        · rcases List.mem_cons.mp hqm with heq | hqt
          · exact heq.symm
          · have h₁ := hp'.1 q hqt
            have h₂ := hq'.1 p hpt
            omega
      subst q
      have hnp : p ∉ ps := by
        intro h
        have := hp'.1 p h
        omega
      have hnq : p ∉ qs := by
        intro h
        have := hq'.1 p h
        omega
      have ht : ps.toFinset = qs.toFinset := by
        have hh := congrArg (fun s : Finset (ℕ × ℕ) => s.erase p) he
        simpa [hnp, hnq] using hh
      exact congrArg (List.cons p) (ih qs hp'.2 hq'.2 ht)

theorem strict_preimage_unique (n : ℕ) (A B : State n) (u v : List (Fin n))
    (hshape : A.1 = B.1) (hu : u.Pairwise (· > ·)) (hv : v.Pairwise (· > ·))
    (hfinal : (TableauWordInsertion.run n A u).1 = (TableauWordInsertion.run n B v).1) :
    (A, u) = (B, v) := by
  have hp := run_rows n A u hu
  have hq := run_rows n B v hv
  have hset : (TableauWordInsertion.run n A u).2.toFinset =
      (TableauWordInsertion.run n B v).2.toFinset := by
    rw [(TableauWordInsertion.run_spec n A u).2.2.2,
      (TableauWordInsertion.run_spec n B v).2.2.2, hshape, hfinal]
  have hhistory : (TableauWordInsertion.run n A u).2 = (TableauWordInsertion.run n B v).2 :=
    row_enumeration_unique _ _ hp hq hset
  have hA := TableauReverseWord.reverse_after_run n A u
  have hB := TableauReverseWord.reverse_after_run n B v
  unfold TableauReverseWord.afterRun at hA hB
  dsimp only at hA hB
  rw [hfinal, hhistory] at hA
  exact Option.some.inj (hA.symm.trans hB)

/-! ## Existence: bottom-to-top peeling of a vertical strip -/

theorem bottom_corner (lam mu : YoungDiagram) (p : ℕ × ℕ)
    (h : Vertical lam mu) (hp : p ∈ mu.cells \ lam.cells)
    (hm : ∀ q ∈ mu.cells \ lam.cells, q.1 ≤ p.1) : TableauCorner.IsCorner mu p := by
  obtain ⟨hpν, hpμ⟩ := Finset.mem_sdiff.mp hp
  refine ⟨hpν, ?_, ?_⟩
  · intro hb
    have hbμ : (p.1 + 1, p.2) ∉ lam.cells := by
      intro hbμ
      exact hpμ (lam.up_left_mem (Nat.le_succ _) le_rfl hbμ)
    have hc := hm (p.1 + 1, p.2) (Finset.mem_sdiff.mpr ⟨hb, hbμ⟩)
    simp only at hc
    omega
  · intro hr
    have hrμ : (p.1, p.2 + 1) ∉ lam.cells := by
      intro hrμ
      exact hpμ (lam.up_left_mem le_rfl (Nat.le_succ _) hrμ)
    have he := h.2 (p.1, p.2 + 1) (Finset.mem_sdiff.mpr ⟨hr, hrμ⟩) p hp rfl
    have hf := congrArg Prod.snd he
    simp only at hf
    omega

theorem erase_vertical (lam mu : YoungDiagram) (p : ℕ × ℕ)
    (h : Vertical lam mu) (hp : p ∈ mu.cells \ lam.cells)
    (hc : TableauCorner.IsCorner mu p) : Vertical lam (TableauCorner.eraseShape mu p hc) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    apply Finset.mem_erase.mpr
    refine ⟨?_, h.1 hq⟩
    intro he
    subst q
    exact (Finset.mem_sdiff.mp hp).2 hq
  · intro q hq r hr he
    exact h.2 q (Finset.mem_sdiff.mpr
      ⟨(Finset.mem_erase.mp (Finset.mem_sdiff.mp hq).1).2, (Finset.mem_sdiff.mp hq).2⟩)
      r (Finset.mem_sdiff.mpr
      ⟨(Finset.mem_erase.mp (Finset.mem_sdiff.mp hr).1).2, (Finset.mem_sdiff.mp hr).2⟩) he

theorem erase_difference (lam mu : YoungDiagram) (p : ℕ × ℕ)
    (hc : TableauCorner.IsCorner mu p) :
    (TableauCorner.eraseShape mu p hc).cells \ lam.cells = (mu.cells \ lam.cells).erase p := by
  ext q
  simp only [TableauCorner.erase_cells, Finset.mem_sdiff, Finset.mem_erase]
  tauto

theorem vertical_peel_order (lam mu : YoungDiagram) (ps : List (ℕ × ℕ))
    (h : Vertical lam mu) (ho : ps.Pairwise (fun p q => q.1 < p.1))
    (he : ps.toFinset = mu.cells \ lam.cells) : TableauStripCorners.PeelsTo lam mu ps := by
  induction ps generalizing mu with
  | nil =>
    apply YoungDiagram.ext
    apply Finset.Subset.antisymm
    · apply Finset.sdiff_eq_empty_iff_subset.mp
      exact he.symm
    · exact h.1
  | cons p ps ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp ho
    have hp : p ∈ mu.cells \ lam.cells := by
      rw [← he]
      simp
    have hm : ∀ q ∈ mu.cells \ lam.cells, q.1 ≤ p.1 := by
      intro q hq
      rw [← he, List.mem_toFinset] at hq
      rcases List.mem_cons.mp hq with hqp | hq
      · subst q
        exact le_rfl
      · exact (hhead q hq).le
    have hc := bottom_corner lam mu p h hp hm
    refine ⟨hc, ih (TableauCorner.eraseShape mu p hc) (erase_vertical lam mu p h hp hc) htail ?_⟩
    have hn : p ∉ ps.toFinset := by
      intro hm
      exact Nat.lt_irrefl _ (hhead p (List.mem_toFinset.mp hm))
    rw [erase_difference, ← he]
    simp [hn]

theorem decreasing_row_enumeration (s : Finset (ℕ × ℕ))
    (hi : ∀ p ∈ s, ∀ q ∈ s, p.1 = q.1 → p = q) :
    ∃ ps : List (ℕ × ℕ), ps.Pairwise (fun p q => q.1 < p.1) ∧ ps.toFinset = s := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases he : s = ∅
    · exact ⟨[], by simp, by simpa using he.symm⟩
    · obtain ⟨p, hp, hm⟩ := Finset.exists_max_image s Prod.fst
        (Finset.nonempty_iff_ne_empty.mpr he)
      have hsmall : ∀ q ∈ s.erase p, ∀ r ∈ s.erase p, q.1 = r.1 → q = r := by
        intro q hq r hr heq
        exact hi q (Finset.mem_erase.mp hq).2 r (Finset.mem_erase.mp hr).2 heq
      obtain ⟨ps, ho, hps⟩ := ih (s.erase p) (Finset.erase_ssubset hp) hsmall
      refine ⟨p :: ps, List.pairwise_cons.mpr ⟨?_, ho⟩, ?_⟩
      · intro q hq
        have hqe : q ∈ s.erase p := by
          rw [← hps]
          exact List.mem_toFinset.mpr hq
        obtain ⟨hne, hqs⟩ := Finset.mem_erase.mp hqe
        have hle := hm q hqs
        have hnc : q.1 ≠ p.1 := fun heq => hne (hi q hqs p hp heq)
        omega
      · rw [List.toFinset_cons, hps, Finset.insert_erase hp]

theorem exists_vertical_peel (lam mu : YoungDiagram) (h : Vertical lam mu) :
    ∃ ps : List (ℕ × ℕ), ps.Pairwise (fun p q => q.1 < p.1) ∧
      ps.toFinset = mu.cells \ lam.cells ∧ TableauStripCorners.PeelsTo lam mu ps := by
  obtain ⟨ps, ho, he⟩ := decreasing_row_enumeration (mu.cells \ lam.cells) h.2
  exact ⟨ps, ho, he, vertical_peel_order lam mu ps h ho he⟩

theorem vertical_exists (n : ℕ) (lam : YoungDiagram) (S : State n) (h : Vertical lam S.1) :
    ∃ Q : State n × List (Fin n), Q.1.1 = lam ∧ Q.2.Pairwise (· > ·) ∧
      Q.2.length = (S.1.cells \ lam.cells).card ∧ (TableauWordInsertion.run n Q.1 Q.2).1 = S := by
  obtain ⟨ps, ho, he, hp⟩ := exists_vertical_peel lam S.1 h
  obtain ⟨Q, hQ, hμ⟩ := TableauReverseWord.reverse_of_peels n lam S ps hp
  have hs := TableauReverseWord.reverse_spec n S ps Q hQ
  have hrun := hs.2.2.2.2
  have hrows : (TableauWordInsertion.run n Q.1 Q.2).2.Pairwise (fun p q => p.1 < q.1) := by
    rw [hrun]
    exact List.pairwise_reverse.mpr ho
  refine ⟨Q, hμ, word_decreasing_of_rows n Q.1 Q.2 hrows, ?_, congrArg Prod.fst hrun⟩
  rw [← he, List.toFinset_card_of_nodup hs.2.2.1]
  exact hs.1

/-! ## The insertion bijection -/

def VInputs (n : ℕ) (lam : YoungDiagram) (k : ℕ) :=
  {Q : State n × List (Fin n) // Q.1.1 = lam ∧ Q.2.Pairwise (· > ·) ∧ Q.2.length = k}

def VOutputs (n : ℕ) (lam : YoungDiagram) (k : ℕ) :=
  {S : State n // Vertical lam S.1 ∧ (S.1.cells \ lam.cells).card = k}

def vForward (n : ℕ) (lam : YoungDiagram) (k : ℕ) (x : VInputs n lam k) : VOutputs n lam k :=
  ⟨(TableauWordInsertion.run n x.val.1 x.val.2).1, by
    rcases x with ⟨⟨S, w⟩, hshape, hdec, hlength⟩
    dsimp only at hshape ⊢
    subst lam
    exact ⟨run_vertical n S w hdec, (run_card n S w).trans hlength⟩⟩

theorem vForward_bijective (n : ℕ) (lam : YoungDiagram) (k : ℕ) :
    Function.Bijective (vForward n lam k) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact strict_preimage_unique n x.val.1 y.val.1 x.val.2 y.val.2
      (x.property.1.trans y.property.1.symm) x.property.2.1 y.property.2.1
      (congrArg Subtype.val h)
  · intro y
    obtain ⟨Q, hμ, hw, hl, hf⟩ := vertical_exists n lam y.val y.property.1
    exact ⟨⟨Q, hμ, hw, hl.trans y.property.2⟩, Subtype.ext hf⟩

def vInsertionEquiv (n : ℕ) (lam : YoungDiagram) (k : ℕ) : VInputs n lam k ≃ VOutputs n lam k :=
  Equiv.ofBijective (vForward n lam k) (vForward_bijective n lam k)

/-! ## Signs -/

theorem no_southeast (mu : YoungDiagram) (p : ℕ × ℕ)
    (hf : p ∉ mu.cells) (q : ℕ × ℕ) (hq : q ∈ mu.cells) : ¬ (p.1 ≤ q.1 ∧ p.2 ≤ q.2) := by
  rintro ⟨hr, hc⟩
  exact hf (mu.up_left_mem hr hc hq)

/-- Adding an outer corner p raises NE by the boxes NE of p (all boxes right of its column)
plus the boxes SW of p (all boxes below its row). -/
theorem insert_northEast (mu nu : YoungDiagram) (p : ℕ × ℕ)
    (hf : p ∉ mu.cells) (he : nu.cells = insert p mu.cells) :
    northEast nu = northEast mu + rightCount mu p.2 + belowCount mu p.1 := by
  unfold northEast
  rw [he, Finset.sum_insert hf]
  have hp : (insert p mu.cells).filter (fun q => q.1 < p.1 ∧ p.2 < q.2) =
      mu.cells.filter (fun q => q.1 < p.1 ∧ p.2 < q.2) := by
    simp [Finset.filter_insert]
  have hr : (mu.cells.filter (fun q => q.1 < p.1 ∧ p.2 < q.2)).card = rightCount mu p.2 := by
    unfold rightCount
    congr 1
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hm, _, hc⟩; exact ⟨hm, hc⟩
    · rintro ⟨hm, hc⟩
      have hn := no_southeast mu p hf q hm
      exact ⟨hm, by omega, hc⟩
  have hsplit : ∀ x ∈ mu.cells,
      ((insert p mu.cells).filter (fun q => q.1 < x.1 ∧ x.2 < q.2)).card =
        (mu.cells.filter (fun q => q.1 < x.1 ∧ x.2 < q.2)).card +
          if p.1 < x.1 then 1 else 0 := by
    intro x hx
    rw [Finset.filter_insert]
    by_cases hx1 : p.1 < x.1
    · have hx2 : x.2 < p.2 := by
        have hn := no_southeast mu p hf x hx
        omega
      rw [if_pos ⟨hx1, hx2⟩, if_pos hx1, Finset.card_insert_of_not_mem]
      intro hm
      exact hf (Finset.mem_filter.mp hm).1
    · rw [if_neg (fun h => hx1 h.1), if_neg hx1]
      rfl
  rw [hp, hr, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  unfold belowCount
  rw [Finset.card_filter]
  omega

theorem neg_one_pow_congr {a b x y : ℕ} (h : a + 2 * x = b + 2 * y) :
    (-1 : ℤ) ^ a = (-1 : ℤ) ^ b := by
  have ha : (-1 : ℤ) ^ (a + 2 * x) = (-1) ^ a := by rw [pow_add, pow_mul]; norm_num
  have hb : (-1 : ℤ) ^ (b + 2 * y) = (-1) ^ b := by rw [pow_add, pow_mul]; norm_num
  rw [← ha, ← hb, h]

theorem belowCount_insert (mu nu : YoungDiagram) (p : ℕ × ℕ)
    (he : nu.cells = insert p mu.cells) (r : ℕ) (hr : p.1 ≤ r) :
    belowCount nu r = belowCount mu r := by
  unfold belowCount
  rw [he]
  simp [Finset.filter_insert, show ¬ r < p.1 by omega]

set_option maxHeartbeats 1600000 in
/-- Telescoped sign bookkeeping for a strictly decreasing inserted word. -/
theorem run_parity (n : ℕ) (S : State n) (w : List (Fin n)) (hw : w.Pairwise (· > ·)) :
    ∃ X : ℕ, northWest S.1 + northEast (TableauWordInsertion.run n S w).1.1 + crossings n S w =
      northWest (TableauWordInsertion.run n S w).1.1 + northEast S.1 + 2 * X +
        histBelow S.1 (TableauWordInsertion.run n S w).2 := by
  induction w generalizing S with
  | nil => exact ⟨0, by simp [TableauWordInsertion.run, crossings, histBelow]⟩
  | cons a w ih =>
    let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
    let S' : State n := ⟨I.shape, ⟨I.tableau, I.bounded⟩⟩
    let R := TableauWordInsertion.run n S' w
    have hc := TableauInsertion.insert_cells n S.1 S.2.1 S.2.2 a
    have hi := insert_crossings_shape n S a
    change northWest S.1 + I.crossings = northWest S'.1 + rightCount S.1 I.newCell.2 at hi
    have hne := insert_northEast S.1 S'.1 I.newCell hc.1 hc.2
    obtain ⟨X, hX⟩ := ih S' (List.pairwise_cons.mp hw).2
    change northWest S'.1 + northEast R.1.1 + crossings n S' w =
      northWest R.1.1 + northEast S'.1 + 2 * X + histBelow S'.1 R.2 at hX
    have hh := run_rows n S (a :: w) hw
    change (I.newCell :: R.2).Pairwise (fun p q => p.1 < q.1) at hh
    have hb : histBelow S'.1 R.2 = histBelow S.1 R.2 := by
      unfold histBelow
      rw [List.map_congr_left (fun p hp =>
        belowCount_insert S.1 S'.1 I.newCell hc.2 p.1 ((List.pairwise_cons.mp hh).1 p hp).le)]
    rw [hb] at hX
    refine ⟨X + rightCount S.1 I.newCell.2, ?_⟩
    change northWest S.1 + northEast R.1.1 + (I.crossings + crossings n S' w) =
      northWest R.1.1 + northEast S.1 + 2 * (X + rightCount S.1 I.newCell.2) +
        histBelow S.1 (I.newCell :: R.2)
    simp only [histBelow, List.map_cons, List.sum_cons] at hX ⊢
    omega

/-- Pointwise (3.10) with the source normalization (3.4) on both sides. -/
theorem run_polynomial (n : ℕ) (S : State n) (w : List (Fin n)) (hw : w.Pairwise (· > ·)) :
    (-1 : ℤ) ^ (directNorth S.1 + north S.1) •
      (rowPolynomial n S.2.1 S.2.2 * PlacticEvaluation.toSkew n (OddPlactic.word n w)) =
    (-1 : ℤ) ^ (directNorth (TableauWordInsertion.run n S w).1.1 +
        north (TableauWordInsertion.run n S w).1.1 +
        histBelow S.1 (TableauWordInsertion.run n S w).2) •
      rowPolynomial n (TableauWordInsertion.run n S w).1.2.1
        (TableauWordInsertion.run n S w).1.2.2 := by
  have h := congrArg (PlacticEvaluation.toSkew n) (run_word n S w)
  simp only [OddPlactic.word_append, map_mul, map_zsmul] at h
  change rowPolynomial n S.2.1 S.2.2 * PlacticEvaluation.toSkew n (OddPlactic.word n w) =
    (-1 : ℤ) ^ crossings n S w • rowPolynomial n
      (TableauWordInsertion.run n S w).1.2.1 (TableauWordInsertion.run n S w).1.2.2 at h
  rw [h, smul_smul, ← pow_add]
  congr 1
  obtain ⟨X, hX⟩ := run_parity n S w hw
  have h1 := shape_partition S.1
  have h2 := shape_partition (TableauWordInsertion.run n S w).1.1
  apply neg_one_pow_congr (x := directNorth (TableauWordInsertion.run n S w).1.1 +
      northEast (TableauWordInsertion.run n S w).1.1)
    (y := X + directNorth S.1 + northEast S.1)
  omega

theorem run_histBelow (n : ℕ) (S : State n) (w : List (Fin n)) :
    histBelow S.1 (TableauWordInsertion.run n S w).2 =
      stripBelow S.1 (TableauWordInsertion.run n S w).1.1 := by
  have hs := TableauWordInsertion.run_spec n S w
  unfold histBelow stripBelow
  rw [← hs.2.2.2, List.sum_toFinset _ hs.2.1]

/-! ## Aggregation -/

def inputMap (n : ℕ) (lam : YoungDiagram) (k : ℕ) (x : Tab n lam × Tab n (column k)) :
    VInputs n lam k :=
  ⟨(⟨lam, x.1⟩, rowFinWord n x.2.1 x.2.2), rfl, column_word_decreasing n k x.2.1 x.2.2,
    column_word_length n k x.2.1 x.2.2⟩

theorem inputMap_bijective (n : ℕ) (lam : YoungDiagram) (k : ℕ) :
    Function.Bijective (inputMap n lam k) := by
  constructor
  · intro x y h
    have hs := congrArg (fun z : VInputs n lam k => z.val.1) h
    have hw := congrArg (fun z : VInputs n lam k => z.val.2) h
    apply Prod.ext
    · exact eq_of_heq (Sigma.mk.inj hs).2
    · exact column_ext n k x.2 y.2 hw
  · rintro ⟨⟨⟨nu, T⟩, w⟩, hμ, hw, hk⟩
    dsimp only at hμ hk hw
    subst nu
    refine ⟨(T, ⟨columnTableau n k w hw hk, columnTableau_bounded n k w hw hk⟩), Subtype.ext ?_⟩
    change ((⟨lam, T⟩ : State n), rowFinWord n (columnTableau n k w hw hk)
      (columnTableau_bounded n k w hw hk)) = _
    rw [columnTableau_word]

def inputEquiv (n : ℕ) (lam : YoungDiagram) (k : ℕ) :
    Tab n lam × Tab n (column k) ≃ VInputs n lam k :=
  Equiv.ofBijective (inputMap n lam k) (inputMap_bijective n lam k)

abbrev Outer (lam : YoungDiagram) (k : ℕ) :=
  {nu : DegreeShape (lam.card + k) // Vertical lam nu.val}
abbrev Indexed (n : ℕ) (lam : YoungDiagram) (k : ℕ) := Σ nu : Outer lam k, Tab n nu.val.val

def outputMap (n : ℕ) (lam : YoungDiagram) (k : ℕ) (y : Indexed n lam k) : VOutputs n lam k :=
  ⟨⟨y.1.val.val, y.2⟩, y.1.property, by
    rw [Finset.card_sdiff y.1.property.1]
    change y.1.val.val.card - lam.card = k
    rw [y.1.val.property]; omega⟩

theorem outputMap_bijective (n : ℕ) (lam : YoungDiagram) (k : ℕ) :
    Function.Bijective (outputMap n lam k) := by
  constructor
  · rintro ⟨⟨⟨nu, hd⟩, hh⟩, T⟩ ⟨⟨⟨nu', hd'⟩, hh'⟩, T'⟩ h
    have he := congrArg Subtype.val h
    have hs := congrArg Sigma.fst he
    dsimp only [outputMap] at hs
    subst nu'
    have ht : T = T' := eq_of_heq (Sigma.mk.inj he).2
    subst T'
    rfl
  · rintro ⟨⟨nu, T⟩, hh, hk⟩
    change (nu.cells \ lam.cells).card = k at hk
    have hd : nu.card = lam.card + k := by
      have hc := Finset.card_sdiff_add_card_eq_card hh.1
      change (nu.cells \ lam.cells).card + lam.card = nu.card at hc
      omega
    exact ⟨⟨⟨⟨nu, hd⟩, hh⟩, T⟩, rfl⟩

def outputEquiv (n : ℕ) (lam : YoungDiagram) (k : ℕ) : Indexed n lam k ≃ VOutputs n lam k :=
  Equiv.ofBijective (outputMap n lam k) (outputMap_bijective n lam k)

def aggregateEquiv (n : ℕ) (lam : YoungDiagram) (k : ℕ) :
    Tab n lam × Tab n (column k) ≃ Indexed n lam k :=
  (inputEquiv n lam k).trans ((vInsertionEquiv n lam k).trans (outputEquiv n lam k).symm)

def inputValue (n : ℕ) (lam : YoungDiagram) (k : ℕ) (x : Tab n lam × Tab n (column k)) :
    SkewPolynomial n :=
  (-1 : ℤ) ^ (directNorth lam + north lam) •
    (rowPolynomial n x.1.val x.1.property * rowPolynomial n x.2.val x.2.property)

def outputValue (n : ℕ) (lam : YoungDiagram) (S : State n) : SkewPolynomial n :=
  (-1 : ℤ) ^ (directNorth S.1 + north S.1 + stripBelow lam S.1) •
    rowPolynomial n S.2.val S.2.property

theorem pointwise (n : ℕ) (lam : YoungDiagram) (k : ℕ) (x : Tab n lam × Tab n (column k)) :
    inputValue n lam k x = outputValue n lam (outputMap n lam k (aggregateEquiv n lam k x)).val := by
  have he : outputMap n lam k (aggregateEquiv n lam k x) =
      vInsertionEquiv n lam k (inputMap n lam k x) :=
    (outputEquiv n lam k).apply_symm_apply _
  rw [he]
  change inputValue n lam k x = outputValue n lam
    (TableauWordInsertion.run n ⟨lam, x.1⟩ (rowFinWord n x.2.1 x.2.2)).1
  have h := run_polynomial n ⟨lam, x.1⟩ (rowFinWord n x.2.1 x.2.2)
    (column_word_decreasing n k x.2.1 x.2.2)
  rw [run_histBelow] at h
  exact h

theorem tableau_sum (n : ℕ) (mu : YoungDiagram) :
    tableauPolynomial n mu = ∑ T : Tab n mu, rowPolynomial n T.val T.property :=
  TableauHorizontalPieri.tableau_sum n mu

theorem input_sum (n : ℕ) (lam : YoungDiagram) (k : ℕ) :
    sp n lam * sp n (column k) = ∑ x : Tab n lam × Tab n (column k), inputValue n lam k x := by
  classical
  rw [sp_column]
  unfold sp
  rw [tableau_sum, tableau_sum, Fintype.sum_prod_type, smul_mul_assoc, Finset.sum_mul_sum,
    Finset.smul_sum]
  simp only [inputValue, Finset.smul_sum]

theorem output_sum (n : ℕ) (lam : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (lam.card + k)
    ∑ y : Indexed n lam k, outputValue n lam (outputMap n lam k y).val =
      ∑ nu : DegreeShape (lam.card + k), if Vertical lam nu.val then
        (-1 : ℤ) ^ stripBelow lam nu.val • sp n nu.val
      else 0 := by
  classical
  letI := degreeFintype (lam.card + k)
  rw [Fintype.sum_sigma]
  have hv : ∀ nu : Outer lam k, ∑ T : Tab n nu.val.val,
      outputValue n lam (outputMap n lam k ⟨nu, T⟩).val =
      (-1 : ℤ) ^ stripBelow lam nu.val.val • sp n nu.val.val := by
    intro nu
    simp only [outputValue, outputMap]
    rw [← Finset.smul_sum, ← tableau_sum]
    unfold sp
    rw [smul_smul, ← pow_add]
    congr 2
    ring
  rw [Fintype.sum_congr _ _ hv]
  rw [← Finset.sum_filter]
  symm
  exact Finset.sum_subtype _ (by simp) _

/-- **Ellis (3.10)**, e-right Pieri rule for the plactic odd Schur functions s^p, exactly as
printed: s^p_λ s^p_(1^k) = ∑_{μ/λ vertical k-strip} (-1)^{|i_1/λ|+…+|i_k/λ|} s^p_μ, in
`SkewPolynomial n` for every n, λ and k (all shapes of degree |λ|+k are summed; those with more
than n rows vanish in the existing `sp`). -/
theorem vertical_pieri (n : ℕ) (lam : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (lam.card + k)
    sp n lam * sp n (column k) =
      ∑ mu : DegreeShape (lam.card + k), if Vertical lam mu.val then
        (-1 : ℤ) ^ stripBelow lam mu.val • sp n mu.val
      else 0 := by
  classical
  letI := degreeFintype (lam.card + k)
  rw [input_sum, ← output_sum]
  exact Fintype.sum_equiv (aggregateEquiv n lam k) _ _ (pointwise n lam k)

end
end OddMath.Frontier.OddLRVerticalPieri
