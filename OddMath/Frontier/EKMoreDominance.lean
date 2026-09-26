import OddMath.Frontier.EKProp310
import OddMath.Frontier.EKNondegeneracy
import OddMath.Frontier.EKAppendixData
import OddMath.Frontier.OddLRExamplesTools

/-!
# [EK] §2.2, p. 16: the dominance order on partitions

Source: A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*,
arXiv:1107.5610v2, p. 16:

  "The dominance partial order is a total order if and only if `n ≤ 5` and is graded if and only
  if `n ≤ 6`. The lowest degree dominance-incomparable pairs are `{(3,1,1,1),(2,2,2)}` and
  `{(4,1,1),(3,3)}`.
  If all partitions of `n` are listed lexicographically, it is not true that reversing the order
  swaps partitions whose corresponding Young diagrams are transposes of each other (this first
  occurs at `n = 6`). One can, however, refine the dominance partial order in such a way that
  this property holds."

Partitions of `n` are the library's `DegreeShape n` (Young diagrams with `n` cells), dominance is
`EKProp310.Dom` (row-prefix cell counts), the lexicographic order is `EKProp310.LexLT` and the
transpose is Mathlib's `YoungDiagram.transpose`. The paper does not define "graded"; we use the
standard notion: there is a rank function `ρ` with `ρ(μ) = ρ(λ) + 1` whenever `μ` covers `λ`
(for a finite bounded poset this is equivalent to all maximal chains having the same length).

* `ek_p16_total_iff`: dominance on partitions of `n` is total iff `n ≤ 5`.
* `ek_p16_graded_iff`: dominance on partitions of `n` is graded iff `n ≤ 6`. For `n = k + 7` the
  interval `[(3+k,2,1,1), (4+k,2,1)]` has saturated chains of lengths `2` and `3`.
* `ek_p16_lowest_incomparable`: in degree `6` the incomparable pairs are exactly the two printed
  ones (and there are none in degrees `≤ 5`).
* `ek_p16_lex_reversal_iff`: for a listing of the partitions of `n` in increasing lexicographic
  order, reversal swaps transposes iff `n ≤ 5`.
* `ek_p16_refinement_iff`: there is a listing refining dominance whose reversal swaps transposes
  iff `n ≤ 7`. **The printed claim fails for every `n ≥ 8`**: then there are two distinct
  self-transpose partitions (`two_self_transpose`), and both would have to occupy the middle
  position of the list; no listing at all has the property (`no_listing_rev_swaps`).
-/

set_option maxRecDepth 100000
open scoped BigOperators

namespace OddMath.Frontier.EKMore
open DegreeShapes TableauDominance
open EKProp310 (Dom LexLT)

/-! ## Row-length lists -/

/-- Sum of the first `k` entries of a list. -/
def pre (w : List ℕ) (k : ℕ) : ℕ := (w.take k).sum

theorem pre_zero (w : List ℕ) : pre w 0 = 0 := by simp [pre]

theorem pre_succ (w : List ℕ) (k : ℕ) : pre w (k + 1) = pre w k + w.getD k 0 := by
  induction w generalizing k with
  | nil => simp [pre]
  | cons a t ih =>
    cases k with
    | zero => simp [pre]
    | succ k =>
      have h := ih k
      simp only [pre, List.take_succ_cons, List.sum_cons, List.getD_cons_succ] at h ⊢
      omega

theorem pre_of_le (w : List ℕ) {k : ℕ} (h : w.length ≤ k) : pre w k = w.sum := by
  simp [pre, List.take_of_length_le h]

theorem length_le_sum (w : List ℕ) (hp : ∀ x ∈ w, 0 < x) : w.length ≤ w.sum := by
  induction w with
  | nil => simp
  | cons a t ih =>
    have ha := hp a (by simp)
    have := ih (fun x hx => hp x (by simp [hx]))
    simp only [List.length_cons, List.sum_cons]
    omega

theorem rowLen_eq_getD (μ : YoungDiagram) (i : ℕ) : μ.rowLen i = μ.rowLens.getD i 0 := by
  by_cases h : i < μ.colLen 0
  · rw [List.getD_eq_getElem _ _ (by rwa [YoungDiagram.length_rowLens])]
    simp [YoungDiagram.rowLens]
  · rw [List.getD_eq_default _ _ (by rw [YoungDiagram.length_rowLens]; omega)]
    by_contra hne
    have hm : (i, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    exact h (YoungDiagram.mem_iff_lt_colLen.mp hm)

theorem shapePrefix_eq_pre (μ : YoungDiagram) (k : ℕ) : shapePrefix μ k = pre μ.rowLens k := by
  induction k with
  | zero => rw [EKProp310.shapePrefix_zero, pre_zero]
  | succ k ih => rw [SignedKostkaInvertibility.shapePrefix_succ, ih, pre_succ, rowLen_eq_getD]

theorem yd_ext_rowLen {μ ν : YoungDiagram} (h : ∀ i, μ.rowLen i = ν.rowLen i) : μ = ν := by
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, h]

theorem rowLens_pos (μ : YoungDiagram) : ∀ x ∈ μ.rowLens, 0 < x := μ.pos_of_mem_rowLens

theorem rowLens_sum' {n : ℕ} (a : DegreeShape n) : a.val.rowLens.sum = n := by
  rw [EKIntegralBases.rowLens_sum, a.property]

theorem shape_ext {n : ℕ} {a b : DegreeShape n} (h : a.val.rowLens = b.val.rowLens) : a = b :=
  Subtype.ext (EKAppendixData.shape_eq_of_rowLens h)

/-- Dominance through prefix sums of row lengths, checked on `k ≤ n`. -/
theorem dom_iff_pre {n : ℕ} (a b : DegreeShape n) :
    Dom a.val b.val ↔ ∀ k ≤ n, pre a.val.rowLens k ≤ pre b.val.rowLens k := by
  constructor
  · intro h k _
    rw [← shapePrefix_eq_pre, ← shapePrefix_eq_pre]
    exact h k
  · intro h k
    rw [shapePrefix_eq_pre, shapePrefix_eq_pre]
    by_cases hk : k ≤ n
    · exact h k hk
    · have ha := length_le_sum _ (rowLens_pos a.val)
      have hb := length_le_sum _ (rowLens_pos b.val)
      rw [rowLens_sum'] at ha hb
      rw [pre_of_le _ (by omega), pre_of_le _ (by omega), rowLens_sum', rowLens_sum']

/-- Boolean dominance of row-length lists of partitions of `n`. -/
def ldom (n : ℕ) (v w : List ℕ) : Bool :=
  (List.range (n + 1)).all fun k => decide (pre v k ≤ pre w k)

theorem ldom_iff {n : ℕ} {v w : List ℕ} : ldom n v w = true ↔ ∀ k ≤ n, pre v k ≤ pre w k := by
  simp [ldom, Nat.lt_succ_iff]

theorem dom_iff_ldom {n : ℕ} (a b : DegreeShape n) :
    Dom a.val b.val ↔ ldom n a.val.rowLens b.val.rowLens = true := by
  rw [dom_iff_pre, ldom_iff]

/-- The partitions of `n` as row-length lists, in increasing lexicographic order. -/
def P (n : ℕ) : List (List ℕ) := EKNondegeneracy.partsF n n n

theorem rowLens_mem_P {n : ℕ} (a : DegreeShape n) : a.val.rowLens ∈ P n :=
  EKNondegeneracy.rowLens_mem_parts n a.val a.property

/-- The shape with row lengths `w`. -/
def mk {n : ℕ} (w : List ℕ) (hs : w.Sorted (· ≥ ·)) (hsum : w.sum = n) : DegreeShape n :=
  ⟨YoungDiagram.ofRowLens w hs, by rw [EKPartitionSpanning.card_ofRowLens, hsum]⟩

theorem mk_rowLens {n : ℕ} {w : List ℕ} {hs : w.Sorted (· ≥ ·)} {hsum : w.sum = n}
    (hp : ∀ x ∈ w, 0 < x) : (mk w hs hsum).val.rowLens = w :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := hs) hp

theorem mk_rowLen {n : ℕ} {w : List ℕ} {hs : w.Sorted (· ≥ ·)} {hsum : w.sum = n}
    (hp : ∀ x ∈ w, 0 < x) (i : ℕ) : (mk w hs hsum).val.rowLen i = w.getD i 0 := by
  rw [rowLen_eq_getD, mk_rowLens hp]

/-- The conjugate partition, from row lengths: `λᵀ_i = #{j : λ_j > i}`. -/
def conjL (w : List ℕ) : List ℕ := (List.range (w.headD 0)).map fun i => (w.filter (fun x => i < x)).length

/-- Every row-length list of a partition of `n` is weakly decreasing and positive with sum `n`,
and its conjugate describes the transposed diagram. -/
abbrev Cert (n : ℕ) : Prop :=
  ∀ w ∈ P n, w.Sorted (· ≥ ·) ∧ (∀ x ∈ w, 0 < x) ∧ w.sum = n ∧ (conjL w).Sorted (· ≥ ·) ∧
    (∀ x ∈ conjL w, 0 < x) ∧
    (Equiv.prodComm ℕ ℕ).finsetCongr (YoungDiagram.cellsOfRowLens w) =
      YoungDiagram.cellsOfRowLens (conjL w)

theorem cert_le {n : ℕ} (hn : n ≤ 7) : Cert n := by
  interval_cases n <;> decide

def mkP {n : ℕ} (hc : Cert n) (w : List ℕ) (hw : w ∈ P n) : DegreeShape n :=
  mk w (hc w hw).1 (hc w hw).2.2.1

theorem mkP_rowLens {n : ℕ} (hc : Cert n) (w : List ℕ) (hw : w ∈ P n) :
    (mkP hc w hw).val.rowLens = w := mk_rowLens (hc w hw).2.1

/-- In degrees `≤ 7` the transpose acts on row lengths by `conjL`. -/
theorem transpose_rowLens {n : ℕ} (hc : Cert n) (a : DegreeShape n) :
    a.val.transpose.rowLens = conjL a.val.rowLens := by
  have hw := hc _ (rowLens_mem_P a)
  have e1 : a.val = YoungDiagram.ofRowLens a.val.rowLens hw.1 :=
    YoungDiagram.ofRowLens_to_rowLens_eq_self.symm
  have e2 : a.val.transpose = YoungDiagram.ofRowLens (conjL a.val.rowLens) hw.2.2.2.1 := by
    rw [congrArg YoungDiagram.transpose e1]
    apply YoungDiagram.ext
    exact hw.2.2.2.2.2
  rw [e2, YoungDiagram.rowLens_ofRowLens_eq_self hw.2.2.2.2.1]

/-! ## Totality -/

/-- Dominance is a total order on the partitions of `n`. -/
def DomTotal (n : ℕ) : Prop := ∀ a b : DegreeShape n, Dom a.val b.val ∨ Dom b.val a.val

theorem total_of_list {n : ℕ} (h : ∀ v ∈ P n, ∀ w ∈ P n, ldom n v w = true ∨ ldom n w v = true) :
    DomTotal n := fun a b => by
  rw [dom_iff_ldom, dom_iff_ldom]; exact h _ (rowLens_mem_P a) _ (rowLens_mem_P b)

theorem sorted_of_chain (w : List ℕ) (h : w.Chain' (· ≥ ·)) : w.Sorted (· ≥ ·) :=
  List.chain'_iff_pairwise.mp h

theorem not_total {n : ℕ} (hn : 6 ≤ n) : ¬ DomTotal n := by
  intro h
  have hp1 : ∀ x ∈ [n - 3, 1, 1, 1], 0 < x := by simp; omega
  have hp2 : ∀ x ∈ [n - 4, 2, 2], 0 < x := by simp; omega
  let a : DegreeShape n := mk [n - 3, 1, 1, 1]
    (sorted_of_chain _ (by simp [List.chain'_cons] ; omega)) (by simp; omega)
  let b : DegreeShape n := mk [n - 4, 2, 2]
    (sorted_of_chain _ (by simp [List.chain'_cons] ; omega)) (by simp; omega)
  rcases h a b with h1 | h1
  · have := h1 1
    rw [shapePrefix_eq_pre, shapePrefix_eq_pre, mk_rowLens hp1, mk_rowLens hp2] at this
    simp [pre] at this
    omega
  · have := h1 3
    rw [shapePrefix_eq_pre, shapePrefix_eq_pre, mk_rowLens hp1, mk_rowLens hp2] at this
    simp [pre] at this
    omega

/-- [EK] p. 16: dominance on partitions of `n` is a total order iff `n ≤ 5`. -/
theorem ek_p16_total_iff (n : ℕ) : DomTotal n ↔ n ≤ 5 := by
  constructor
  · intro h
    by_contra hn
    exact not_total (by omega) h
  · intro hn
    apply total_of_list
    interval_cases n <;> decide

/-- [EK] p. 16: the lowest-degree incomparable pairs. -/
theorem ek_p16_lowest_incomparable :
    (∀ n ≤ 5, DomTotal n) ∧ ∀ a b : DegreeShape 6,
      (¬ Dom a.val b.val ∧ ¬ Dom b.val a.val) ↔
        (a.val.rowLens, b.val.rowLens) ∈ [([3, 1, 1, 1], [2, 2, 2]), ([2, 2, 2], [3, 1, 1, 1]),
          ([4, 1, 1], [3, 3]), ([3, 3], [4, 1, 1])] := by
  refine ⟨fun n hn => (ek_p16_total_iff n).mpr hn, fun a b => ?_⟩
  rw [dom_iff_ldom, dom_iff_ldom]
  have key : ∀ v ∈ P 6, ∀ w ∈ P 6, (¬ ldom 6 v w = true ∧ ¬ ldom 6 w v = true) ↔
      (v, w) ∈ [([3, 1, 1, 1], [2, 2, 2]), ([2, 2, 2], [3, 1, 1, 1]),
          ([4, 1, 1], [3, 3]), ([3, 3], [4, 1, 1])] := by decide
  exact key _ (rowLens_mem_P a) _ (rowLens_mem_P b)

/-! ## Gradedness -/

/-- `b` covers `a` in the dominance order on partitions of `n`. -/
def DomCovBy {n : ℕ} (a b : DegreeShape n) : Prop :=
  Dom a.val b.val ∧ a ≠ b ∧ ∀ c : DegreeShape n, Dom a.val c.val → Dom c.val b.val → c = a ∨ c = b

/-- The dominance order on partitions of `n` is graded: it has a rank function. -/
def DomGraded (n : ℕ) : Prop :=
  ∃ ρ : DegreeShape n → ℕ, ∀ a b, DomCovBy a b → ρ b = ρ a + 1

/-- Boolean cover relation on row-length lists. -/
def lcov (n : ℕ) (v w : List ℕ) : Bool :=
  ldom n v w && !(v == w) &&
    (P n).all (fun u => !(ldom n v u && ldom n u w) || (u == v || u == w))

theorem lcov_of_cov {n : ℕ} (hc : Cert n) {a b : DegreeShape n} (h : DomCovBy a b) :
    lcov n a.val.rowLens b.val.rowLens = true := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [lcov, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_iff_eq]
  refine ⟨⟨(dom_iff_ldom a b).mp h1, fun he => h2 (shape_ext he)⟩, fun u hu => ?_⟩
  by_cases hd : ldom n a.val.rowLens u = true ∧ ldom n u b.val.rowLens = true
  · right
    have e := mkP_rowLens hc u hu
    have hac : Dom a.val (mkP hc u hu).val := by rw [dom_iff_ldom, e]; exact hd.1
    have hcb : Dom (mkP hc u hu).val b.val := by rw [dom_iff_ldom, e]; exact hd.2
    rcases h3 _ hac hcb with hc' | hc'
    · left; rw [← e, hc']
    · right; rw [← e, hc']
  · left
    by_contra hne
    simp only [Bool.not_eq_false] at hne
    exact hd ⟨by cases h' : ldom n a.val.rowLens u <;> simp_all,
      by cases h' : ldom n u b.val.rowLens <;> simp_all⟩

/-- Ranks of the partitions of `n ≤ 6` (length of the longest chain from `(1ⁿ)`). -/
def rkTable : List (List ℕ × ℕ) :=
  [([], 0), ([1], 0), ([1, 1], 0), ([2], 1), ([1, 1, 1], 0), ([2, 1], 1), ([3], 2),
    ([1, 1, 1, 1], 0), ([2, 1, 1], 1), ([2, 2], 2), ([3, 1], 3), ([4], 4),
    ([1, 1, 1, 1, 1], 0), ([2, 1, 1, 1], 1), ([2, 2, 1], 2), ([3, 1, 1], 3), ([3, 2], 4),
    ([4, 1], 5), ([5], 6),
    ([1, 1, 1, 1, 1, 1], 0), ([2, 1, 1, 1, 1], 1), ([2, 2, 1, 1], 2), ([2, 2, 2], 3),
    ([3, 1, 1, 1], 3), ([3, 2, 1], 4), ([3, 3], 5), ([4, 1, 1], 5), ([4, 2], 6), ([5, 1], 7),
    ([6], 8)]

def rk (w : List ℕ) : ℕ := (rkTable.lookup w).getD 0

theorem graded_of_list {n : ℕ} (hc : Cert n)
    (h : ∀ v ∈ P n, ∀ w ∈ P n, lcov n v w = true → rk w = rk v + 1) : DomGraded n :=
  ⟨fun a => rk a.val.rowLens, fun a b hab =>
    h _ (rowLens_mem_P a) _ (rowLens_mem_P b) (lcov_of_cov hc hab)⟩

/-- A cover criterion: every shape between `a` and `b` has the row lengths of `a` or of `b`. -/
theorem covBy_of {n : ℕ} {a b : DegreeShape n} (hab : Dom a.val b.val)
    (hne : a.val.rowLens ≠ b.val.rowLens)
    (h : ∀ c : DegreeShape n, Dom a.val c.val → Dom c.val b.val →
      (∀ i, c.val.rowLen i = a.val.rowLen i) ∨ (∀ i, c.val.rowLen i = b.val.rowLen i)) :
    DomCovBy a b := by
  refine ⟨hab, fun he => hne (by rw [he]), fun c h1 h2 => ?_⟩
  rcases h c h1 h2 with h' | h'
  · exact Or.inl (Subtype.ext (yd_ext_rowLen h'))
  · exact Or.inr (Subtype.ext (yd_ext_rowLen h'))

/-- Prefix bounds for a shape between two shapes. -/
theorem pinned {n : ℕ} {a b c : DegreeShape n} (h1 : Dom a.val c.val) (h2 : Dom c.val b.val)
    (j : ℕ) : pre a.val.rowLens j ≤ pre c.val.rowLens j ∧ pre c.val.rowLens j ≤ pre b.val.rowLens j := by
  have e1 := h1 j
  have e2 := h2 j
  rw [shapePrefix_eq_pre, shapePrefix_eq_pre] at e1 e2
  exact ⟨e1, e2⟩

theorem pre_c_succ (c : YoungDiagram) (j : ℕ) :
    pre c.rowLens (j + 1) = pre c.rowLens j + c.rowLen j := by
  rw [pre_succ, rowLen_eq_getD]

theorem c_facts (c : YoungDiagram) :
    pre c.rowLens 1 = c.rowLen 0 ∧ pre c.rowLens 2 = pre c.rowLens 1 + c.rowLen 1 ∧
    pre c.rowLens 3 = pre c.rowLens 2 + c.rowLen 2 ∧ pre c.rowLens 4 = pre c.rowLens 3 + c.rowLen 3 ∧
    pre c.rowLens 5 = pre c.rowLens 4 + c.rowLen 4 ∧ c.rowLen 1 ≤ c.rowLen 0 ∧
    c.rowLen 2 ≤ c.rowLen 1 ∧ c.rowLen 3 ≤ c.rowLen 2 ∧ c.rowLen 4 ≤ c.rowLen 3 := by
  have s0 := pre_c_succ c 0
  simp only [pre_zero, zero_add] at s0
  exact ⟨s0, pre_c_succ c 1, pre_c_succ c 2, pre_c_succ c 3, pre_c_succ c 4,
    c.rowLen_anti 0 1 (by omega), c.rowLen_anti 1 2 (by omega), c.rowLen_anti 2 3 (by omega),
    c.rowLen_anti 3 4 (by omega)⟩

theorem rowLen_tail {c : YoungDiagram} (w : List ℕ) (hw : w.length ≤ 4)
    (h : ∀ i < 4, c.rowLen i = w.getD i 0) (h4 : c.rowLen 4 = 0) : ∀ i, c.rowLen i = w.getD i 0 := by
  intro i
  by_cases hi : i < 4
  · exact h i hi
  · rw [List.getD_eq_default _ _ (by omega)]
    have := c.rowLen_anti 4 i (by omega)
    omega

section Chains
variable (k : ℕ)

theorem sx : [3 + k, 2, 1, 1].Sorted (· ≥ ·) := sorted_of_chain _ (by simp [List.chain'_cons] ; omega)
theorem sm : [4 + k, 1, 1, 1].Sorted (· ≥ ·) := sorted_of_chain _ (by simp [List.chain'_cons] ; omega)
theorem sy : [4 + k, 2, 1].Sorted (· ≥ ·) := sorted_of_chain _ (by simp [List.chain'_cons] ; omega)
theorem sp : [3 + k, 2, 2].Sorted (· ≥ ·) := sorted_of_chain _ (by simp [List.chain'_cons] ; omega)
theorem sq : [3 + k, 3, 1].Sorted (· ≥ ·) := sorted_of_chain _ (by simp [List.chain'_cons])

/-- `(3+k,2,1,1)`. -/
def shX : DegreeShape (k + 7) := mk [3 + k, 2, 1, 1] (sx k) (by simp; omega)
/-- `(4+k,1,1,1)`. -/
def shM : DegreeShape (k + 7) := mk [4 + k, 1, 1, 1] (sm k) (by simp; omega)
/-- `(4+k,2,1)`. -/
def shY : DegreeShape (k + 7) := mk [4 + k, 2, 1] (sy k) (by simp; omega)
/-- `(3+k,2,2)`. -/
def shP : DegreeShape (k + 7) := mk [3 + k, 2, 2] (sp k) (by simp; omega)
/-- `(3+k,3,1)`. -/
def shQ : DegreeShape (k + 7) := mk [3 + k, 3, 1] (sq k) (by simp; omega)

theorem shX_rows : (shX k).val.rowLens = [3 + k, 2, 1, 1] := mk_rowLens (by simp)
theorem shM_rows : (shM k).val.rowLens = [4 + k, 1, 1, 1] := mk_rowLens (by simp)
theorem shY_rows : (shY k).val.rowLens = [4 + k, 2, 1] := mk_rowLens (by simp)
theorem shP_rows : (shP k).val.rowLens = [3 + k, 2, 2] := mk_rowLens (by simp)
theorem shQ_rows : (shQ k).val.rowLens = [3 + k, 3, 1] := mk_rowLens (by simp)

theorem rowLen_getD_eq {n : ℕ} (a : DegreeShape n) {w : List ℕ} (h : a.val.rowLens = w) (i : ℕ) :
    a.val.rowLen i = w.getD i 0 := by rw [rowLen_eq_getD, h]

/-- Dominance between explicit shapes, checked on prefixes. -/
theorem dom_of_pre {n : ℕ} {a b : DegreeShape n} {v w : List ℕ} (ha : a.val.rowLens = v)
    (hb : b.val.rowLens = w) (h : ∀ j, pre v j ≤ pre w j) : Dom a.val b.val := by
  intro j; rw [shapePrefix_eq_pre, shapePrefix_eq_pre, ha, hb]; exact h j

theorem pre_explicit4 (a b c d j : ℕ) :
    pre [a, b, c, d] j = if j = 0 then 0 else if j = 1 then a else if j = 2 then a + b else
      if j = 3 then a + b + c else a + b + c + d := by
  rcases j with _ | _ | _ | _ | j <;> simp [pre] <;> omega

theorem pre_explicit3 (a b c j : ℕ) :
    pre [a, b, c] j = if j = 0 then 0 else if j = 1 then a else if j = 2 then a + b else
      a + b + c := by
  rcases j with _ | _ | _ | j <;> simp [pre]; omega

/-- The five covers. The proof pattern: pin the prefix sums of an intermediate shape `c`,
determine its first four row lengths, and the fifth vanishes. -/
theorem cov_XM : DomCovBy (shX k) (shM k) := by
  refine covBy_of (dom_of_pre (shX_rows k) (shM_rows k) (fun j => by
    rw [pre_explicit4, pre_explicit4]; split_ifs <;> omega))
    (by rw [shX_rows, shM_rows]; simp) (fun c h1 h2 => ?_)
  have p := pinned h1 h2
  rw [shX_rows, shM_rows] at p
  have p1 := p 1; have p2 := p 2; have p3 := p 3; have p4 := p 4; have p5 := p 5
  simp only [pre_explicit4] at p1 p2 p3 p4 p5
  norm_num at p1 p2 p3 p4 p5
  obtain ⟨s0, s1, s2, s3, s4, a0, a1, a2, a3⟩ := c_facts c.val
  have h4 : c.val.rowLen 4 = 0 := by omega
  rcases (by omega : c.val.rowLen 0 = 3 + k ∨ c.val.rowLen 0 = 4 + k) with e | e
  · left
    intro i; rw [rowLen_getD_eq _ (shX_rows k)]
    apply rowLen_tail _ (by simp) (fun i hi => by interval_cases i <;> simp <;> omega) h4
  · right
    intro i; rw [rowLen_getD_eq _ (shM_rows k)]
    apply rowLen_tail _ (by simp) (fun i hi => by interval_cases i <;> simp <;> omega) h4

theorem cov_MY : DomCovBy (shM k) (shY k) := by
  refine covBy_of (dom_of_pre (shM_rows k) (shY_rows k) (fun j => by
    rw [pre_explicit4, pre_explicit3]; split_ifs <;> omega))
    (by rw [shM_rows, shY_rows]; simp) (fun c h1 h2 => ?_)
  have p := pinned h1 h2
  rw [shM_rows, shY_rows] at p
  have p1 := p 1; have p2 := p 2; have p3 := p 3; have p4 := p 4; have p5 := p 5
  simp only [pre_explicit4, pre_explicit3] at p1 p2 p3 p4 p5
  norm_num at p1 p2 p3 p4 p5
  obtain ⟨s0, s1, s2, s3, s4, a0, a1, a2, a3⟩ := c_facts c.val
  have h4 : c.val.rowLen 4 = 0 := by omega
  rcases (by omega : c.val.rowLen 1 = 1 ∨ c.val.rowLen 1 = 2) with e | e
  · left
    intro i; rw [rowLen_getD_eq _ (shM_rows k)]
    apply rowLen_tail _ (by simp) (fun i hi => by interval_cases i <;> simp <;> omega) h4
  · right
    intro i; rw [rowLen_getD_eq _ (shY_rows k)]
    apply rowLen_tail _ (by simp) (fun i hi => by interval_cases i <;> simp <;> omega) h4

theorem cov_XP : DomCovBy (shX k) (shP k) := by
  refine covBy_of (dom_of_pre (shX_rows k) (shP_rows k) (fun j => by
    rw [pre_explicit4, pre_explicit3]; split_ifs <;> omega))
    (by rw [shX_rows, shP_rows]; simp) (fun c h1 h2 => ?_)
  have p := pinned h1 h2
  rw [shX_rows, shP_rows] at p
  have p1 := p 1; have p2 := p 2; have p3 := p 3; have p4 := p 4; have p5 := p 5
  simp only [pre_explicit4, pre_explicit3] at p1 p2 p3 p4 p5
  norm_num at p1 p2 p3 p4 p5
  obtain ⟨s0, s1, s2, s3, s4, a0, a1, a2, a3⟩ := c_facts c.val
  have h4 : c.val.rowLen 4 = 0 := by omega
  rcases (by omega : c.val.rowLen 2 = 1 ∨ c.val.rowLen 2 = 2) with e | e
  · left
    intro i; rw [rowLen_getD_eq _ (shX_rows k)]
    apply rowLen_tail _ (by simp) (fun i hi => by interval_cases i <;> simp <;> omega) h4
  · right
    intro i; rw [rowLen_getD_eq _ (shP_rows k)]
    apply rowLen_tail _ (by simp) (fun i hi => by interval_cases i <;> simp <;> omega) h4

theorem cov_PQ : DomCovBy (shP k) (shQ k) := by
  refine covBy_of (dom_of_pre (shP_rows k) (shQ_rows k) (fun j => by
    rw [pre_explicit3, pre_explicit3]; split_ifs <;> omega))
    (by rw [shP_rows, shQ_rows]; simp) (fun c h1 h2 => ?_)
  have p := pinned h1 h2
  rw [shP_rows, shQ_rows] at p
  have p1 := p 1; have p2 := p 2; have p3 := p 3; have p4 := p 4; have p5 := p 5
  simp only [pre_explicit3] at p1 p2 p3 p4 p5
  norm_num at p1 p2 p3 p4 p5
  obtain ⟨s0, s1, s2, s3, s4, a0, a1, a2, a3⟩ := c_facts c.val
  have h4 : c.val.rowLen 4 = 0 := by omega
  rcases (by omega : c.val.rowLen 1 = 2 ∨ c.val.rowLen 1 = 3) with e | e
  · left
    intro i; rw [rowLen_getD_eq _ (shP_rows k)]
    apply rowLen_tail _ (by simp) (fun i hi => by interval_cases i <;> simp <;> omega) h4
  · right
    intro i; rw [rowLen_getD_eq _ (shQ_rows k)]
    apply rowLen_tail _ (by simp) (fun i hi => by interval_cases i <;> simp <;> omega) h4

theorem cov_QY : DomCovBy (shQ k) (shY k) := by
  refine covBy_of (dom_of_pre (shQ_rows k) (shY_rows k) (fun j => by
    rw [pre_explicit3, pre_explicit3]; split_ifs <;> omega))
    (by rw [shQ_rows, shY_rows]; simp) (fun c h1 h2 => ?_)
  have p := pinned h1 h2
  rw [shQ_rows, shY_rows] at p
  have p1 := p 1; have p2 := p 2; have p3 := p 3; have p4 := p 4; have p5 := p 5
  simp only [pre_explicit3] at p1 p2 p3 p4 p5
  norm_num at p1 p2 p3 p4 p5
  obtain ⟨s0, s1, s2, s3, s4, a0, a1, a2, a3⟩ := c_facts c.val
  have h4 : c.val.rowLen 4 = 0 := by omega
  rcases (by omega : c.val.rowLen 0 = 3 + k ∨ c.val.rowLen 0 = 4 + k) with e | e
  · left
    intro i; rw [rowLen_getD_eq _ (shQ_rows k)]
    apply rowLen_tail _ (by simp) (fun i hi => by interval_cases i <;> simp <;> omega) h4
  · right
    intro i; rw [rowLen_getD_eq _ (shY_rows k)]
    apply rowLen_tail _ (by simp) (fun i hi => by interval_cases i <;> simp <;> omega) h4

/-- For `n = k + 7` the dominance order is not graded: the interval `[(3+k,2,1,1), (4+k,2,1)]`
has saturated chains `(3+k,2,1,1) ⋖ (4+k,1,1,1) ⋖ (4+k,2,1)` and
`(3+k,2,1,1) ⋖ (3+k,2,2) ⋖ (3+k,3,1) ⋖ (4+k,2,1)`. -/
theorem not_graded : ¬ DomGraded (k + 7) := by
  rintro ⟨ρ, hρ⟩
  have e1 := hρ _ _ (cov_XM k)
  have e2 := hρ _ _ (cov_MY k)
  have e3 := hρ _ _ (cov_XP k)
  have e4 := hρ _ _ (cov_PQ k)
  have e5 := hρ _ _ (cov_QY k)
  omega

end Chains

/-- [EK] p. 16: dominance on partitions of `n` is graded iff `n ≤ 6`. -/
theorem ek_p16_graded_iff (n : ℕ) : DomGraded n ↔ n ≤ 6 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    exact not_graded k h
  · intro hn
    apply graded_of_list (cert_le (by omega))
    interval_cases n <;> decide

/-! ## Listings and transposition -/

/-- A listing of all partitions of `n`, each exactly once. -/
def IsListing {n : ℕ} (L : List (DegreeShape n)) : Prop := L.Nodup ∧ ∀ a, a ∈ L

/-- Reversing the listing swaps each partition with its transpose. -/
def RevSwaps {n : ℕ} (L : List (DegreeShape n)) : Prop :=
  ∀ i (hi : i < L.length), (L[L.length - 1 - i]'(by omega)).val = (L[i]).val.transpose

/-- The listing refines the dominance order. -/
def RefinesDom {n : ℕ} (L : List (DegreeShape n)) : Prop :=
  ∀ i j (hi : i < L.length) (hj : j < L.length), Dom (L[i]).val (L[j]).val → i ≤ j

/-- The listing is in increasing lexicographic order. -/
def LexSorted {n : ℕ} (L : List (DegreeShape n)) : Prop := L.Sorted fun a b => LexLT a.val b.val

/-- No listing of partitions of `n` swaps transposes when there are two distinct self-transpose
partitions: both would occupy the middle position. -/
theorem no_listing_rev_swaps {n : ℕ} {a b : DegreeShape n} (hab : a ≠ b)
    (ha : a.val.transpose = a.val) (hb : b.val.transpose = b.val) {L : List (DegreeShape n)}
    (hL : IsListing L) : ¬ RevSwaps L := by
  intro hr
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem (hL.2 a)
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem (hL.2 b)
  have mid : ∀ t (ht : t < L.length), (L[t]).val.transpose = (L[t]).val → L.length - 1 - t = t := by
    intro t ht hself
    have h1 := hr t ht
    rw [hself] at h1
    have h2 : L[L.length - 1 - t]'(by omega) = L[t] := Subtype.ext h1
    exact (List.Nodup.getElem_inj_iff hL.1).mp h2
  have mi := mid i hi (by rw [hia]; exact ha)
  have mj := mid j hj (by rw [hjb]; exact hb)
  have hij : i = j := by omega
  subst hij
  exact hab (hia.symm.trans hjb)

theorem getD_rep (r i : ℕ) : (List.replicate r 1).getD i 0 = if i < r then 1 else 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> simp

theorem mem_ofRowLens_getD {w : List ℕ} {hw : w.Sorted (· ≥ ·)} {i j : ℕ} :
    (i, j) ∈ YoungDiagram.ofRowLens w hw ↔ j < w.getD i 0 := by
  rw [OddLRExamples.mem_ofRowLens_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hi
    rw [List.getD_eq_default _ _ (by simpa using hi)] at h
    omega

theorem transpose_self_of {w : List ℕ} (hw : w.Sorted (· ≥ ·))
    (h : ∀ i j, i < w.getD j 0 ↔ j < w.getD i 0) :
    (YoungDiagram.ofRowLens w hw).transpose = YoungDiagram.ofRowLens w hw := by
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
    mem_ofRowLens_getD, mem_ofRowLens_getD, h]

theorem sorted_append_rep (l : List ℕ) (hl : l.Sorted (· ≥ ·)) (h1 : ∀ x ∈ l, 1 ≤ x) (r : ℕ) :
    (l ++ List.replicate r 1).Sorted (· ≥ ·) := by
  rw [List.Sorted, List.pairwise_append]
  refine ⟨hl, by rw [List.pairwise_replicate]; simp, ?_⟩
  intro a ha b hb
  rw [List.eq_of_mem_replicate hb]
  exact h1 a ha

/-- For `n ≥ 8` there are two distinct self-transpose partitions of `n`. -/
theorem two_self_transpose {n : ℕ} (hn : 8 ≤ n) :
    ∃ a b : DegreeShape n, a ≠ b ∧ a.val.transpose = a.val ∧ b.val.transpose = b.val := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · -- `(m, 2, 1^{m-2})` and `(m-1, 3, 2, 1^{m-4})`
    have hsA : ([m, 2] ++ List.replicate (m - 2) 1).Sorted (· ≥ ·) :=
      sorted_append_rep _ (sorted_of_chain _ (by simp [List.chain'_cons]; omega))
        (by simp; omega) _
    have hsB : ([m - 1, 3, 2] ++ List.replicate (m - 4) 1).Sorted (· ≥ ·) :=
      sorted_append_rep _ (sorted_of_chain _ (by simp [List.chain'_cons]; omega))
        (by simp; omega) _
    have hpA : ∀ x ∈ [m, 2] ++ List.replicate (m - 2) 1, 0 < x := by
      simp [List.mem_replicate]; omega
    have hpB : ∀ x ∈ [m - 1, 3, 2] ++ List.replicate (m - 4) 1, 0 < x := by
      simp [List.mem_replicate]; omega
    refine ⟨mk _ hsA (by simp [List.sum_replicate]; omega),
      mk _ hsB (by simp [List.sum_replicate]; omega), ?_, ?_, ?_⟩
    · intro he
      have := congrArg (fun a : DegreeShape (2 * m) => a.val.rowLens.headD 0) he
      simp only [mk_rowLens hpA, mk_rowLens hpB] at this
      simp at this
      omega
    · refine transpose_self_of hsA (fun i j => ?_)
      rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
        simp only [List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
          getD_rep] <;> (try split_ifs) <;> omega
    · refine transpose_self_of hsB (fun i j => ?_)
      rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
        simp only [List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
          getD_rep] <;> (try split_ifs) <;> omega
  · -- `(m+1, 1^m)` and `(m-1, 3, 3, 1^{m-4})`
    have hsA : ([m + 1] ++ List.replicate m 1).Sorted (· ≥ ·) :=
      sorted_append_rep _ (by simp) (by simp) _
    have hsB : ([m - 1, 3, 3] ++ List.replicate (m - 4) 1).Sorted (· ≥ ·) :=
      sorted_append_rep _ (sorted_of_chain _ (by simp [List.chain'_cons]; omega))
        (by simp; omega) _
    have hpA : ∀ x ∈ [m + 1] ++ List.replicate m 1, 0 < x := by
      simp [List.mem_replicate]
    have hpB : ∀ x ∈ [m - 1, 3, 3] ++ List.replicate (m - 4) 1, 0 < x := by
      simp [List.mem_replicate]; omega
    refine ⟨mk _ hsA (by simp [List.sum_replicate]; omega),
      mk _ hsB (by simp [List.sum_replicate]; omega), ?_, ?_, ?_⟩
    · intro he
      have := congrArg (fun a : DegreeShape (2 * m + 1) => a.val.rowLens.headD 0) he
      simp only [mk_rowLens hpA, mk_rowLens hpB] at this
      simp at this
      omega
    · refine transpose_self_of hsA (fun i j => ?_)
      rcases i with _ | i <;> rcases j with _ | j <;>
        simp only [List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
          getD_rep] <;> (try split_ifs) <;> omega
    · refine transpose_self_of hsB (fun i j => ?_)
      rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
        simp only [List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
          getD_rep] <;> (try split_ifs) <;> omega

/-- For `n ≥ 8` no listing of the partitions of `n` (refining dominance or not) has reversal
swapping transposes. -/
theorem no_rev_swaps_ge_eight {n : ℕ} (hn : 8 ≤ n) {L : List (DegreeShape n)} (hL : IsListing L) :
    ¬ RevSwaps L := by
  obtain ⟨a, b, hab, ha, hb⟩ := two_self_transpose hn
  exact no_listing_rev_swaps hab ha hb hL

/-! ### Explicit listings in degrees `≤ 7` -/

/-- The listing of shapes with the row lengths in `Q`. -/
def listing {n : ℕ} (hc : Cert n) (Q : List (List ℕ)) (hQ : ∀ w ∈ Q, w ∈ P n) :
    List (DegreeShape n) :=
  Q.attach.map fun w => mkP hc w.1 (hQ w.1 w.2)

theorem listing_length {n : ℕ} (hc : Cert n) (Q : List (List ℕ)) (hQ : ∀ w ∈ Q, w ∈ P n) :
    (listing hc Q hQ).length = Q.length := by simp [listing]

theorem listing_get {n : ℕ} (hc : Cert n) (Q : List (List ℕ)) (hQ : ∀ w ∈ Q, w ∈ P n) (i : ℕ)
    (hi : i < (listing hc Q hQ).length) :
    ((listing hc Q hQ)[i]).val.rowLens = Q[i]'(by rw [listing_length] at hi; exact hi) := by
  simp only [listing, List.getElem_map, List.getElem_attach]
  exact mkP_rowLens hc _ _

theorem listing_isListing {n : ℕ} (hc : Cert n) (Q : List (List ℕ)) (hQ : ∀ w ∈ Q, w ∈ P n)
    (hnd : Q.Nodup) (hall : ∀ w ∈ P n, w ∈ Q) : IsListing (listing hc Q hQ) := by
  refine ⟨?_, fun a => ?_⟩
  · apply List.Nodup.map_on _ (List.nodup_attach.mpr hnd)
    intro x _ y _ hxy
    apply Subtype.ext
    have := congrArg (fun a : DegreeShape n => a.val.rowLens) hxy
    simpa only [mkP_rowLens] using this
  · rw [listing, List.mem_map]
    refine ⟨⟨a.val.rowLens, hall _ (rowLens_mem_P a)⟩, List.mem_attach _ _, ?_⟩
    apply shape_ext
    rw [mkP_rowLens]

theorem listing_revSwaps_iff {n : ℕ} (hc : Cert n) (Q : List (List ℕ)) (hQ : ∀ w ∈ Q, w ∈ P n) :
    RevSwaps (listing hc Q hQ) ↔
      ∀ i (hi : i < Q.length), Q[Q.length - 1 - i]'(by omega) = conjL (Q[i]) := by
  constructor
  · intro h i hi
    have hi' : i < (listing hc Q hQ).length := by rw [listing_length]; exact hi
    have e := congrArg YoungDiagram.rowLens (h i hi')
    rw [transpose_rowLens hc, listing_get, listing_get] at e
    simpa only [listing_length] using e
  · intro h i hi
    apply EKAppendixData.shape_eq_of_rowLens
    rw [transpose_rowLens hc, listing_get, listing_get]
    have hi' : i < Q.length := by rw [listing_length] at hi; exact hi
    simpa only [listing_length] using h i hi'

theorem listing_refines_of {n : ℕ} (hc : Cert n) (Q : List (List ℕ)) (hQ : ∀ w ∈ Q, w ∈ P n)
    (h : ∀ i (hi : i < Q.length) j (hj : j < Q.length), ldom n (Q[i]) (Q[j]) = true → i ≤ j) :
    RefinesDom (listing hc Q hQ) := by
  intro i j hi hj hd
  rw [dom_iff_ldom, listing_get, listing_get] at hd
  exact h i _ j _ hd

/-- The lexicographic listing is in increasing lexicographic order. -/
theorem listing_lexSorted {n : ℕ} (hc : Cert n) (hs : (P n).Sorted (· < ·)) :
    LexSorted (listing hc (P n) (fun _ h => h)) := by
  rw [LexSorted, List.Sorted, List.pairwise_iff_getElem]
  intro i j hi hj hij
  unfold LexLT
  rw [listing_get, listing_get]
  exact (List.pairwise_iff_getElem.mp hs) i j _ _ hij

instance lexAntisymm (n : ℕ) : IsAntisymm (DegreeShape n) (fun a b => LexLT a.val b.val) :=
  ⟨fun _ _ h1 h2 => absurd h2 (lt_asymm h1)⟩

/-- A lexicographically sorted listing is the lexicographic listing. -/
theorem lex_listing_unique {n : ℕ} (hc : Cert n) (hs : (P n).Sorted (· < ·))
    {L : List (DegreeShape n)} (hL : IsListing L) (hLs : LexSorted L) (hnd : (P n).Nodup) :
    L = listing hc (P n) (fun _ h => h) := by
  have hM := listing_isListing hc (P n) (fun _ h => h) hnd (fun _ h => h)
  apply List.eq_of_perm_of_sorted _ hLs (listing_lexSorted hc hs)
  rw [List.perm_ext_iff_of_nodup hL.1 hM.1]
  exact fun a => ⟨fun _ => hM.2 a, fun _ => hL.2 a⟩

abbrev LexCert (n : ℕ) : Prop := (P n).Sorted (· < ·) ∧ (P n).Nodup

theorem lexCert_le {n : ℕ} (hn : n ≤ 7) : LexCert n := by
  interval_cases n <;> decide

/-- [EK] p. 16: for a listing of the partitions of `n` in increasing lexicographic order,
reversing the order swaps transposes iff `n ≤ 5` (the first failure is at `n = 6`). -/
theorem ek_p16_lex_reversal_iff (n : ℕ) {L : List (DegreeShape n)} (hL : IsListing L)
    (hLs : LexSorted L) : RevSwaps L ↔ n ≤ 5 := by
  by_cases h8 : 8 ≤ n
  · exact ⟨fun h => absurd h (no_rev_swaps_ge_eight h8 hL), fun h => by omega⟩
  have hn : n ≤ 7 := by omega
  have hc := cert_le hn
  obtain ⟨hs, hnd⟩ := lexCert_le hn
  rw [lex_listing_unique hc hs hL hLs hnd, listing_revSwaps_iff]
  interval_cases n <;> decide

/-- Dominance-refining listings whose reversal swaps transposes, degrees `0, …, 7`. -/
def refineQ : ℕ → List (List ℕ)
  | 0 => [[]]
  | 1 => [[1]]
  | 2 => [[1, 1], [2]]
  | 3 => [[1, 1, 1], [2, 1], [3]]
  | 4 => [[1, 1, 1, 1], [2, 1, 1], [2, 2], [3, 1], [4]]
  | 5 => [[1, 1, 1, 1, 1], [2, 1, 1, 1], [2, 2, 1], [3, 1, 1], [3, 2], [4, 1], [5]]
  | 6 => [[1, 1, 1, 1, 1, 1], [2, 1, 1, 1, 1], [2, 2, 1, 1], [2, 2, 2], [3, 1, 1, 1], [3, 2, 1],
      [4, 1, 1], [3, 3], [4, 2], [5, 1], [6]]
  | 7 => [[1, 1, 1, 1, 1, 1, 1], [2, 1, 1, 1, 1, 1], [2, 2, 1, 1, 1], [2, 2, 2, 1],
      [3, 1, 1, 1, 1], [3, 2, 1, 1], [3, 2, 2], [4, 1, 1, 1], [3, 3, 1], [4, 2, 1], [5, 1, 1],
      [4, 3], [5, 2], [6, 1], [7]]
  | _ => []

abbrev RefineCert (n : ℕ) : Prop :=
  (∀ w ∈ refineQ n, w ∈ P n) ∧ (refineQ n).Nodup ∧ (∀ w ∈ P n, w ∈ refineQ n) ∧
    (∀ i (hi : i < (refineQ n).length) j (hj : j < (refineQ n).length),
      ldom n ((refineQ n)[i]) ((refineQ n)[j]) = true → i ≤ j) ∧
    ∀ i (hi : i < (refineQ n).length),
      (refineQ n)[(refineQ n).length - 1 - i]'(by omega) = conjL ((refineQ n)[i])

theorem refineCert_le {n : ℕ} (hn : n ≤ 7) : RefineCert n := by
  interval_cases n <;> decide

/-- [EK] p. 16: a listing of the partitions of `n` that refines dominance and whose reversal swaps
transposes exists iff `n ≤ 7`. The printed "one can refine the dominance partial order in such
a way that this property holds" is false for every `n ≥ 8`. -/
theorem ek_p16_refinement_iff (n : ℕ) :
    (∃ L : List (DegreeShape n), IsListing L ∧ RefinesDom L ∧ RevSwaps L) ↔ n ≤ 7 := by
  constructor
  · rintro ⟨L, hL, -, hr⟩
    by_contra h8
    exact no_rev_swaps_ge_eight (by omega) hL hr
  · intro hn
    have hc := cert_le hn
    obtain ⟨hQ, hnd, hall, href, hrev⟩ := refineCert_le hn
    exact ⟨listing hc _ hQ, listing_isListing hc _ hQ hnd hall, listing_refines_of hc _ hQ href,
      (listing_revSwaps_iff hc _ hQ).mpr hrev⟩

end OddMath.Frontier.EKMore
