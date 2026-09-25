import OddMath.Frontier.OddSchurPieri
import OddMath.Frontier.CompleteTableauExpansion
import OddMath.Frontier.TableauExtremal

/-! Ellis 1111.3932v1, Theorem 3.8 (s^p = s^s): Lemma 3.5 base case and the column-product
triangular elimination (last paragraph of the proof of Theorem 3.8).

Carriers (frozen by the fixed specification): s^p = `CompleteTableauExpansion.sp`,
s^s = `OddSymmetrizer.schur`, both in `SkewPolynomial (n+2)`.  The Young-diagram bridge is the
row-length correspondence `toYoung` below.  The e-right Pieri rule is indexed exactly as the
existing `OddSchurPieri.right_pieri` ((3.7)): sets `I` of `k` rows whose one-box increment is
a partition, sign `(-1)^{Σ_{i∈I} |i/λ|}` with `|i/λ| = lowerRows` (boxes strictly below row i).

* (a) `lemma_3_5`: sp (1^k) = schur (1^k) = (-1)^{k(k-1)/2} e_k.
* (b) `eliminate`: two families on `PartitionExponent n` (at most n+2 rows) that agree on the
  columns (1^k) and satisfy the SAME e-right Pieri rule agree everywhere; outer strong induction
  on the width λ_1, inner well-founded induction on the lexicographic order of λ^T (printed
  argument).  Triangularity: `strip_lex`.
* (c) `sp_eq_schur_of_pieri310` (CONDITIONAL): sp = schur for every partition with at most n+2
  rows, assuming the named hypothesis `Pieri310` (Ellis (3.10) for sp,
  not proved here; discharged in `OddLRThm38`).  (3.7) is the existing `right_pieri`.
No Lemma 2.15, no EK quotient identification, no hives. -/
namespace OddMath.Frontier.OddLRElimination
open OddSymmetrizer OddSchurPieri TableauStripSigns
open OddMath.SkewPolynomial (SkewPolynomial)
open scoped BigOperators
noncomputable section

/-! ## 0. Row-length bridge `PartitionExponent n → YoungDiagram` -/

/-- Row lengths on all of ℕ, zero past the padded alphabet. -/
def rowFun {n : ℕ} (α : PartitionExponent n) (a : ℕ) : ℕ :=
  if h : a < n+2 then α.val ⟨a, h⟩ else 0

theorem rowFun_antitone {n : ℕ} (α : PartitionExponent n) : Antitone (rowFun α) := by
  intro a b hab
  unfold rowFun
  by_cases hb : b < n+2
  · have ha : a < n+2 := lt_of_le_of_lt hab hb
    rw [dif_pos hb, dif_pos ha]
    exact α.property (show (⟨a, ha⟩ : Fin (n+2)) ≤ ⟨b, hb⟩ from hab)
  · rw [dif_neg hb]; exact Nat.zero_le _

theorem rowFun_pos {n : ℕ} (α : PartitionExponent n) {a : ℕ} (h : 0 < rowFun α a) : a < n+2 := by
  unfold rowFun at h
  by_contra hn
  rw [dif_neg hn] at h
  exact lt_irrefl 0 h

/-- The cells of the row-length diagram. -/
def cellsOf {n : ℕ} (α : PartitionExponent n) : Finset (ℕ × ℕ) :=
  ((Finset.range (n+2)) ×ˢ (Finset.range (rowFun α 0))).filter (fun p => p.2 < rowFun α p.1)

theorem mem_cellsOf {n : ℕ} (α : PartitionExponent n) (p : ℕ × ℕ) :
    p ∈ cellsOf α ↔ p.2 < rowFun α p.1 := by
  simp only [cellsOf, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨rowFun_pos α (lt_of_le_of_lt (Nat.zero_le _) h),
      lt_of_lt_of_le h (rowFun_antitone α (Nat.zero_le _))⟩, h⟩

/-- The row-length Young diagram of a padded partition. -/
def toYoung {n : ℕ} (α : PartitionExponent n) : YoungDiagram where
  cells := cellsOf α
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.mem_coe, mem_cellsOf] at hb ⊢
    exact lt_of_le_of_lt hab.2 (lt_of_lt_of_le hb (rowFun_antitone α hab.1))

@[simp] theorem mem_toYoung {n : ℕ} (α : PartitionExponent n) (p : ℕ × ℕ) :
    p ∈ toYoung α ↔ p.2 < rowFun α p.1 := mem_cellsOf α p

/-- The bridge sends the padded column to the literal one-column diagram (1^k). -/
theorem toYoung_column (n k : ℕ) (hk : k ≤ n+2) :
    toYoung (column n k) = TableauExtremal.columnShape k := by
  apply YoungDiagram.ext
  ext ⟨a, b⟩
  change (a, b) ∈ toYoung (column n k) ↔ (a, b) ∈ TableauExtremal.columnShape k
  rw [mem_toYoung, TableauExtremal.mem_columnShape]
  simp only [rowFun, column]
  by_cases ha : a < n+2
  · rw [dif_pos ha]
    split_ifs <;> omega
  · rw [dif_neg ha]
    omega

/-- Diagrams with at most n+2 rows, read back as padded row lengths. -/
def ofYoung {n : ℕ} (μ : YoungDiagram) : PartitionExponent n :=
  ⟨fun i => μ.rowLen i.val, fun _ _ h => μ.rowLen_anti _ _ h⟩

theorem toYoung_ofYoung {n : ℕ} (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n+2) :
    toYoung (ofYoung (n := n) μ) = μ := by
  apply YoungDiagram.ext
  ext ⟨a, b⟩
  change (a, b) ∈ toYoung (ofYoung (n := n) μ) ↔ (a, b) ∈ μ
  rw [mem_toYoung, YoungDiagram.mem_iff_lt_rowLen]
  simp only [rowFun, ofYoung]
  by_cases ha : a < n+2
  · rw [dif_pos ha]
  · rw [dif_neg ha]
    have h0 : ¬ (a, 0) ∈ μ := by
      rw [YoungDiagram.mem_iff_lt_colLen]; omega
    rw [YoungDiagram.mem_iff_lt_rowLen] at h0
    omega

/-! ## (a) Lemma 3.5 (3.5), columns -/

theorem directNorth_column (k : ℕ) :
    directNorth (TableauExtremal.columnShape k) = north (TableauExtremal.columnShape k) := by
  unfold directNorth north
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := ((TableauExtremal.mem_columnShape k p.1 p.2).mp hp).1
  congr 1
  apply Finset.filter_congr
  intro q hq
  have hq' := ((TableauExtremal.mem_columnShape k q.1 q.2).mp hq).1
  simp [hp', hq']

/-- s^p_{(1^k)} = (-1)^{C(k,2)} e_k in every rank N (including k > N, where both vanish). -/
theorem sp_column (N k : ℕ) :
    CompleteTableauExpansion.sp N (TableauExtremal.columnShape k) =
      (-1 : ℤ) ^ k.choose 2 • FiniteCompleteElementary.elementaryPoly N k := by
  rw [CompleteTableauExpansion.sp, TableauExtremal.tableauPolynomial_column, directNorth_column,
    smul_smul, ← pow_add, ← two_mul, pow_add, pow_mul]
  norm_num

/-- Ellis Lemma 3.5 (3.5), the s^p and s^s parts, exactly as printed
(`k.choose 2 = k(k-1)/2`), with the row-length bridge. -/
theorem lemma_3_5 (n k : ℕ) (hk : k ≤ n+2) :
    CompleteTableauExpansion.sp (n+2) (toYoung (column n k)) = schur n (column n k) ∧
    schur n (column n k) =
      (-1 : ℤ) ^ (k * (k-1) / 2) • FiniteCompleteElementary.elementaryPoly (n+2) k := by
  rw [toYoung_column n k hk, sp_column, schur_column n k hk, Nat.choose_two_right]
  exact ⟨rfl, rfl⟩

/-! ## (b) Triangularity of the last-column Pieri step -/

/-- Column lengths of a row-length vector: `colLen a j = (λ^T)_{j+1}`. -/
def colLen {N : ℕ} (a : Fin N → ℕ) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => j < a i)).card

theorem colLen_le {N : ℕ} (a : Fin N → ℕ) (j : ℕ) : colLen a j ≤ N := by
  unfold colLen
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The first `r` column lengths, as an element of a finite lexicographic order. -/
def colVec {n : ℕ} (r : ℕ) (α : PartitionExponent n) : Lex (Fin r → Fin (n+3)) :=
  toLex (fun j => ⟨colLen α.val j.val, Nat.lt_succ_of_le (colLen_le α.val j.val)⟩)

instance (r m : ℕ) : Finite (Lex (Fin r → Fin m)) := inferInstanceAs (Finite (Fin r → Fin m))

theorem le_width {n : ℕ} (α : PartitionExponent n) (i : Fin (n+2)) : α.val i ≤ α.val 0 :=
  α.property (Fin.zero_le i)

/-- Remove the last column: λ ↦ λ with its r-th column deleted, r = λ_1. -/
def trunc {n : ℕ} (α : PartitionExponent n) : PartitionExponent n :=
  ⟨fun i => min (α.val i) (α.val 0 - 1), fun _ _ h => min_le_min (α.property h) le_rfl⟩

/-- The rows touching the last column (the top `c = (λ^T)_r` rows). -/
def topSet {n : ℕ} (α : PartitionExponent n) : Finset (Fin (n+2)) :=
  Finset.univ.filter (fun i => α.val 0 - 1 < α.val i)

theorem increment_trunc_top {n : ℕ} (α : PartitionExponent n) (hr : 1 ≤ α.val 0) :
    increment (trunc α).val (topSet α) = α.val := by
  funext i
  have := le_width α i
  simp only [increment, trunc, topSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.min_def]
  split_ifs <;> omega

/-- The vertical strip that rebuilds λ from `trunc λ`. -/
def topStrip {n : ℕ} (α : PartitionExponent n) (hr : 1 ≤ α.val 0) :
    VerticalStrip n (colLen α.val (α.val 0 - 1)) (trunc α) :=
  ⟨topSet α, rfl, by rw [increment_trunc_top α hr]; exact α.property⟩

theorem strip_top_eq {n : ℕ} (α : PartitionExponent n) (hr : 1 ≤ α.val 0) :
    stripPartition (topStrip α hr) = α :=
  Subtype.ext (increment_trunc_top α hr)

theorem increment_inj {N : ℕ} (a : Fin N → ℕ) {I J : Finset (Fin N)}
    (h : increment a I = increment a J) : I = J := by
  ext i
  have := congrFun h i
  simp only [increment] at this
  by_cases hI : i ∈ I <;> by_cases hJ : i ∈ J <;> simp_all

theorem strip_le {n c : ℕ} (α : PartitionExponent n) (hr : 1 ≤ α.val 0)
    (I : VerticalStrip n c (trunc α)) (i : Fin (n+2)) :
    (stripPartition I).val i ≤ α.val 0 := by
  change min (α.val i) (α.val 0 - 1) + (if i ∈ I.val then 1 else 0) ≤ α.val 0
  rw [Nat.min_def]
  split_ifs <;> omega

theorem subsetExp_iff {N : ℕ} (I : Finset (Fin N)) (i : Fin N) :
    subsetExp I i = 1 ↔ i ∈ I := by
  unfold subsetExp; split_ifs with h <;> simp [h]

/-- A down-closed set of rows is determined by its cardinality. -/
theorem downset_eq {N : ℕ} (I J : Finset (Fin N)) (hI : Antitone (subsetExp I))
    (hJ : Antitone (subsetExp J)) (hc : I.card = J.card) : I = J := by
  have h := antitone_subset I hI
  have h' := antitone_subset J hJ
  rw [hc, ← h'] at h
  ext i
  rw [← subsetExp_iff, ← subsetExp_iff, h]

/-- Triangularity (last paragraph of the proof of Thm 3.8): every OTHER term of the Pieri
step `s_{trunc λ} · s_{(1^c)}` is strictly lex-greater than λ in the order of λ^T. -/
theorem strip_lex {n r : ℕ} (α : PartitionExponent n) (hα : α.val 0 = r) (hr : 1 ≤ r)
    (I : VerticalStrip n (colLen α.val (α.val 0 - 1)) (trunc α))
    (hne : stripPartition I ≠ α) :
    colVec r α < colVec r (stripPartition I) := by
  classical
  have hν : ∀ i, (stripPartition I).val i =
      min (α.val i) (r - 1) + (if i ∈ I.val then 1 else 0) := by
    intro i
    change min (α.val i) (α.val 0 - 1) + _ = _
    have h1 : α.val 0 - 1 = r - 1 := by omega
    exact congrArg (fun z => min (α.val i) z + (if i ∈ I.val then 1 else 0)) h1
  by_cases hA : ∃ i ∈ I.val, min (α.val i) (r - 1) < r - 1
  · let P : ℕ → Prop := fun j => ∃ i ∈ I.val, min (α.val i) (r - 1) = j ∧ j < r - 1
    have hP : ∃ j, P j := by
      obtain ⟨i, hi, hlt⟩ := hA
      exact ⟨_, i, hi, rfl, hlt⟩
    obtain ⟨i0, hi0, hbi0, hj0⟩ := Nat.find_spec hP
    have hmin : ∀ j < Nat.find hP, ¬ P j := fun j hj => Nat.find_min hP hj
    have heq : ∀ j, j < r - 1 → ¬ P j →
        colLen α.val j = colLen (stripPartition I).val j := by
      intro j hj hnP
      unfold colLen
      congr 1
      apply Finset.filter_congr
      intro i _
      rw [hν i]
      by_cases hi : i ∈ I.val
      · have hne' : min (α.val i) (r - 1) ≠ j := fun h => hnP ⟨i, hi, h, hj⟩
        rw [if_pos hi]
        rw [Nat.min_def] at hne' ⊢
        split_ifs at hne' ⊢ <;> omega
      · rw [if_neg hi, Nat.min_def]
        split_ifs <;> omega
    refine ⟨⟨Nat.find hP, by omega⟩, ?_, ?_⟩
    · intro j hj
      apply Fin.ext
      exact heq j.val (by have : j.val < Nat.find hP := hj; omega) (hmin j.val hj)
    · show colLen α.val (Nat.find hP) < colLen (stripPartition I).val (Nat.find hP)
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨i0, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hν i0, if_pos hi0, hbi0]; omega
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
          rw [Nat.min_def] at hbi0
          split_ifs at hbi0 <;> omega
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        rw [hν i, Nat.min_def]
        split_ifs <;> omega
  · push_neg at hA
    exfalso
    apply hne
    have hIν : ∀ i, (stripPartition I).val i = r ↔ i ∈ I.val := by
      intro i
      rw [hν i]
      by_cases hi : i ∈ I.val
      · have := hA i hi
        rw [if_pos hi]
        simp only [hi, iff_true]
        rw [Nat.min_def] at this ⊢
        split_ifs at this ⊢ <;> omega
      · rw [if_neg hi, Nat.min_def]
        simp only [hi, iff_false]
        split_ifs <;> omega
    have hItop : ∀ i, α.val i = r ↔ i ∈ topSet α := by
      intro i
      have := le_width α i
      simp only [topSet, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hI : I.val = topSet α := by
      apply downset_eq
      · intro a b hab
        unfold subsetExp
        by_cases hb : b ∈ I.val
        · have h1 := (hIν b).mpr hb
          have h2 := (stripPartition I).property hab
          have h3 := strip_le α (by omega) I a
          have ha : a ∈ I.val := (hIν a).mp (by omega)
          simp [ha, hb]
        · simp [hb]
      · intro a b hab
        unfold subsetExp
        by_cases hb : b ∈ topSet α
        · have h1 := (hItop b).mpr hb
          have h2 := α.property hab
          have h3 := le_width α a
          have ha : a ∈ topSet α := (hItop a).mp (by omega)
          simp [ha, hb]
        · simp [hb]
      · rw [I.property.1]; rfl
    apply Subtype.ext
    change increment (trunc α).val I.val = α.val
    rw [hI, increment_trunc_top α (by omega)]

/-! ## (b) Abstract elimination -/

instance {n k : ℕ} {α : PartitionExponent n} : DecidableEq (VerticalStrip n k α) := by
  unfold VerticalStrip; infer_instance

/-- The e-right Pieri rule in the exact form (and signs) of `right_pieri`, (3.7)/(3.10). -/
def RightPieri {n : ℕ} {R : Type*} [Ring R] (F : PartitionExponent n → R) : Prop :=
  ∀ k, k ≤ n+2 → ∀ α : PartitionExponent n,
    F α * F (column n k) =
      ∑ I : VerticalStrip n k α, (-1 : ℤ) ^ lowerRows α.val I.val • F (stripPartition I)

theorem column_zero_eq {n : ℕ} (α : PartitionExponent n) (h : α.val 0 = 0) :
    α = column n 0 := by
  apply Subtype.ext
  funext i
  have := le_width α i
  simp only [column, Nat.not_lt_zero, if_false]
  omega

/-- Isolate the λ-term of the Pieri step `s_{trunc λ} · s_{(1^c)}`. -/
theorem isolate {n : ℕ} {R : Type*} [Ring R] (F : PartitionExponent n → R) (hF : RightPieri F)
    (α : PartitionExponent n) (hr : 1 ≤ α.val 0) :
    (-1 : ℤ) ^ lowerRows (trunc α).val (topSet α) • F α =
      F (trunc α) * F (column n (colLen α.val (α.val 0 - 1))) -
        ∑ I ∈ Finset.univ.erase (topStrip α hr),
          (-1 : ℤ) ^ lowerRows (trunc α).val I.val • F (stripPartition I) := by
  rw [hF _ (colLen_le _ _) (trunc α), ← Finset.add_sum_erase _ _ (Finset.mem_univ (topStrip α hr)),
    add_sub_cancel_right, strip_top_eq α hr]
  rfl

/-- Ellis Thm 3.8, last paragraph, abstractly: two families indexed by partitions with at
most n+2 rows that agree on all columns (1^k) and satisfy the same e-right Pieri rule agree. -/
theorem eliminate {n : ℕ} {R : Type*} [Ring R] (F G : PartitionExponent n → R)
    (hcol : ∀ k, k ≤ n+2 → F (column n k) = G (column n k))
    (hF : RightPieri F) (hG : RightPieri G) : ∀ α, F α = G α := by
  suffices H : ∀ r, ∀ α : PartitionExponent n, α.val 0 = r → F α = G α from
    fun α => H _ α rfl
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ihr =>
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · intro α hα
    rw [column_zero_eq α (hα.trans h0)]
    exact hcol 0 (Nat.zero_le _)
  suffices H : ∀ v : Lex (Fin r → Fin (n+3)), ∀ α : PartitionExponent n, α.val 0 = r →
      colVec r α = v → F α = G α from fun α hα => H _ α hα rfl
  intro v
  induction v using (wellFounded_gt (α := Lex (Fin r → Fin (n+3)))).induction with
  | _ v ihv =>
  intro α hα hv
  have hr : 1 ≤ α.val 0 := by omega
  have hβ : F (trunc α) = G (trunc α) :=
    ihr (r - 1) (by omega) (trunc α) (by
      change min (α.val 0) (α.val 0 - 1) = r - 1
      rw [hα]; omega)
  have hterm : ∀ I ∈ Finset.univ.erase (topStrip α hr),
      F (stripPartition I) = G (stripPartition I) := by
    intro I hI
    have hI' := Finset.ne_of_mem_erase hI
    have hne : stripPartition I ≠ α := by
      intro h
      apply hI'
      apply Subtype.ext
      apply increment_inj (trunc α).val
      change increment (trunc α).val I.val = increment (trunc α).val (topSet α)
      rw [increment_trunc_top α hr]
      exact congrArg Subtype.val h
    have hle : (stripPartition I).val 0 ≤ r := hα ▸ strip_le α hr I 0
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact ihr _ hlt _ rfl
    · exact ihv (colVec r (stripPartition I)) (hv ▸ strip_lex α hα hpos I hne) _ heq rfl
  have hs : ((-1 : ℤ) ^ lowerRows (trunc α).val (topSet α)) *
      ((-1 : ℤ) ^ lowerRows (trunc α).val (topSet α)) = 1 := by
    rw [← mul_pow]; norm_num
  have h2 : (-1 : ℤ) ^ lowerRows (trunc α).val (topSet α) • F α =
      (-1 : ℤ) ^ lowerRows (trunc α).val (topSet α) • G α := by
    rw [isolate F hF α hr, isolate G hG α hr, hβ, hcol _ (colLen_le _ _)]
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    rw [hterm I hI]
  calc F α = (((-1 : ℤ) ^ lowerRows (trunc α).val (topSet α)) *
        ((-1 : ℤ) ^ lowerRows (trunc α).val (topSet α))) • F α := by rw [hs, one_smul]
    _ = _ := by rw [mul_smul, h2, ← mul_smul, hs, one_smul]

/-! ## (c) Conditional: s^p = s^s -/

/-- The existing EKL Proposition 2.26 = Ellis (3.7) is exactly `RightPieri (schur n)`. -/
theorem schur_rightPieri (n : ℕ) : RightPieri (schur n) :=
  fun k hk α => right_pieri n k hk α

/-- NAMED HYPOTHESIS (Ellis (3.10), NOT proved here; discharged in `OddLRThm38`), in the
bounded row-set form: for every partition λ with at most n+2 rows and k ≤ n+2,
s^p_λ s^p_{(1^k)} = Σ_μ (-1)^{|i_1/λ|+…+|i_k/λ|} s^p_μ, μ over λ plus a vertical strip of
size k with at most n+2 rows (taller μ are omitted; s^p of them vanishes in n+2 variables). -/
def Pieri310Bounded (n : ℕ) : Prop :=
  RightPieri (fun α : PartitionExponent n => CompleteTableauExpansion.sp (n+2) (toYoung α))

/-- CONDITIONAL Theorem 3.8 (s^p = s^s), hypothesis `Pieri310Bounded n` exactly. -/
theorem sp_eq_schur_of_pieri310Bounded (n : ℕ) (h310 : Pieri310Bounded n)
    (α : PartitionExponent n) :
    CompleteTableauExpansion.sp (n+2) (toYoung α) = schur n α :=
  eliminate _ (schur n) (fun k hk => (lemma_3_5 n k hk).1) h310 (schur_rightPieri n) α

/-- The same, for every Young diagram with at most n+2 rows. -/
theorem sp_eq_schur_diagram_of_pieri310Bounded (n : ℕ) (h310 : Pieri310Bounded n)
    (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n+2) :
    CompleteTableauExpansion.sp (n+2) μ = schur n (ofYoung μ) := by
  rw [← sp_eq_schur_of_pieri310Bounded n h310, toYoung_ofYoung μ hμ]


/-! ## (c) The named hypothesis in all-shapes Young-diagram form, and the bridge

`Pieri310 N` transcribes printed (3.10) in N variables for EVERY Young diagram λ and every k,
including the μ with more than N rows.  The printed sum over μ ⊇ λ with μ/λ a vertical strip of
size k is indexed by the set I = {i_1,…,i_k} of rows receiving a box (0-indexed); μ has row
lengths `rowInc λ I`.  `stripRows_complete` proves that the index set contains EVERY such I
(the range bound is automatic), so no strip is omitted.  `|i/λ|` (paper row i = a+1, remove
rows 1..i) is `belowRows λ a` = Σ_{b > a} λ_b. -/

/-- |i/λ| for the 0-indexed row a (paper row i = a+1): boxes strictly below row a. -/
def belowRows (lam : YoungDiagram) (a : ℕ) : ℕ :=
  ∑ b ∈ Finset.range (lam.colLen 0), if a < b then lam.rowLen b else 0

/-- Row lengths after adding one box in each row of I. -/
def rowInc (lam : YoungDiagram) (I : Finset ℕ) (a : ℕ) : ℕ :=
  lam.rowLen a + if a ∈ I then 1 else 0

/-- Young diagram with antitone row-length function f, supported below row B. -/
def diagramOf (f : ℕ → ℕ) (hf : Antitone f) (B : ℕ) : YoungDiagram where
  cells := ((Finset.range B) ×ˢ (Finset.range (f 0))).filter (fun p => p.2 < f p.1)
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_setOf_eq] at hb ⊢
    refine ⟨⟨lt_of_le_of_lt hab.1 hb.1.1, lt_of_le_of_lt hab.2 hb.1.2⟩, ?_⟩
    exact lt_of_le_of_lt hab.2 (lt_of_lt_of_le hb.2 (hf hab.1))

theorem mem_diagramOf (f : ℕ → ℕ) (hf : Antitone f) (B : ℕ) (hB : ∀ a, 0 < f a → a < B)
    (p : ℕ × ℕ) : p ∈ diagramOf f hf B ↔ p.2 < f p.1 := by
  change p ∈ (((Finset.range B) ×ˢ (Finset.range (f 0))).filter (fun p => p.2 < f p.1)) ↔ _
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨hB _ (lt_of_le_of_lt (Nat.zero_le _) h),
      lt_of_lt_of_le h (hf (Nat.zero_le _))⟩, h⟩

open Classical in
/-- The candidate strip rows: k rows below the bound whose increment is a partition. -/
def stripRows (lam : YoungDiagram) (k : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (lam.colLen 0 + k)).powerset.filter
    (fun I => I.card = k ∧ Antitone (rowInc lam I))

open Classical in
/-- μ = λ + (one box in each row of I); ⊥ off the index set (never summed). -/
def addStrip (lam : YoungDiagram) (k : ℕ) (I : Finset ℕ) : YoungDiagram :=
  if h : Antitone (rowInc lam I) then diagramOf (rowInc lam I) h (lam.colLen 0 + k) else ⊥

theorem rowLen_pos {lam : YoungDiagram} {a : ℕ} (h : 0 < lam.rowLen a) : a < lam.colLen 0 := by
  rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]; exact h

theorem rowLen_beyond {lam : YoungDiagram} {a : ℕ} (h : lam.colLen 0 ≤ a) : lam.rowLen a = 0 := by
  by_contra hn
  have := rowLen_pos (lam := lam) (Nat.pos_of_ne_zero hn)
  omega

/-- Completeness of the index set: every vertical strip of size k lies below row
`colLen 0 + k`, so `stripRows` omits no μ. -/
theorem stripRows_bound {k : ℕ} (lam : YoungDiagram) (I : Finset ℕ) (hc : I.card = k)
    (hI : Antitone (rowInc lam I)) : ∀ a ∈ I, a < lam.colLen 0 + k := by
  intro a ha
  by_contra hn
  push_neg at hn
  have hsub : Finset.Icc (lam.colLen 0) a ⊆ I := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    have h1 := hI hb.2
    simp only [rowInc, if_pos ha] at h1
    rw [rowLen_beyond hb.1] at h1
    by_contra hbI
    rw [if_neg hbI] at h1
    omega
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  omega

theorem stripRows_complete {k : ℕ} (lam : YoungDiagram) (I : Finset ℕ) (hc : I.card = k)
    (hI : Antitone (rowInc lam I)) : I ∈ stripRows lam k := by
  simp only [stripRows, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun a ha => Finset.mem_range.mpr (stripRows_bound lam I hc hI a ha), hc, hI⟩

theorem mem_addStrip (lam : YoungDiagram) (k : ℕ) {I : Finset ℕ} (hI : I ∈ stripRows lam k)
    (p : ℕ × ℕ) : p ∈ addStrip lam k I ↔ p.2 < rowInc lam I p.1 := by
  simp only [stripRows, Finset.mem_filter, Finset.mem_powerset] at hI
  unfold addStrip
  rw [dif_pos hI.2.2, mem_diagramOf]
  intro a ha
  unfold rowInc at ha
  by_cases hr : 0 < lam.rowLen a
  · have := rowLen_pos hr; omega
  · have hin : a ∈ I := by by_contra hn; simp [hn] at ha; omega
    exact Finset.mem_range.mp (hI.1 hin)

/-- NAMED HYPOTHESIS: Ellis (3.10) for s^p = `sp N`, all Young diagrams λ, all k, as printed
(NOT proved here; discharged in `OddLRThm38.pieri310`). -/
def Pieri310 (N : ℕ) : Prop :=
  ∀ (lam : YoungDiagram) (k : ℕ),
    CompleteTableauExpansion.sp N lam * CompleteTableauExpansion.sp N (TableauExtremal.columnShape k) =
      ∑ I ∈ stripRows lam k,
        (-1 : ℤ) ^ (∑ a ∈ I, belowRows lam a) • CompleteTableauExpansion.sp N (addStrip lam k I)

/-- s^p vanishes on shapes with more than N rows (no SSYT with entries ≤ N). -/
theorem sp_tall (N : ℕ) (μ : YoungDiagram) (h : (N, 0) ∈ μ) :
    CompleteTableauExpansion.sp N μ = 0 := by
  rw [CompleteTableauExpansion.sp]
  convert smul_zero _
  unfold TableauPolynomial.tableauPolynomial
  apply Finset.sum_eq_zero
  intro T _
  exfalso
  have hb := (TableauPolynomial.mem_tableauxInAlphabet N T.val).mp T.property
  have h1 : T.val.entry N 0 ≤ N := hb (N, 0) h
  have h2 := TableauDominance.entry_ge_row T.val h
  omega

theorem rowLen_toYoung {n : ℕ} (α : PartitionExponent n) (a : ℕ) :
    (toYoung α).rowLen a = rowFun α a := by
  apply eq_of_forall_lt_iff
  intro b
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_toYoung]

theorem colLen_toYoung {n : ℕ} (α : PartitionExponent n) : (toYoung α).colLen 0 ≤ n+2 := by
  by_contra hn
  push_neg at hn
  have := (YoungDiagram.mem_iff_lt_colLen (μ := toYoung α) (i := n+2) (j := 0)).mpr hn
  rw [mem_toYoung] at this
  simp [rowFun] at this

theorem belowRows_toYoung {n : ℕ} (α : PartitionExponent n) (i : Fin (n+2)) :
    belowRows (toYoung α) i.val = ∑ j ∈ Finset.univ.filter (i < ·), α.val j := by
  unfold belowRows
  have hsub : Finset.range ((toYoung α).colLen 0) ⊆ Finset.range (n+2) :=
    Finset.range_subset.mpr (colLen_toYoung α)
  rw [Finset.sum_subset hsub (by
    intro b _ hb
    rw [Finset.mem_range, not_lt] at hb
    rw [rowLen_beyond hb]; simp)]
  simp only [rowLen_toYoung]
  rw [← Fin.sum_univ_eq_sum_range (fun b => if i.val < b then rowFun α b else 0), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  simp only [rowFun, dif_pos j.isLt, Fin.lt_def]

/-- The strip rows of a bounded strip, on ℕ. -/
def strRows {n k : ℕ} {α : PartitionExponent n} (J : VerticalStrip n k α) : Finset ℕ :=
  J.val.map Fin.valEmbedding

theorem rowInc_strRows {n k : ℕ} {α : PartitionExponent n} (J : VerticalStrip n k α) (a : ℕ) :
    rowInc (toYoung α) (strRows J) a = rowFun (stripPartition J) a := by
  unfold rowInc strRows
  rw [rowLen_toYoung]
  unfold rowFun
  by_cases ha : a < n+2
  · rw [dif_pos ha, dif_pos ha]
    change _ = α.val ⟨a, ha⟩ + (if (⟨a, ha⟩ : Fin (n+2)) ∈ J.val then 1 else 0)
    congr 1
    simp only [Finset.mem_map, Fin.valEmbedding_apply]
    by_cases hj : (⟨a, ha⟩ : Fin (n+2)) ∈ J.val
    · rw [if_pos hj, if_pos ⟨_, hj, rfl⟩]
    · rw [if_neg hj, if_neg]
      rintro ⟨j, hj', rfl⟩
      exact hj hj'
  · rw [dif_neg ha, dif_neg ha]
    simp only [Finset.mem_map, Fin.valEmbedding_apply, zero_add]
    rw [if_neg]
    rintro ⟨j, _, rfl⟩
    exact ha j.isLt

theorem strRows_mem {n k : ℕ} {α : PartitionExponent n} (J : VerticalStrip n k α) :
    strRows J ∈ (stripRows (toYoung α) k).filter (· ⊆ Finset.range (n+2)) := by
  have hA : Antitone (rowInc (toYoung α) (strRows J)) := by
    have : rowInc (toYoung α) (strRows J) = rowFun (stripPartition J) :=
      funext (rowInc_strRows J)
    rw [this]; exact rowFun_antitone _
  have hc : (strRows J).card = k := by rw [strRows, Finset.card_map, J.property.1]
  rw [Finset.mem_filter]
  refine ⟨stripRows_complete _ _ hc hA, ?_⟩
  intro a ha
  simp only [strRows, Finset.mem_map, Fin.valEmbedding_apply] at ha
  obtain ⟨j, _, rfl⟩ := ha
  exact Finset.mem_range.mpr j.isLt

/-- The finite set of rows, read back in the padded alphabet. -/
def finRows (n : ℕ) (I : Finset ℕ) : Finset (Fin (n+2)) := Finset.univ.filter (fun j => j.val ∈ I)

theorem finRows_map (n : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range (n+2)) :
    (finRows n I).map Fin.valEmbedding = I := by
  ext a
  simp only [finRows, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact hj
  · intro ha
    exact ⟨⟨a, Finset.mem_range.mp (hI ha)⟩, ha, rfl⟩

theorem finRows_strip {n k : ℕ} {α : PartitionExponent n} (I : Finset ℕ)
    (hI : I ∈ (stripRows (toYoung α) k).filter (· ⊆ Finset.range (n+2))) :
    (finRows n I).card = k ∧ Antitone (increment α.val (finRows n I)) := by
  rw [Finset.mem_filter] at hI
  have hI1 := hI.1
  simp only [stripRows, Finset.mem_filter, Finset.mem_powerset] at hI1
  constructor
  · rw [← Finset.card_map Fin.valEmbedding, finRows_map n I hI.2, hI1.2.1]
  · intro i j hij
    have h := hI1.2.2 (show i.val ≤ j.val from hij)
    unfold rowInc at h
    rw [rowLen_toYoung, rowLen_toYoung] at h
    simp only [rowFun, dif_pos i.isLt, dif_pos j.isLt] at h
    simpa only [increment, finRows, Finset.mem_filter, Finset.mem_univ, true_and] using h

/-- Bridge: the all-shapes printed (3.10) implies the bounded row-set form. -/
theorem pieri310_bounded (n : ℕ) (h : Pieri310 (n+2)) : Pieri310Bounded n := by
  intro k hk α
  change CompleteTableauExpansion.sp (n+2) (toYoung α) *
      CompleteTableauExpansion.sp (n+2) (toYoung (column n k)) = _
  rw [toYoung_column n k hk, h (toYoung α) k]
  rw [← Finset.sum_filter_add_sum_filter_not (stripRows (toYoung α) k)
    (· ⊆ Finset.range (n+2))]
  rw [Finset.sum_eq_zero (s := (stripRows (toYoung α) k).filter (fun I => ¬ I ⊆ Finset.range (n+2))),
    add_zero]
  · symm
    refine Finset.sum_bij' (fun J _ => strRows J)
      (fun I hI => (⟨finRows n I, finRows_strip I hI⟩ : VerticalStrip n k α)) ?_ ?_ ?_ ?_ ?_
    · intro J _; exact strRows_mem J
    · intro I _; exact Finset.mem_univ _
    · intro J _
      apply Subtype.ext
      ext j
      simp [finRows, strRows, Fin.val_inj]
    · intro I hI
      exact finRows_map n I (Finset.mem_filter.mp hI).2
    · intro J _
      have hsign : (∑ a ∈ strRows J, belowRows (toYoung α) a) = lowerRows α.val J.val := by
        rw [strRows, Finset.sum_map]
        unfold lowerRows
        apply Finset.sum_congr rfl
        intro i _
        exact belowRows_toYoung α i
      have hmem := (Finset.mem_filter.mp (strRows_mem J)).1
      have hdiag : addStrip (toYoung α) k (strRows J) = toYoung (stripPartition J) := by
        apply YoungDiagram.ext
        ext p
        change p ∈ addStrip (toYoung α) k (strRows J) ↔ p ∈ toYoung (stripPartition J)
        rw [mem_addStrip _ _ hmem, mem_toYoung, rowInc_strRows]
      rw [hsign, hdiag]
  · intro I hI
    rw [Finset.mem_filter] at hI
    obtain ⟨a, ha, han⟩ := Finset.not_subset.mp hI.2
    rw [Finset.mem_range, not_lt] at han
    have hin : (a, (toYoung α).rowLen a) ∈ addStrip (toYoung α) k I := by
      rw [mem_addStrip _ _ hI.1]
      simp [rowInc, ha]
    have htall : (n+2, 0) ∈ addStrip (toYoung α) k I :=
      (addStrip (toYoung α) k I).isLowerSet (show ((n+2, 0) : ℕ × ℕ) ≤ (a, _) from
        ⟨han, Nat.zero_le _⟩) hin
    rw [sp_tall (n+2) _ htall, smul_zero]

/-- CONDITIONAL Theorem 3.8 (s^p = s^s) from the all-shapes printed (3.10). -/
theorem sp_eq_schur_of_pieri310 (n : ℕ) (h310 : Pieri310 (n+2)) (α : PartitionExponent n) :
    CompleteTableauExpansion.sp (n+2) (toYoung α) = schur n α :=
  sp_eq_schur_of_pieri310Bounded n (pieri310_bounded n h310) α

theorem sp_eq_schur_diagram_of_pieri310 (n : ℕ) (h310 : Pieri310 (n+2))
    (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n+2) :
    CompleteTableauExpansion.sp (n+2) μ = schur n (ofYoung μ) :=
  sp_eq_schur_diagram_of_pieri310Bounded n (pieri310_bounded n h310) μ hμ

end
end OddMath.Frontier.OddLRElimination
