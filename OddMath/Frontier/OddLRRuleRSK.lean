import OddMath.Frontier.OddLRRuleGrowth
import OddMath.Frontier.EKRskBijection
import OddMath.Frontier.EKRskSign

/-!
# The RSK correspondence: insertion words, recording shapes, symmetry

For the library RSK map `EKRskBijection.rskRec` (EK arXiv:1107.5610v2, §4.1, Theorem 4.3):

* `nrows_rskP`: the rows of `P(A)` are the list-level insertion tableau of the column word;
* `sh_res_nrows_rskQ`: the entries `≤ i` of `Q(A)` fill the insertion shape of the first `i`
  rows of `A`;
* `nrows_rskP_transpose`: the Symmetry Theorem `P(Aᵀ) = Q(A)` (Fulton, *Young Tableaux*,
  §4.1), from the growth-diagram symmetry `OddLRRule.G_transpose`;
* `rskRec_join`: RSK of a stacked matrix continues RSK of the upper block.

These are the RSK facts used in the proof of Ellis, arXiv:1111.3932v1, Theorem 4.8, which
cites Fulton §5.2.
-/

namespace OddMath.Frontier.OddLRRule

open EKClassicalPlactic TableauSign TableauEvaluation
open EKRskBijection (Pairs Tab rskRec step emptyPairs)

/-! ## Rows of a tableau as lists of natural numbers -/

/-- Rows of `T`, top row first. -/
noncomputable def nrows {μ : YoungDiagram} (T : PositiveTableau μ) : List (List ℕ) :=
  (List.range (μ.colLen 0)).map (fun r => (List.range (μ.rowLen r)).map (fun c => T.entry r c))

theorem nrows_eq_rows {n : ℕ} {μ : YoungDiagram} (T : PositiveTableau μ) (hT : InAlphabet n T) :
    nrows T = (TableauRowRecursion.rows n T hT).map (List.map lab) := by
  simp only [nrows, TableauRowRecursion.rows, List.map_map]
  apply List.map_congr_left
  intro r _
  exact (TableauRowStep.row_labels n μ T hT r).symm

theorem rowLen_eq_zero {μ : YoungDiagram} {r : ℕ} (h : μ.colLen 0 ≤ r) : μ.rowLen r = 0 := by
  by_contra hne
  have : (r, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
  have := YoungDiagram.mem_iff_lt_colLen.mp this
  omega

theorem rowAt_nrows {μ : YoungDiagram} (T : PositiveTableau μ) (k : ℕ) :
    rowAt (nrows T) k = (List.range (μ.rowLen k)).map (fun c => T.entry k c) := by
  unfold rowAt nrows
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hk : k < μ.colLen 0
  · simp [List.getElem?_range hk]
  · rw [List.getElem?_eq_none (by simpa using hk), rowLen_eq_zero (by omega)]
    rfl

theorem sh_nrows {μ : YoungDiagram} (T : PositiveTableau μ) (k : ℕ) : sh (nrows T) k = μ.rowLen k := by
  simp [sh, rowAt_nrows]

/-- A bound for all entries. -/
noncomputable def entryBound {μ : YoungDiagram} (T : PositiveTableau μ) : ℕ :=
  (TableauRowWord.rowWord T).foldr max 0

theorem inAlphabet_entryBound {μ : YoungDiagram} (T : PositiveTableau μ) :
    InAlphabet (entryBound T) T :=
  inAlphabet_of_knuth T (fun _ ha => le_foldr_max ha) (knuth_refl _)

theorem nrows_valid {μ : YoungDiagram} (T : PositiveTableau μ) : Valid (nrows T) := by
  rw [nrows_eq_rows T (inAlphabet_entryBound T)]
  exact valid_rows T _

theorem valid_sorted : ∀ {rs : List (List ℕ)}, Valid rs → RowsSorted rs
  | [], _ => by simp [RowsSorted]
  | R :: rs, h => by
    intro S hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact h.2.1
    · exact valid_sorted h.2.2.2 S hS

theorem valid_ne_nil : ∀ {rs : List (List ℕ)}, Valid rs → ∀ R ∈ rs, R ≠ []
  | [], _ => by simp
  | R :: rs, h => by
    intro S hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact h.1
    · exact valid_ne_nil h.2.2.2 S hS

theorem nrows_sorted {μ : YoungDiagram} (T : PositiveTableau μ) : RowsSorted (nrows T) :=
  valid_sorted (nrows_valid T)

/-- `Eqv` lists without empty rows are equal. -/
theorem eq_of_eqv : ∀ {rs rs' : List (List ℕ)}, (∀ R ∈ rs, R ≠ []) → (∀ R ∈ rs', R ≠ []) →
    Eqv rs rs' → rs = rs'
  | [], [], _, _, _ => rfl
  | [], R :: rs', _, h', h => absurd (eqv_nil_cons_iff.mp h).1 (h' R List.mem_cons_self)
  | R :: rs, [], h, _, h'' => absurd (eqv_nil_cons_iff.mp h''.symm).1 (h R List.mem_cons_self)
  | R :: rs, R' :: rs', h, h', h'' => by
    obtain ⟨rfl, ht⟩ := eqv_cons_iff.mp h''
    rw [eq_of_eqv (fun S hS => h S (List.mem_cons_of_mem _ hS))
      (fun S hS => h' S (List.mem_cons_of_mem _ hS)) ht]

theorem sigma_eq_of_nrows {μ μ' : YoungDiagram} (T : PositiveTableau μ) (T' : PositiveTableau μ')
    (h : nrows T = nrows T') :
    (⟨μ, T⟩ : Σ μ : YoungDiagram, PositiveTableau μ) = ⟨μ', T'⟩ := by
  have hk : KnuthEquiv (TableauRowWord.rowWord T) (TableauRowWord.rowWord T') := by
    rw [rowWord_eq_readR _ T (inAlphabet_entryBound T),
      rowWord_eq_readR _ T' (inAlphabet_entryBound T'), ← nrows_eq_rows, ← nrows_eq_rows, h]
    exact knuth_refl _
  exact tableau_eq_of_knuth T T' hk

theorem rowWord_eq_readR_nrows {μ : YoungDiagram} (T : PositiveTableau μ) :
    TableauRowWord.rowWord T = readR (nrows T) := by
  rw [rowWord_eq_readR _ T (inAlphabet_entryBound T), ← nrows_eq_rows]

/-! ## The column word of a matrix -/

variable {R C : ℕ}

/-- Column word of `A` (labels `1..C`), rows read in order. -/
def colword (A : Fin R → Fin C → ℕ) : List ℕ :=
  ((List.finRange R).flatMap fun i => EKRskBijection.rowWord (A i)).map lab

/-- Extension of `A` by zero to `ℕ × ℕ`, one-based. -/
def ext (A : Fin R → Fin C → ℕ) (p q : ℕ) : ℕ :=
  if h : 0 < p ∧ p ≤ R ∧ 0 < q ∧ q ≤ C then A ⟨p - 1, by omega⟩ ⟨q - 1, by omega⟩ else 0

theorem flatMap_finRange {α : Type*} (n : ℕ) (f : Fin n → List α) (g : ℕ → List α)
    (h : ∀ i : Fin n, f i = g i.val) : (List.finRange n).flatMap f = (List.range n).flatMap g := by
  rw [← List.map_coe_finRange, List.flatMap_map]
  exact List.flatMap_congr (fun i _ => h i)

theorem colword_eq_word (A : Fin R → Fin C → ℕ) : colword A = word (ext A) R C := by
  unfold colword word
  rw [List.map_flatMap]
  apply flatMap_finRange
  intro i
  unfold EKRskBijection.rowWord rowW
  rw [List.map_flatMap]
  apply flatMap_finRange
  intro j
  simp only [List.map_replicate, lab, ext]
  rw [dif_pos (by omega)]
  rfl

/-! ## `P(A)` is the insertion tableau of the column word -/

theorem nrows_run (n : ℕ) (S : TableauWordInsertion.State n) (w : List (Fin n)) :
    nrows (TableauWordInsertion.run n S w).1.2.1 = insW (nrows S.2.1) (w.map lab) := by
  rw [nrows_eq_rows _ (TableauWordInsertion.run n S w).1.2.2, run_rows, foldl_runRows_map,
    ← nrows_eq_rows]

theorem nrows_empty : nrows (TableauContent.emptyTableau) = [] := by
  have h : (⊥ : YoungDiagram).colLen 0 = 0 := by
    by_contra hne
    exact YoungDiagram.not_mem_bot (0, 0)
      (YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero hne))
  simp [nrows, h]

theorem colword_succ (A : Fin (R + 1) → Fin C → ℕ) :
    colword A = colword (Fin.init A) ++ (EKRskBijection.rowWord (A (Fin.last R))).map lab := by
  simp [colword, List.finRange_succ_last, List.flatMap_append, List.flatMap_map, Fin.init]

theorem colword_zero (A : Fin 0 → Fin C → ℕ) : colword A = [] := by simp [colword]

theorem nrows_rskP (C : ℕ) : ∀ (R : ℕ) (A : Fin R → Fin C → ℕ),
    nrows (rskRec C R A).2.1.1 = P (colword A)
  | 0, A => by
    rw [colword_zero]
    exact nrows_empty
  | R + 1, A => by
    change nrows (TableauWordInsertion.run C (rskRec C R (Fin.init A)).pState
      (EKRskBijection.rowWord (A (Fin.last R)))).1.2.1 = _
    rw [nrows_run, colword_succ, P_append]
    congr 1
    exact nrows_rskP C R (Fin.init A)

/-! ## `Q(A)` records the insertion shapes -/

theorem word_congr {B B' : ℕ → ℕ → ℕ} {i : ℕ} (j : ℕ) (h : ∀ p, 0 < p → p ≤ i → ∀ q, B p q = B' p q) :
    word B i j = word B' i j := by
  unfold word
  apply List.flatMap_congr
  intro p hp
  have hp' := List.mem_range.mp hp
  unfold rowW
  apply List.flatMap_congr
  intro q _
  rw [h (p + 1) (by omega) (by omega)]

theorem word_stable {B : ℕ → ℕ → ℕ} {R : ℕ} (hB : ∀ p, R < p → ∀ q, B p q = 0) (j : ℕ) :
    ∀ i, R ≤ i → word B i j = word B R j := by
  intro i hi
  induction i with
  | zero => have : R = 0 := by omega
            subst this; rfl
  | succ i ih =>
    rcases Nat.eq_or_lt_of_le hi with h | h
    · rw [h]
    · rw [word_succ, ih (by omega)]
      have : rowW B (i + 1) j = [] := by
        simp [rowW, hB (i + 1) (by omega)]
      rw [this, List.append_nil]

theorem ext_zero (A : Fin R → Fin C → ℕ) : ∀ p, R < p → ∀ q, ext A p q = 0 := by
  intro p hp q
  simp only [ext]
  rw [dif_neg (by omega)]

theorem ext_init (A : Fin (R + 1) → Fin C → ℕ) : ∀ p, 0 < p → p ≤ R → ∀ q,
    ext (Fin.init A) p q = ext A p q := by
  intro p hp hpR q
  simp only [ext]
  by_cases hq : 0 < q ∧ q ≤ C
  · rw [dif_pos (by omega), dif_pos (by omega)]
    rfl
  · rw [dif_neg (by omega), dif_neg (by omega)]

theorem rowLen_le_of_subset {mu nu : YoungDiagram} (h : mu.cells ⊆ nu.cells) (k : ℕ) :
    mu.rowLen k ≤ nu.rowLen k := by
  by_contra hlt
  have hm : (k, nu.rowLen k) ∈ mu := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  have hn : (k, nu.rowLen k) ∈ nu := by simpa using h (by simpa using hm)
  have := YoungDiagram.mem_iff_lt_rowLen.mp hn
  omega

theorem rowAt_nrows_extend {mu nu : YoungDiagram} (T : PositiveTableau mu) (r : ℕ)
    (hb : InAlphabet r T) (hh : TableauStripCorners.Horizontal mu nu) (k : ℕ) :
    rowAt (nrows (CompleteTableauExpansion.extendTableau T r hb hh)) k =
      rowAt (nrows T) k ++ List.replicate (nu.rowLen k - mu.rowLen k) (r + 1) := by
  rw [rowAt_nrows, rowAt_nrows]
  have hle := rowLen_le_of_subset hh.1 k
  obtain ⟨d, hd⟩ : ∃ d, nu.rowLen k = mu.rowLen k + d := ⟨_, (Nat.add_sub_of_le hle).symm⟩
  rw [hd, List.range_add, List.map_append, Nat.add_sub_cancel_left]
  congr 1
  · apply List.map_congr_left
    intro c hc
    have hm : (k, c) ∈ mu.cells := by
      simpa using YoungDiagram.mem_iff_lt_rowLen.mpr (List.mem_range.mp hc)
    exact CompleteTableauExpansion.extend_old T r hb hh hm
  · rw [List.map_map, List.eq_replicate_iff]
    refine ⟨by simp, fun b hb' => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb'
    have hc' := List.mem_range.mp hc
    have hn : (k, mu.rowLen k + c) ∈ nu.cells \ mu.cells := by
      simp only [Finset.mem_sdiff, YoungDiagram.mem_cells]
      exact ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega),
        fun h => by have := YoungDiagram.mem_iff_lt_rowLen.mp h; omega⟩
    exact CompleteTableauExpansion.extend_new T r hb hh hn

theorem res_nrows_of_bound {μ : YoungDiagram} (T : PositiveTableau μ) {n i : ℕ} (hT : InAlphabet n T)
    (hi : n ≤ i) : res i (nrows T) = nrows T := by
  unfold res
  conv_rhs => rw [← List.map_id (nrows T)]
  apply List.map_congr_left
  intro R hR
  apply filter_le_of_le
  intro y hy
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hR
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
  by_cases hm : (r, c) ∈ μ
  · exact le_trans (hT (r, c) (by simpa using hm)) hi
  · rw [T.zeros' hm]; omega

/-- The entries `≤ i` of `Q(A)` fill the insertion shape of the first `i` rows. -/
theorem sh_res_nrows_rskQ (C : ℕ) : ∀ (R : ℕ) (A : Fin R → Fin C → ℕ) (i k : ℕ),
    sh (res i (nrows (rskRec C R A).2.2.1)) k = G (ext A) i C k
  | 0, A, i, k => by
    change sh (res i (nrows TableauContent.emptyTableau)) k = _
    rw [nrows_empty, G, word_stable (ext_zero A) C i (Nat.zero_le _)]
    simp [sh, res, word, P, insW]
  | R + 1, A, i, k => by
    by_cases hi : i ≤ R
    · have hQ : Eqv (res i (nrows (rskRec C (R + 1) A).2.2.1))
          (res i (nrows (rskRec C R (Fin.init A)).2.2.1)) := by
        intro k'
        rw [rowAt_res, rowAt_res]
        change ((rowAt (nrows (CompleteTableauExpansion.extendTableau
          (rskRec C R (Fin.init A)).2.2.1 R (rskRec C R (Fin.init A)).2.2.2
          (EKRskBijection.run_horizontal' C (rskRec C R (Fin.init A)).pState
            (A (Fin.last R))))) k').filter _) = _
        rw [rowAt_nrows_extend, List.filter_append,
          filter_le_of_gt (List.replicate _ (R + 1))
            (fun y hy => by rw [List.eq_of_mem_replicate hy]; omega),
          List.append_nil]
      rw [sh_eqv hQ, sh_res_nrows_rskQ C R (Fin.init A) i k, G, G,
        word_congr (i := i) C (fun p hp hpi q => ext_init A p hp (by omega) q)]
    · have hb := (rskRec C (R + 1) A).2.2.2
      rw [res_nrows_of_bound _ hb (by omega), sh_nrows]
      have hP := sh_nrows (rskRec C (R + 1) A).2.1.1 k
      rw [← hP, nrows_rskP, colword_eq_word, G,
        word_stable (ext_zero A) C i (by omega)]

/-! ## The Symmetry Theorem -/

theorem word_filter_add (B : ℕ → ℕ → ℕ) (i j : ℕ) : ∀ t,
    (word B i (j + t)).filter (fun x => decide (x ≤ j)) = word B i j
  | 0 => filter_le_of_le _ (fun y hy => (mem_word hy).2)
  | t + 1 => by
    have h : (word B i (j + (t + 1))).filter (fun x => decide (x ≤ j)) =
        ((word B i (j + t + 1)).filter (fun x => decide (x ≤ j + t))).filter
          (fun x => decide (x ≤ j)) := by
      rw [List.filter_filter, ← Nat.add_assoc]
      congr 1
      funext x
      by_cases hx : x ≤ j
      · simp [hx, show x ≤ j + t by omega]
      · simp [hx]
    rw [h, word_filter, word_filter_add B i j t]

theorem ext_transpose (A : Fin R → Fin C → ℕ) (p q : ℕ) :
    ext (fun j i => A i j) p q = ext A q p := by
  simp only [ext]
  by_cases h : 0 < p ∧ p ≤ C ∧ 0 < q ∧ q ≤ R
  · rw [dif_pos h, dif_pos (by omega)]
  · rw [dif_neg h, dif_neg (by omega)]

theorem sh_res_P_word (B : ℕ → ℕ → ℕ) (a b i k : ℕ) :
    sh (res i (P (word B a b))) k = G B a (min i b) k := by
  rw [sh_eqv (res_P i _) k, G]
  by_cases hi : i ≤ b
  · obtain ⟨t, rfl⟩ : ∃ t, b = i + t := ⟨b - i, by omega⟩
    rw [word_filter_add, min_eq_left hi]
  · rw [filter_le_of_le _ (fun y hy => by have := (mem_word hy).2; omega),
      min_eq_right (by omega)]

/-- **Symmetry Theorem** (Fulton §4.1): `P(Aᵀ) = Q(A)`, compared as rows. -/
theorem nrows_rskP_transpose (A : Fin R → Fin C → ℕ) :
    nrows (rskRec R C (fun j i => A i j)).2.1.1 = nrows (rskRec C R A).2.2.1 := by
  apply eq_of_eqv (valid_ne_nil (nrows_valid _)) (valid_ne_nil (nrows_valid _))
  apply eqv_of_sh_res (nrows_sorted _) (nrows_sorted _)
  intro i k
  rw [nrows_rskP, colword_eq_word, sh_res_P_word, sh_res_nrows_rskQ]
  have hT : ext (fun j i => A i j) = fun p q => ext A q p := by
    funext p q; exact ext_transpose A p q
  rw [hT, G_transpose]
  by_cases hi : i ≤ R
  · rw [min_eq_left hi]
  · rw [min_eq_right (by omega), G, G, word_stable (ext_zero A) C i (by omega)]

/-- The symmetry theorem for sigma-tableaux. -/
theorem rskP_transpose (A : Fin R → Fin C → ℕ) :
    (⟨(rskRec R C (fun j i => A i j)).1, (rskRec R C (fun j i => A i j)).2.1.1⟩ :
      Σ μ : YoungDiagram, PositiveTableau μ) =
      ⟨(rskRec C R A).1, (rskRec C R A).2.2.1⟩ :=
  sigma_eq_of_nrows _ _ (nrows_rskP_transpose A)

/-! ## RSK of a stacked matrix -/

/-- Continue RSK from the pair `z` with the rows of `V`. -/
noncomputable def rskFrom (C m : ℕ) (z : Pairs C m) : (r : ℕ) → (Fin r → Fin C → ℕ) → Pairs C (m + r)
  | 0, _ => z
  | r + 1, V => step C (m + r) (rskFrom C m z r (Fin.init V)) (V (Fin.last r))

theorem join_init {m r : ℕ} (U : Fin m → Fin C → ℕ) (V : Fin (r + 1) → Fin C → ℕ) :
    Fin.init (n := m + r) (α := fun _ => Fin C → ℕ) (EKPairingMatrices.join (r := m) (s := r + 1) U V) =
      EKPairingMatrices.join U (Fin.init V) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · have : (Fin.castSucc (Fin.castAdd r a) : Fin (m + (r + 1))) = Fin.castAdd (r + 1) a := rfl
    simp only [Fin.init, this, EKPairingMatrices.join_left]
  · have : (Fin.castSucc (Fin.natAdd m b) : Fin (m + (r + 1))) = Fin.natAdd m (Fin.castSucc b) := rfl
    simp only [Fin.init, this, EKPairingMatrices.join_right]

theorem join_last {m r : ℕ} (U : Fin m → Fin C → ℕ) (V : Fin (r + 1) → Fin C → ℕ) :
    EKPairingMatrices.join U V (Fin.last (m + r)) = V (Fin.last r) := by
  have : (Fin.last (m + r) : Fin (m + (r + 1))) = Fin.natAdd m (Fin.last r) := rfl
  rw [this, EKPairingMatrices.join_right]

theorem join_zero {m : ℕ} (U : Fin m → Fin C → ℕ) (V : Fin 0 → Fin C → ℕ) :
    (EKPairingMatrices.join U V : Fin (m + 0) → Fin C → ℕ) = U := by
  funext i
  exact EKPairingMatrices.join_left U V i

theorem rskRec_join {m : ℕ} (U : Fin m → Fin C → ℕ) : ∀ (r : ℕ) (V : Fin r → Fin C → ℕ),
    rskRec C (m + r) (EKPairingMatrices.join U V) = rskFrom C m (rskRec C m U) r V
  | 0, V => by rw [join_zero]; rfl
  | r + 1, V => by
    change step C (m + r) (rskRec C (m + r) (Fin.init (n := m + r) (α := fun _ => Fin C → ℕ)
      (EKPairingMatrices.join (r := m) (s := r + 1) U V)))
      (EKPairingMatrices.join U V (Fin.last (m + r))) = _
    rw [join_init, join_last, rskRec_join U r (Fin.init V)]
    rfl

theorem nrows_rskFrom (C m : ℕ) (z : Pairs C m) : ∀ (r : ℕ) (V : Fin r → Fin C → ℕ),
    nrows (rskFrom C m z r V).2.1.1 = insW (nrows z.2.1.1) (colword V)
  | 0, V => by rw [colword_zero]; rfl
  | r + 1, V => by
    change nrows (TableauWordInsertion.run C (rskFrom C m z r (Fin.init V)).pState
      (EKRskBijection.rowWord (V (Fin.last r)))).1.2.1 = _
    rw [nrows_run, colword_succ, insW_append]
    congr 1
    exact nrows_rskFrom C m z r (Fin.init V)

/-- Old cells keep their labels; new cells get labels `> m`. -/
theorem rskFrom_Q (C m : ℕ) (z : Pairs C m) : ∀ (r : ℕ) (V : Fin r → Fin C → ℕ),
    z.1.cells ⊆ (rskFrom C m z r V).1.cells ∧
      (∀ p ∈ z.1.cells, (rskFrom C m z r V).2.2.1.entry p.1 p.2 = z.2.2.1.entry p.1 p.2) ∧
      (∀ p ∈ (rskFrom C m z r V).1.cells, p ∉ z.1.cells →
        m < (rskFrom C m z r V).2.2.1.entry p.1 p.2)
  | 0, V => ⟨subset_rfl, fun _ _ => rfl, fun p h h' => absurd h h'⟩
  | r + 1, V => by
    obtain ⟨h1, h2, h3⟩ := rskFrom_Q C m z r (Fin.init V)
    set y := rskFrom C m z r (Fin.init V)
    have hh := EKRskBijection.run_horizontal' C y.pState (V (Fin.last r))
    change z.1.cells ⊆ (TableauWordInsertion.run C y.pState _).1.1.cells ∧
      (∀ p ∈ z.1.cells, (CompleteTableauExpansion.extendTableau y.2.2.1 (m + r) y.2.2.2 hh).entry
        p.1 p.2 = z.2.2.1.entry p.1 p.2) ∧
      (∀ p ∈ (TableauWordInsertion.run C y.pState _).1.1.cells, p ∉ z.1.cells →
        m < (CompleteTableauExpansion.extendTableau y.2.2.1 (m + r) y.2.2.2 hh).entry p.1 p.2)
    refine ⟨h1.trans hh.1, fun p hp => ?_, fun p hp hpz => ?_⟩
    · rw [CompleteTableauExpansion.extend_old _ _ _ _ (h1 hp), h2 p hp]
    · by_cases hy : p ∈ y.1.cells
      · rw [CompleteTableauExpansion.extend_old _ _ _ _ hy]
        exact h3 p hy hpz
      · rw [CompleteTableauExpansion.extend_new _ _ _ _ (Finset.mem_sdiff.mpr ⟨hp, hy⟩)]
        omega

/-! ## Agreement with the RSK map of `EKRskSign`, and the sign identity -/

/-- Relation between the two RSK states. -/
def StRel (s : EKRskSign.St R C) (t : EKRskBijection.St C × (ℕ × ℕ → ℕ)) : Prop :=
  (⟨s.shape, ⟨s.P, s.hP⟩⟩ : TableauWordInsertion.State C) = t.1 ∧ ∀ i j, s.Q i j = t.2 (i, j)

theorem stRel_step (s : EKRskSign.St R C) (t : EKRskBijection.St C × (ℕ × ℕ → ℕ))
    (h : StRel s t) (x : Fin R × Fin C) :
    StRel (EKRskSign.step s x) (EKRskBijection.foldStep C t (x.1.val, x.2)) := by
  obtain ⟨s1, s2, s3, s4⟩ := s
  obtain ⟨⟨t1, t2, t3⟩, q⟩ := t
  obtain ⟨he, hq⟩ := h
  simp only [Sigma.mk.injEq] at he
  obtain ⟨rfl, he⟩ := he
  have : s2 = t2 := by
    have := eq_of_heq he
    simp only [Subtype.mk.injEq] at this
    exact this
  subst this
  refine ⟨rfl, fun i j => ?_⟩
  simp only [EKRskSign.step, EKRskBijection.foldStep]
  split_ifs <;> first | rfl | exact hq i j

theorem twoLine_eq (A : Fin R → Fin C → ℕ) :
    EKRskBijection.twoLine A = (EKRskSign.twoLine A).map (fun x => (x.1.val, x.2)) := by
  simp [EKRskBijection.twoLine, EKRskSign.twoLine, EKRskBijection.rowWord, List.map_flatMap,
    List.map_replicate]

theorem stRel_fold (L : List (Fin R × Fin C)) : ∀ s t, StRel s t →
    StRel (L.foldl EKRskSign.step s) ((L.map (fun x => (x.1.val, x.2))).foldl
      (EKRskBijection.foldStep C) t) := by
  induction L with
  | nil => intro s t h; exact h
  | cons x L ih => intro s t h; exact ih _ _ (stRel_step s t h x)

theorem stRel_rsk (A : Fin R → Fin C → ℕ) : StRel (EKRskSign.rskState A) (EKRskBijection.rskFold A) := by
  unfold EKRskSign.rskState EKRskBijection.rskFold
  rw [twoLine_eq]
  exact stRel_fold _ _ _ ⟨rfl, fun _ _ => rfl⟩

theorem rskP_sigma (A : Fin R → Fin C → ℕ) :
    (⟨(rskRec C R A).1, (rskRec C R A).2.1.1⟩ : Σ μ : YoungDiagram, PositiveTableau μ) =
      ⟨EKRskSign.rskShape A, EKRskSign.rskP A⟩ := by
  have h1 := (stRel_rsk A).1
  rw [(EKRskBijection.rsk_eq_frozen C R A).1] at h1
  have := congrArg (fun S : TableauWordInsertion.State C => (⟨S.1, S.2.1⟩ :
    Σ μ : YoungDiagram, PositiveTableau μ)) h1
  exact this.symm

theorem rskQ_sigma (A : Fin R → Fin C → ℕ) :
    (⟨(rskRec C R A).1, (rskRec C R A).2.2.1⟩ : Σ μ : YoungDiagram, PositiveTableau μ) =
      ⟨EKRskSign.rskShape A, EKRskSign.rskQ A⟩ := by
  have h1 := (stRel_rsk A).1
  rw [(EKRskBijection.rsk_eq_frozen C R A).1] at h1
  have hsh : (rskRec C R A).1 = EKRskSign.rskShape A := (congrArg Sigma.fst h1).symm
  apply sigma_eq _ _ hsh
  intro i j
  change _ = (EKRskSign.rskState A).Q i j
  rw [(stRel_rsk A).2 i j, (EKRskBijection.rsk_eq_frozen C R A).2 (i, j)]

theorem tableauSign_congr {μ μ' : YoungDiagram} {T : PositiveTableau μ} {T' : PositiveTableau μ'}
    (h : (⟨μ, T⟩ : Σ μ : YoungDiagram, PositiveTableau μ) = ⟨μ', T'⟩) :
    TableauDominance.tableauSign T = TableauDominance.tableauSign T' := by
  cases h; rfl

theorem colword_eq_twoLine (A : Fin R → Fin C → ℕ) :
    colword A = (EKRskSign.twoLine A).map (fun x => EKRskSign.lab x.2) := by
  have : (EKRskSign.twoLine A).map (fun x => EKRskSign.lab x.2) =
      ((EKRskSign.twoLine A).map Prod.snd).map EKRskSign.lab := by rw [List.map_map]; rfl
  rw [this, EKRskSign.twoLine_snd]
  rfl

/-- The odd RSK sign (EK Thm 3.7, (3.8)) for the library map `rskRec`, in word form:
`(-1)^{inv(column word)} = (-1)^{binom(λᵀ,2)} sign(P) sign(Q)`. -/
theorem rsk_sign (A : Fin R → Fin C → ℕ) :
    (-1 : ℤ) ^ TableauRowWord.inversions (colword A) =
      (-1 : ℤ) ^ EKRskSign.shapeExp (rskRec C R A).1 *
        TableauDominance.tableauSign (rskRec C R A).2.1.1 *
        TableauDominance.tableauSign (rskRec C R A).2.2.1 := by
  have h := EKRskSign.thm_3_7_sign A
  rw [← EKRskSign.inversions_twoLine] at h
  rw [colword_eq_twoLine, h, tableauSign_congr (rskP_sigma A), tableauSign_congr (rskQ_sigma A),
    congrArg Sigma.fst (rskP_sigma A)]

end OddMath.Frontier.OddLRRule
