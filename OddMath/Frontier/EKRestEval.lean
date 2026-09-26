import OddMath.Frontier.EKAppendixData
import OddMath.Frontier.EKCenterPowerControls

/-! # A row-recursive certified evaluator for mixed h/e pairings

EK arXiv:1107.5610v2, §2.2, Proposition 2.6 (p. 13), integral q = -1.

`fastEval β η α ε` evaluates the pairing `(h^η_β, h^ε_α)` of two mixed words
(`false` = complete `h`, `true` = elementary `e`) by peeling off the top row:
the top platform `b` meets a coordinatewise split `u ≤ α` of the bottom
(`EKMixedPairing.pairing_word_mul`, adjointness), with the single-platform value
`EKMixedPairing.pairing_gen_word`. This is the matrix sum of Proposition 2.6
enumerated row by row, so it runs in the kernel far faster than the
margin-matrix enumerator `EKAppendixData.mhEval`.

* `pairing_word_fastEval`: the free-algebra pairing of `word β η` and `word α ε`
  equals `fastEval`;
* `quotientPairing_mixed_fastEval`: the same in the quotient `Q`;
* `Mh_fast`, `M_fast`, `Me_fast`: the three Gram matrices `M′ = Mh`, `M`, `M″ = Me`
  of `EKDualBases` in terms of `fastEval`.
-/

noncomputable section
open scoped BigOperators TensorProduct

namespace OddMath.Frontier.EKRest
open CompleteElementary EKFreeCoproduct EKPairingAdjoint EKRadicalQuotient
open EKPairingMatrices EKMixedPairing

/-- All coordinatewise splits `u ≤ α` of a list of naturals with `∑ u = b`. -/
def splitsB : ℕ → List ℕ → List (List ℕ)
  | b, [] => if b = 0 then [[]] else []
  | b, a :: α => (List.range (min a b + 1)).flatMap (fun i => (splitsB (b - i) α).map (i :: ·))

/-- List form of `crossCols`: `∑_{l < j} u_j v_l`. -/
def crossL : List ℕ → List ℕ → ℕ
  | _ :: u, b :: v => b * u.sum + crossL u v
  | _, _ => 0

/-- List form of `∏_j cell b (ε j) (u j)`. -/
def cellsL (b : Bool) : List Bool → List ℕ → ℤ
  | e :: ε, a :: u => cell b e a * cellsL b ε u
  | _, _ => 1

/-- Row-recursive evaluator for `(h^η_β, h^ε_α)`. -/
def fastEval : List ℕ → List Bool → List ℕ → List Bool → ℤ
  | [], _, α, _ => if α.sum = 0 then 1 else 0
  | b :: β, η, α, ε => ((splitsB b α).map (fun u =>
      (-1 : ℤ) ^ crossL u (List.zipWith (· - ·) α u) * cellsL (η.headD false) ε u *
        fastEval β η.tail (List.zipWith (· - ·) α u) ε)).sum

/-- All-`h` specialisation. -/
def fastH (β α : List ℕ) : ℤ :=
  fastEval β (List.replicate β.length false) α (List.replicate α.length false)

/-- All-`e` top, all-`h` bottom (the matrix `M` of (3.2)). -/
def fastEH (β α : List ℕ) : ℤ :=
  fastEval β (List.replicate β.length true) α (List.replicate α.length false)

/-- All-`e` specialisation (the matrix `M″` of (3.2)). -/
def fastE (β α : List ℕ) : ℤ :=
  fastEval β (List.replicate β.length true) α (List.replicate α.length true)

/-! ## Correctness -/

theorem crossCols_ofFn {c : ℕ} (u v : Fin c → ℕ) :
    crossCols u v = crossL (List.ofFn u) (List.ofFn v) := by
  induction c with
  | zero => simp [crossCols, crossL]
  | succ c ih =>
    rw [crossCols_succ, List.ofFn_succ, List.ofFn_succ, crossL, ih, List.sum_ofFn]
    ring

theorem cellsL_ofFn (b : Bool) {c : ℕ} (ε : Fin c → Bool) (u : Fin c → ℕ) :
    ∏ j, cell b (ε j) (u j) = cellsL b (List.ofFn ε) (List.ofFn u) := by
  induction c with
  | zero => simp [cellsL]
  | succ c ih => rw [Fin.prod_univ_succ, List.ofFn_succ, List.ofFn_succ, cellsL, ih]

theorem zipWith_ofFn {c : ℕ} (a u : Fin c → ℕ) :
    List.zipWith (· - ·) (List.ofFn a) (List.ofFn u) = List.ofFn (fun j => a j - u j) := by
  induction c with
  | zero => simp
  | succ c ih => simp only [List.ofFn_succ, List.zipWith_cons_cons, ih]

theorem sum_range_list (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range f n]
  exact EKAppendixData.list_sum_range n f

theorem sum_flatMap_list {ι : Type*} (l : List ι) (f : ι → List ℤ) :
    (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_range_trunc (a b : ℕ) (T : ℕ → ℤ) (hT : ∀ i, b < i → T i = 0) :
    ∑ i ∈ Finset.range (a+1), T i = ∑ i ∈ Finset.range (min a b + 1), T i := by
  symm
  apply Finset.sum_subset
  · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    exact hT i (by omega)

/-- A sum over `Splits α` restricted to `∑ u = b` is a list sum over `splitsB b`. -/
theorem sum_splitsB {c : ℕ} (α : Fin c → ℕ) (b : ℕ) (G : List ℕ → ℤ) :
    ∑ u : Splits α, (if ∑ j, (u j : ℕ) = b then G (List.ofFn (fun j => (u j : ℕ))) else 0) =
      ((splitsB b (List.ofFn α)).map G).sum := by
  induction c generalizing b G with
  | zero =>
    rw [EKCenterPowerControls.sum_splits_zero]
    by_cases hb : b = 0 <;> simp [splitsB, hb, eq_comm]
  | succ c ih =>
    rw [EKCenterPowerControls.sum_splits_succ, List.ofFn_succ, splitsB, List.map_flatMap,
      sum_flatMap_list, EKAppendixData.list_sum_range, Finset.sum_fin_eq_sum_range]
    rw [sum_range_trunc (α 0) b]
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      have hib : i ≤ b := by omega
      have hia : i < α 0 + 1 := by omega
      rw [dif_pos hia]
      have := ih (fun j => α j.succ) (b - i) (fun l => G (i :: l))
      simp only [List.map_map, Function.comp_def] at this ⊢
      rw [← this]
      apply Finset.sum_congr rfl
      intro u _
      rw [Fin.sum_univ_succ, List.ofFn_succ]
      simp only [Fin.insertNth_apply_same, ← Fin.succAbove_zero, Fin.insertNth_apply_succAbove]
      by_cases h : ∑ j : Fin c, (u j : ℕ) = b - i
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    · intro i hi
      split_ifs with hia
      · apply Finset.sum_eq_zero
        intro u _
        rw [if_neg]
        rw [Fin.sum_univ_succ]
        simp only [Fin.insertNth_apply_same]
        simp only [Fin.val_mk] at *
        omega
      · rfl

/-- The free-algebra pairing of two mixed words is `fastEval`. -/
theorem pairing_word_fastEval {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :
    pairing (word β η) (word α ε) =
      fastEval (List.ofFn β) (List.ofFn η) (List.ofFn α) (List.ofFn ε) := by
  induction r generalizing α with
  | zero =>
    rw [word_zero, ← gen_zero false, pairing_gen_word, List.ofFn_zero, fastEval, List.sum_ofFn]
    by_cases h : ∑ j, α j = 0
    · rw [if_pos h.symm, if_pos h]
      apply Finset.prod_eq_one
      intro j _
      have : α j = 0 := by
        have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (α k))
          (Finset.mem_univ j)
        omega
      rw [this, cell_zero]
    · rw [if_neg (Ne.symm h), if_neg h]
  | succ r ih =>
    rw [word_succ, pairing_word_mul, List.ofFn_succ, List.ofFn_succ, fastEval]
    simp only [List.headD_cons, List.tail_cons]
    rw [← sum_splitsB]
    apply Finset.sum_congr rfl
    intro u _
    rw [pairing_gen_word, ih, zipWith_ofFn]
    by_cases hs : β 0 = ∑ j, (u j : ℕ)
    · rw [if_pos hs, if_pos hs.symm, crossCols_ofFn, cellsL_ofFn]
    · rw [if_neg hs, if_neg (Ne.symm hs)]
      ring

/-- EK Proposition 2.6 evaluated: the quotient pairing of two mixed words is `fastEval`. -/
theorem quotientPairing_mixed_fastEval {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :
    quotientPairing (mixed β η) (mixed α ε) =
      fastEval (List.ofFn β) (List.ofFn η) (List.ofFn α) (List.ofFn ε) := by
  rw [mixed_eq_pi, mixed_eq_pi, quotientPairing_pi, pairing_word_fastEval]

/-- The mixed word of explicit lists. -/
def mixedL (β : List ℕ) (η : List Bool) (h : η.length = β.length) : Q :=
  mixed (fun i : Fin β.length => β.get i) (fun i => η.get (Fin.cast h.symm i))

theorem quotientPairing_mixedL (β : List ℕ) (η : List Bool) (hη : η.length = β.length)
    (α : List ℕ) (ε : List Bool) (hε : ε.length = α.length) :
    quotientPairing (mixedL β η hη) (mixedL α ε hε) = fastEval β η α ε := by
  rw [mixedL, mixedL, quotientPairing_mixed_fastEval, List.ofFn_get, List.ofFn_get]
  congr 1
  · apply List.ext_get (by simp [hη]); intro n h1 h2; simp
  · apply List.ext_get (by simp [hε]); intro n h1 h2; simp

theorem hword_fastH (a b : List ℕ) :
    quotientPairing (EKAppendixData.hword a) (EKAppendixData.hword b) = fastH a b := by
  rw [EKAppendixData.hword, EKAppendixData.hword, quotientPairing_mixed_fastEval,
    List.ofFn_get, List.ofFn_get, List.ofFn_const, List.ofFn_const, fastH]

theorem mhEval_fastH (a b : List ℕ) : EKAppendixData.mhEval a b = fastH a b := by
  rw [← EKAppendixData.hword_pairing, hword_fastH]

open DegreeShapes EKDualBases EKPartitionSpanning in
/-- `M′ = Mh`, the h-basis Gram matrix, by `fastH` on row lengths. -/
theorem Mh_fast (d : ℕ) (ν μ : DegreeShape d) :
    Mh d ν μ = fastH ν.val.rowLens μ.val.rowLens := by
  rw [EKAppendixData.Mh_eval, mhEval_fastH]

/-- The colour-`c` generator in `Q` (`false` = `h`, `true` = `e`). -/
def col (c : Bool) (n : ℕ) : Q := if c then EKElementaryQuotient.e n else EKElementaryQuotient.h n

theorem mixed_const (c : Bool) (l : List ℕ) :
    mixed (fun i : Fin l.length => l.get i) (fun _ => c) = (l.map (col c)).prod := by
  rw [mixed]
  congr 1
  apply List.ext_get (by simp)
  intro n h1 h2
  simp [col]

/-- Pairing of two constant-colour words of explicit lists. -/
theorem pairing_const (c d : Bool) (a b : List ℕ) :
    quotientPairing (a.map (col c)).prod (b.map (col d)).prod =
      fastEval a (List.replicate a.length c) b (List.replicate b.length d) := by
  rw [← mixed_const, ← mixed_const, quotientPairing_mixed_fastEval, List.ofFn_get, List.ofFn_get,
    List.ofFn_const, List.ofFn_const]

theorem hPartition_col (μ : YoungDiagram) :
    EKPartitionSpanning.hPartition μ = (μ.rowLens.map (col false)).prod := by
  rw [EKPartitionSpanning.hPartition]; congr 2

theorem ePartition_col (μ : YoungDiagram) :
    EKPartitionSpanning.ePartition μ = (μ.rowLens.map (col true)).prod := by
  rw [EKPartitionSpanning.ePartition]; congr 2

open DegreeShapes EKDualBases in
/-- `M`, the e/h Gram matrix of (3.2), by `fastEH` on row lengths. -/
theorem M_fast (d : ℕ) (ν μ : DegreeShape d) :
    M d ν μ = fastEH ν.val.rowLens μ.val.rowLens := by
  rw [M, ePartition_col, hPartition_col, pairing_const, fastEH]

open DegreeShapes EKDualBases in
/-- `M″ = Me`, the e-basis Gram matrix of (3.2), by `fastE` on row lengths. -/
theorem Me_fast (d : ℕ) (ν μ : DegreeShape d) :
    Me d ν μ = fastE ν.val.rowLens μ.val.rowLens := by
  rw [Me, ePartition_col, ePartition_col, pairing_const, fastE]

end OddMath.Frontier.EKRest
