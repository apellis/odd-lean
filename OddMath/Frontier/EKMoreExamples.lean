import OddMath.Frontier.EKCompleteErrata
import OddMath.Frontier.EKRestData
import OddMath.Frontier.EKSchurOrthonormalControls
import OddMath.Frontier.OddLRExamplesTools

/-!
# [EK] §§3.1–3.3: Example 3.2, the expansion of `p₆`, Examples 3.5 and 3.6

Source: A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*,
arXiv:1107.5610v2.

* Example 3.2, p. 24. The ℕ-matrices with row sums `(3,2)` and column sums `(2,2,1)` are exactly
  the five printed ones (`ex32_exhaustive`, `ex32_mem`). Their SW–NE counts are `0, 2, 2, 3, 6`,
  only the fourth is a `{0,1}`-matrix, and their cable exponents `Σ C(a,2)` are `1, 2, 1, 0, 2`
  (`ex32_table`). The printed cable exponents `C(3,2), C(3,2)+C(3,2), C(3,2), 0,
  C(3,2)+C(3,2)` misprint `C(2,2)` as `C(3,2)` (`ex32_printed_cable_exponents_differ`), but give
  the same signs (`ex32_printed_cable_signs`), so every printed contribution is correct and the
  column sums are `−1, 3, −1` (`ex32_column_sums`, agreeing with `EKRest.example_3_2`).
* p. 25: the printed `p₆ = h₁₁₁₁₁₁ + 3h₂₂₁₁ − 3h₃₃ − 6h₄₁₁ + 6h₅₁` holds (`p_six`).
* Example 3.5, p. 27: the five standard tableaux of shape `(2,2,1)` have signs `+ − − + −`
  (`ex35_signs`), their row words are exactly the valid fillings of `(2,2,1)` with content `1⁵`
  (`ex35_words`), and `K_{(2,2,1),(1⁵)} = sign(T_{(2,2,1)}) Σ_T sign(T) = −1` (`ex35_kostka`).
* Example 3.6, p. 27: the three tableaux of shape `(3,1,1)` and content `(2,1,1,1)` have signs
  `− + −` (`ex36_signs`, `ex36_words`), and `K_{(3,1,1),(2,1,1,1)} = 1` (`ex36_kostka`).
-/

noncomputable section
set_option maxRecDepth 100000
open scoped BigOperators

namespace OddMath.Frontier.EKMore
open EKRadicalQuotient EKPairingMatrices

/-! ## Example 3.2 -/

/-- The five printed matrices of Example 3.2, in printed order. -/
def ex32Mats : List (Raw 2 3) :=
  [![![2, 1, 0], ![0, 1, 1]], ![![2, 0, 1], ![0, 2, 0]], ![![1, 2, 0], ![1, 0, 1]],
    ![![1, 1, 1], ![1, 1, 0]], ![![0, 2, 1], ![2, 0, 0]]]

theorem raw23_eta (A : Raw 2 3) :
    A = ![![A 0 0, A 0 1, A 0 2], ![A 1 0, A 1 1, A 1 2]] := by
  funext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Every ℕ-matrix with row sums `(3,2)` and column sums `(2,2,1)` is one of the printed five. -/
theorem ex32_exhaustive (A : Raw 2 3) (hr : rowSum A = ![3, 2]) (hc : colSum A = ![2, 2, 1]) :
    A ∈ ex32Mats := by
  have r0 := congrFun hr 0
  have r1 := congrFun hr 1
  have c0 := congrFun hc 0
  have c1 := congrFun hc 1
  have c2 := congrFun hc 2
  simp only [rowSum, colSum, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, add_zero, Fin.isValue] at r0 r1 c0 c1 c2
  rw [raw23_eta A]
  generalize A 0 0 = a at *
  generalize A 0 1 = b at *
  generalize A 0 2 = c at *
  generalize A 1 0 = d at *
  generalize A 1 1 = e at *
  generalize A 1 2 = f at *
  obtain rfl : d = 2 - a := by omega
  obtain rfl : e = 2 - b := by omega
  obtain rfl : c = 3 - a - b := by omega
  obtain rfl : f = 1 - (3 - a - b) := by omega
  have ha : a ≤ 2 := by omega
  have hb : b ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;> first | omega | decide

theorem ex32_mem : ∀ A ∈ ex32Mats, rowSum A = ![3, 2] ∧ colSum A = ![2, 2, 1] := by decide

theorem ex32_nodup : ex32Mats.Nodup := by decide

/-- A `{0,1}`-matrix. -/
def zeroOne (A : Raw 2 3) : Bool := decide (∀ i j, A i j ≤ 1)

/-- Example 3.2: per matrix, whether it is a `{0,1}`-matrix, its SW–NE count, and its cable
exponent `Σ C(a,2)`. -/
theorem ex32_table :
    ex32Mats.map (fun A => (zeroOne A, crossing A, EKDualBases.cable A)) =
      [(false, 0, 1), (false, 2, 2), (false, 2, 1), (true, 3, 0), (false, 6, 2)] := by
  decide

/-- The printed cable exponents of the `M″` column. -/
def ex32PrintedCable : List ℕ :=
  [Nat.choose 3 2, Nat.choose 3 2 + Nat.choose 3 2, Nat.choose 3 2, 0,
    Nat.choose 3 2 + Nat.choose 3 2]

theorem ex32_printed_cable_exponents_differ :
    ex32Mats.map EKDualBases.cable ≠ ex32PrintedCable := by decide

theorem ex32_printed_cable_signs :
    (ex32Mats.zip ex32PrintedCable).map (fun p => (-1 : ℤ) ^ (crossing p.1 + p.2)) =
      ex32Mats.map (fun A => (-1 : ℤ) ^ (crossing A + EKDualBases.cable A)) := by decide

/-- The three contribution columns and their sums: `M = −1`, `M′ = 3`, `M″ = −1`. -/
theorem ex32_column_sums :
    ex32Mats.map (fun A => if zeroOne A then (-1 : ℤ) ^ crossing A else 0) = [0, 0, 0, -1, 0] ∧
    ex32Mats.map (fun A => (-1 : ℤ) ^ crossing A) = [1, 1, 1, -1, 1] ∧
    ex32Mats.map (fun A => (-1 : ℤ) ^ (crossing A + EKDualBases.cable A)) = [-1, 1, -1, -1, 1] ∧
    (ex32Mats.map (fun A => if zeroOne A then (-1 : ℤ) ^ crossing A else 0)).sum =
      EKDualBases.M 5 EKRest.shape32 EKRest.shape221 ∧
    (ex32Mats.map (fun A => (-1 : ℤ) ^ crossing A)).sum =
      EKDualBases.Mh 5 EKRest.shape32 EKRest.shape221 ∧
    (ex32Mats.map (fun A => (-1 : ℤ) ^ (crossing A + EKDualBases.cable A))).sum =
      EKDualBases.Me 5 EKRest.shape32 EKRest.shape221 := by
  obtain ⟨h1, h2, h3⟩ := EKRest.example_3_2
  rw [h1, h2, h3]
  decide

/-! ## p. 25: `p₆` -/

section PSix
open EKComplete EKNondegeneracy EKRest

private theorem pairing_hL_hL_fast (l l' : List ℕ) :
    quotientPairing (hL l) (hL l') = fastH l l' := by
  have e : ∀ m : List ℕ, hL m = (m.map (col false)).prod := fun m => by
    rw [hL]; congr 2
  rw [e, e, pairing_const, fastH]

private theorem pair_hL_comb_fast (l : List ℕ) (c : List (ℤ × List ℕ)) :
    quotientPairing (hL l) (comb c) = (c.map fun t => t.1 * fastH l t.2).sum := by
  induction c with
  | nil => simp [comb]
  | cons t c ih =>
    simp only [comb, List.map_cons, List.sum_cons, map_add, map_zsmul, smul_eq_mul] at ih ⊢
    rw [ih, pairing_hL_hL_fast]

/-- The printed expansion of `p₆` ([EK] p. 25). -/
def P6 : List (ℤ × List ℕ) :=
  [(1, [1, 1, 1, 1, 1, 1]), (3, [2, 2, 1, 1]), (-3, [3, 3]), (-6, [4, 1, 1]), (6, [5, 1])]

/-- [EK] p. 25: `p₆ = m₆ = h₁₁₁₁₁₁ + 3h₂₂₁₁ − 3h₃₃ − 6h₄₁₁ + 6h₅₁`, as printed. -/
theorem p_six : EKCenterPower.p 6 = comb P6 := by
  refine eq_of_pair_hL (p_mem 6) (comb_mem 6 P6 (by decide)) fun l hl => ?_
  have hshape : ∀ l ∈ partsF 6 6 6, l.Sorted (· ≥ ·) ∧ ∀ x ∈ l, 0 < x := by decide
  have hval : ∀ l ∈ partsF 6 6 6,
      (P6.map fun t => t.1 * fastH l t.2).sum = if l = [6] then 1 else 0 := by decide +kernel
  rw [pair_hL_comb_fast, hval l hl, pair_hL_p (by decide) l (hshape l hl).1 (hshape l hl).2]

end PSix

/-! ## Examples 3.5 and 3.6 -/

section Signs
open TableauSign TableauDominance TableauRowWord OddLRExamples EKSchurOrthonormalControls

/-- Explicit tableaux of Example 3.5. -/
def T35a : PositiveTableau y221 :=
  posTab [[1, 2], [3, 4], [5]] (by decide) 3 2 (by decide) (by decide) (by decide) (by decide)
def T35b : PositiveTableau y221 :=
  posTab [[1, 2], [3, 5], [4]] (by decide) 3 2 (by decide) (by decide) (by decide) (by decide)
def T35c : PositiveTableau y221 :=
  posTab [[1, 3], [2, 4], [5]] (by decide) 3 2 (by decide) (by decide) (by decide) (by decide)
def T35d : PositiveTableau y221 :=
  posTab [[1, 3], [2, 5], [4]] (by decide) 3 2 (by decide) (by decide) (by decide) (by decide)
def T35e : PositiveTableau y221 :=
  posTab [[1, 4], [2, 5], [3]] (by decide) 3 2 (by decide) (by decide) (by decide) (by decide)

theorem ex35_rowWords :
    [rowWord T35a, rowWord T35b, rowWord T35c, rowWord T35d, rowWord T35e] =
      [[5, 3, 4, 1, 2], [4, 3, 5, 1, 2], [5, 2, 4, 1, 3], [4, 2, 5, 1, 3], [3, 2, 5, 1, 4]] := by
  simp only [T35a, T35b, T35c, T35d, T35e, rowWord_posTab]
  decide

/-- Example 3.5: the printed signs `+ − − + −`. -/
theorem ex35_signs :
    [tableauSign T35a, tableauSign T35b, tableauSign T35c, tableauSign T35d, tableauSign T35e] =
      [1, -1, -1, 1, -1] := by
  have h := ex35_rowWords
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨ha, hb, hc, hd, he⟩ := h
  simp only [tableauSign, ha, hb, hc, hd, he]
  decide

/-- Example 3.5: these five row words are all the valid fillings of `(2,2,1)` by `1,…,5`. -/
theorem ex35_words :
    words (rowCells y221) ((rowCells y11111).map (fun p => p.1 + 1)) =
      [rowWord T35a, rowWord T35b, rowWord T35c, rowWord T35d, rowWord T35e].toFinset := by
  rw [ex35_rowWords, y221_cells, y11111_cells]
  decide

/-- Example 3.5: `K_{(2,2,1),(1⁵)} = sign(T_{(2,2,1)}) Σ_T sign(T) = 1 · (1 − 1 − 1 + 1 − 1)`. -/
theorem ex35_kostka :
    signedKostka y221 y11111 = tableauSign (canonicalTableau y221) *
      [tableauSign T35a, tableauSign T35b, tableauSign T35c, tableauSign T35d,
        tableauSign T35e].sum ∧ signedKostka y221 y11111 = -1 := by
  rw [ex35_signs, example_3_5.1, example_3_5.2]
  decide

/-- Explicit tableaux of Example 3.6. -/
def T36a : PositiveTableau y311 :=
  posTab [[1, 1, 2], [3], [4]] (by decide) 3 3 (by decide) (by decide) (by decide) (by decide)
def T36b : PositiveTableau y311 :=
  posTab [[1, 1, 3], [2], [4]] (by decide) 3 3 (by decide) (by decide) (by decide) (by decide)
def T36c : PositiveTableau y311 :=
  posTab [[1, 1, 4], [2], [3]] (by decide) 3 3 (by decide) (by decide) (by decide) (by decide)

theorem ex36_rowWords :
    [rowWord T36a, rowWord T36b, rowWord T36c] =
      [[4, 3, 1, 1, 2], [4, 2, 1, 1, 3], [3, 2, 1, 1, 4]] := by
  simp only [T36a, T36b, T36c, rowWord_posTab]
  decide

/-- Example 3.6: the printed signs `− + −`. -/
theorem ex36_signs : [tableauSign T36a, tableauSign T36b, tableauSign T36c] = [-1, 1, -1] := by
  have h := ex36_rowWords
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨ha, hb, hc⟩ := h
  simp only [tableauSign, ha, hb, hc]
  decide

/-- Example 3.6: these three row words are all the valid fillings of `(3,1,1)` with content
`(2,1,1,1)`. -/
theorem ex36_words :
    words (rowCells y311) ((rowCells y2111).map (fun p => p.1 + 1)) =
      [rowWord T36a, rowWord T36b, rowWord T36c].toFinset := by
  rw [ex36_rowWords, y311_cells, y2111_cells]
  decide

/-- Example 3.6: `K_{(3,1,1),(2,1,1,1)} = sign(T_{(3,1,1)}) Σ_T sign(T) = −1 · (−1 + 1 − 1) = 1`. -/
theorem ex36_kostka :
    signedKostka y311 y2111 = tableauSign (canonicalTableau y311) *
      [tableauSign T36a, tableauSign T36b, tableauSign T36c].sum ∧
      signedKostka y311 y2111 = 1 := by
  rw [ex36_signs, example_3_6.1, example_3_6.2]
  decide

end Signs

end OddMath.Frontier.EKMore
