import OddMath.LrLegB

/-! Hand-derived LR Leg B fixtures, written BEFORE the module exists (TDD red step).

Paper: Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1.
Leg B (Thm 3.8 proof, second half, paper lines 508-520): `s^p = s^s` by
Pieri induction -- (B1) column base case Lemma 3.5, (B2) psi1-psi2 transfer
of the h-right plactic Pieri rule (3.8) to the e-right form (3.10) with the
SAME signs as the s^s rule (3.7), (B3) induction on width then lexicographic
transpose, (B4) triangular solve for both families in terms of elementaries.

Values below are hand-derived from the paper's Sec 3.1-3.2 counting rules
BEFORE any Lean is written:
- F1 partition basics: widths, sizes, `isPartition` accepts/rejects.
- F2 transpose `lam^T_j = #{i : lam_i > j}`: `[]`, `[1]`, `[3]`, `[2,1]`
  (self-conjugate), `[3,1] -> [2,1,1]`, `[2,2]` (self-conjugate).
- F3 vertical strips (`mu` extends `lam` by `<= 1` box per row):
  `[2,1]+[0,1]=[2,2]`, `+ [1,0]=[3,1]`, `+[1,1]=[3,2]` valid;
  `[3,3]` (row 1 gains 2), `[4,1]` (row 0 gains 2), `[2]` (removal),
  `[]->[2]` (a 2-box row is never a vertical strip) invalid.
- F4 NE-sign model (paper proof gloss: "The sign (-1)^{|i|lam|} counts
  boxes NorthEast of the new box"): adding `(1,1)` to `[3,1]` sees the
  `(0,2)` box (exponent 1, sign -1); adding `(1,1)` to `[2,1]` sees
  nothing (exponent 0, sign +1); top-row additions see nothing North.
- F5 triangular solve (B4) end-to-end: shared elementary products and
  shared signs pin both families to the same values (top `2`, mid `3`,
  lower `5` with mixed `±1` signs).
- F6 induction measure (B3): lexicographic comparisons including a
  transpose-then-compare pair that distinguishes `[3,1]` from `[2,2]`.
This file MUST fail to elaborate until `OddMath.LrLegB` exists.
-/

namespace OddMath.LrLegB.Tests

open OddMath.LrLegB

-- F1: partition basics.
example : width ([] : Partition) = 0 := by decide
example : width [2, 1] = 2 := by decide
example : width [3, 1] = 3 := by decide
example : ([2, 1] : Partition).sum = 3 := by decide
example : ([2, 1] : Partition).length = 2 := by decide
example : isPartition ([] : Partition) = true := by decide
example : isPartition [2, 1] = true := by decide
example : isPartition [3, 1] = true := by decide
example : isPartition [1, 3] = false := by decide
example : isPartition [2, 0] = false := by decide

-- F2: transpose values.
example : transpose ([] : Partition) = [] := by decide
example : transpose [1] = [1] := by decide
example : transpose [3] = [1, 1, 1] := by decide
example : transpose [2, 1] = [2, 1] := by decide
example : transpose [3, 1] = [2, 1, 1] := by decide
example : transpose [2, 2] = [2, 2] := by decide

-- F3: vertical strips (valid additions).
example : isVertStrip [2, 1] [2, 2] = true := by decide
example : isVertStrip [2, 1] [3, 1] = true := by decide
example : isVertStrip [2, 1] [3, 2] = true := by decide
example : isVertStrip [2, 1] [2, 1] = true := by decide
example : isVertStrip ([] : Partition) [1, 1] = true := by decide

-- F3: vertical strips (invalid additions).
example : isVertStrip [2, 1] [3, 3] = false := by decide
example : isVertStrip [2, 1] [4, 1] = false := by decide
example : isVertStrip [2, 1] [2] = false := by decide
example : isVertStrip ([] : Partition) [2] = false := by decide

-- F3: strip sizes.
example : stripSize [2, 1] [3, 2] = 2 := by decide
example : stripSize [2, 1] [2, 1] = 0 := by decide
example : stripSize [2, 1] [3, 1] = 1 := by decide

-- F4: NE-sign model values.
example : eastCount 3 1 = 1 := by decide
example : eastCount 2 1 = 0 := by decide
example : addedSignExp [3, 1] 1 1 = 1 := by decide
example : addedSign [3, 1] 1 1 = -1 := by decide
example : addedSignExp [2, 1] 1 1 = 0 := by decide
example : addedSign [2, 1] 1 1 = 1 := by decide
example : addedSignExp [2, 1] 0 2 = 0 := by decide
example : addedSign [2, 1] 0 2 = 1 := by decide

-- F5a: top-shape determination (B4 base): `1 * x = 2` pins `x = 2`.
example : (2 : Int) = 2 :=
  OddMath.LrLegB.solve_one 1 2 2 2 (by decide) (by decide) (by decide)

-- F5b: two-shape chain (B4 step): top `1 * x_1 = 3`, lower `1 * x_0 + 1 * 3 = 8`.
example : (5 : Int) = 5 ∧ (3 : Int) = 3 :=
  OddMath.LrLegB.solve_two 1 1 1 5 3 5 3 8 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- F5c: three-shape chain with mixed signs (B4 full pattern):
-- top `x_2 = 2`, mid `x_1 - x_2 = 1`, lower `x_0 + x_1 - x_2 = 6`.
example : (5 : Int) = 5 ∧ (3 : Int) = 3 ∧ (2 : Int) = 2 :=
  OddMath.LrLegB.solve_three 1 1 1 (-1) 1 (-1) 5 3 2 5 3 2 6 1 2
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- F5d: the empty-strip reflexivity theorem applied to paper data.
example : isVertStrip [2, 1] [2, 1] = true := vertStrip_refl _

-- F6: lexicographic measure comparisons (B3 induction order).
example : lexGe [2, 1] [2, 1] = true := by decide
example : lexGe [3, 1] [2, 2] = true := by decide
example : lexGe [2, 2] [3, 1] = false := by decide
example : lexGe ([] : Partition) ([] : Partition) = true := by decide
example : lexGe [1] ([] : Partition) = true := by decide
example : lexGe ([] : Partition) [1] = false := by decide

-- F6: transpose-then-compare distinguishes `[3,1]` from `[2,2]`.
example : transpose [3, 1] = [2, 1, 1] := by decide
example : transpose [2, 2] = [2, 2] := by decide
example : lexGe (transpose [3, 1]) (transpose [2, 2]) = false := by decide
example : lexGe (transpose [2, 2]) (transpose [3, 1]) = true := by decide

end OddMath.LrLegB.Tests
