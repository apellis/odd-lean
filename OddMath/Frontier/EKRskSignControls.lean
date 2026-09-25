import OddMath.Frontier.EKPairingMatrices

/-!
# Controls for EK Thm 3.7 (3.8): entrywise sign refinement of odd RSK

EK arXiv:1107.5610v2, p.24 Prop. 3.1(2) (sign of `A` in `M'`: SW-NE pairs),
p.27-28 Thm 3.7 (3.8), Sec. 4.1 (RSK map, p.32), Example 4.5 (p.33), Sec. 4.2 (pp.34-35).

These are compiled BEFORE production.  They use a small, computable, list-based mirror of
the frozen RSK map (book-order two-line array, Schensted row insertion of the column
letters, row letters placed in the new cell) and a list mirror of the tableau sign
(row word read bottom-to-top, left-to-right; strict inversions).  They validate the
printed statement and its conventions; they are NOT the production objects and
are not used by the production proof.

* `examples_4_5`: the four printed matrices of Example 4.5 give exactly the printed pairs.
* `exhaustive_le_four`: for every `n ≤ 4`, all partitions `μ, ρ ⊢ n`, and every
  ℕ-matrix with row sums `μ` and column sums `ρ`, the printed identity holds.
* `variant_without_shape_fails`: dropping the shape term `(-1)^{binom(λ^T,2)}` fails.
* `crossing_agrees_*`: the existing `EKPairingMatrices.crossing` agrees with the list
  mirror on the Example 4.5 matrices (so the mirror measures the existing quantity).
-/

namespace OddMath.Frontier.EKRskSignControls

set_option maxRecDepth 100000

/-- Row insertion of `x` into a tableau given as a list of rows (top row first).
Returns the new tableau and the row index of the new cell. -/
def insertRow (x : ℕ) : List ℕ → Option ℕ × List ℕ
  | [] => (none, [x])
  | y :: ys => if x < y then (some y, x :: ys) else
      let r := insertRow x ys
      (r.1, y :: r.2)

def insertTab (x : ℕ) : List (List ℕ) → List (List ℕ) × ℕ
  | [] => ([[x]], 0)
  | row :: rows =>
    match insertRow x row with
    | (none, row') => (row' :: rows, 0)
    | (some y, row') =>
      let r := insertTab y rows
      (row' :: r.1, r.2 + 1)

/-- Append `u` to row `s` (creating the row if `s` is the length). -/
def placeAt (u : ℕ) : ℕ → List (List ℕ) → List (List ℕ)
  | _, [] => [[u]]
  | 0, row :: rows => (row ++ [u]) :: rows
  | s + 1, row :: rows => row :: placeAt u s rows

/-- Two-line array in book order: row index `i+1`, column index `j+1`, repeated `A i j` times. -/
def twoLine (A : List (List ℕ)) : List (ℕ × ℕ) :=
  (A.zipIdx.map fun (row, i) =>
    (row.zipIdx.map fun (a, j) => List.replicate a (i + 1, j + 1)).flatten).flatten

def rskFrom : List (List ℕ) × List (List ℕ) → List (ℕ × ℕ) → List (List ℕ) × List (List ℕ)
  | st, [] => st
  | (P, Q), (u, v) :: rest =>
    let r := insertTab v P
    rskFrom (r.1, placeAt u r.2 Q) rest

def rsk (A : List (List ℕ)) : List (List ℕ) × List (List ℕ) := rskFrom ([], []) (twoLine A)

def inv : List ℕ → ℕ
  | [] => 0
  | x :: xs => (xs.filter (fun y => y < x)).length + inv xs

def rowWord (T : List (List ℕ)) : List ℕ := T.reverse.flatten

/-- `sum_j binom(λ^T_j, 2) = sum over cells of the (zero-based) row index`. -/
def shapeExp (T : List (List ℕ)) : ℕ := (T.zipIdx.map fun (row, i) => i * row.length).sum

def crossingL (A : List (List ℕ)) : ℕ :=
  let e := (A.zipIdx.map fun (row, i) => row.zipIdx.map fun (a, j) => (i, j, a)).flatten
  (e.map fun (i, j, a) => (e.map fun (k, l, b) => if i < k ∧ l < j then a * b else 0).sum).sum

def printed (A : List (List ℕ)) : Bool :=
  let r := rsk A
  (crossingL A) % 2 == (shapeExp r.1 + inv (rowWord r.1) + inv (rowWord r.2)) % 2

def variantNoShape (A : List (List ℕ)) : Bool :=
  let r := rsk A
  (crossingL A) % 2 == (inv (rowWord r.1) + inv (rowWord r.2)) % 2

/-- Partitions of `n` with parts at most `m` (fuel `f`). -/
def parts : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => []
  | _ + 1, 0, _ => [[]]
  | f + 1, n + 1, m => ((List.range (min (n + 1) m)).map (· + 1)).flatMap fun k =>
      (parts f (n + 1 - k) k).map (k :: ·)

def partitions (n : ℕ) : List (List ℕ) := parts (n + 1) n n

/-- All rows with entries bounded by `cap` summing to `s`. -/
def rowsWith : List ℕ → ℕ → List (List ℕ)
  | [], s => if s = 0 then [[]] else []
  | c :: cs, s => (List.range (min c s + 1)).flatMap fun a =>
      (rowsWith cs (s - a)).map (a :: ·)

def matsWith : List ℕ → List ℕ → List (List (List ℕ))
  | [], cap => if cap.all (· == 0) then [[]] else []
  | m :: ms, cap => (rowsWith cap m).flatMap fun row =>
      (matsWith ms (List.zipWith (· - ·) cap row)).map (row :: ·)

def allMatrices (N : ℕ) : List (List (List ℕ)) :=
  (List.range (N + 1)).flatMap fun n =>
    (partitions n).flatMap fun μ => (partitions n).flatMap fun ρ => matsWith μ ρ

theorem allMatrices_count : (allMatrices 4).length = 133 := by decide +kernel

theorem examples_4_5 :
    rsk [[2,0,0],[0,1,1]] = ([[1,1,2,3]], [[1,1,2,2]]) ∧
    rsk [[1,1,0],[1,0,1]] = ([[1,1,3],[2]], [[1,1,2],[2]]) ∧
    rsk [[1,0,1],[1,1,0]] = ([[1,1,2],[3]], [[1,1,2],[2]]) ∧
    rsk [[0,1,1],[2,0,0]] = ([[1,1],[2,3]], [[1,1],[2,2]]) := by decide +kernel

theorem examples_4_5_signs :
    printed [[2,0,0],[0,1,1]] = true ∧ printed [[1,1,0],[1,0,1]] = true ∧
    printed [[1,0,1],[1,1,0]] = true ∧ printed [[0,1,1],[2,0,0]] = true := by decide +kernel

theorem exhaustive_le_four : (allMatrices 4).all printed = true := by decide +kernel

theorem variant_without_shape_fails : variantNoShape [[0,1],[1,0]] = false := by decide +kernel

theorem variant_without_shape_fails_exhaustive :
    ((allMatrices 4).filter (fun A => !variantNoShape A)).length = 76 := by decide +kernel

/-- The existing SW-NE count agrees with the list mirror on the Example 4.5 matrices. -/
def ex1 : EKPairingMatrices.Raw 2 3 := ![![2,0,0],![0,1,1]]
def ex2 : EKPairingMatrices.Raw 2 3 := ![![1,1,0],![1,0,1]]
def ex3 : EKPairingMatrices.Raw 2 3 := ![![1,0,1],![1,1,0]]
def ex4 : EKPairingMatrices.Raw 2 3 := ![![0,1,1],![2,0,0]]

theorem crossing_agrees_examples :
    EKPairingMatrices.crossing ex1 = crossingL [[2,0,0],[0,1,1]] ∧
    EKPairingMatrices.crossing ex2 = crossingL [[1,1,0],[1,0,1]] ∧
    EKPairingMatrices.crossing ex3 = crossingL [[1,0,1],[1,1,0]] ∧
    EKPairingMatrices.crossing ex4 = crossingL [[0,1,1],[2,0,0]] := by decide +kernel

end OddMath.Frontier.EKRskSignControls
