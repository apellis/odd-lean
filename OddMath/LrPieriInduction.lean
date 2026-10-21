import OddMath.SkewSign

/-!
# Partition combinatorics and the triangular solve for `s^p = s^s`

Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1, proof of Theorem 3.8: the
equality `s^p = s^s` is proved by induction on the width of `lam` and, within a width,
lexicographically on `lam^T`, using the e-right Pieri rule (3.10), which sums over the `mu`
obtained from `lam` by adding a vertical strip.

Main results:
- `width`, `transpose` (`lam^T_j = #{i : lam_i > j}`), the lexicographic order `lexGe` and
  the vertical-strip predicate `isVertStrip`.
- `addedSignExp` / `addedSign`: the sign of adding one box, counting the boxes strictly
  North of the new box and strictly East of its column (proof of Prop 3.7: "The sign
  (-1)^{|i|lam|} counts boxes NorthEast of the new box").
- `solve_one` / `solve_two` / `solve_three`: the solve step at depth one, two and three.
  Both families satisfy `s_{(lam^T_1)} ... s_{(lam^T_r)} = sum_mu ± s_mu` over `mu` of width
  at most `r`, lexicographically at least `lam`, with leading coefficient `±1` and the same
  signs for both families; with the same matrix and the same right-hand side, the solutions
  agree.

The base case `lam = (1^k)` (Lemma 3.5, eq (3.5)) and the agreement of the coefficient
matrices for the two families (from the involution `psi1 psi2` applied to (3.8)) enter as
hypotheses. The general finite solve is `OddMath.LrTriangular.unique`; Theorem 3.8 is proved
in `OddMath.Frontier.OddLRThm38`. English Ferrers coordinates (rows down, columns right), as
in `OddMath.LrNorthEastSign`; the import of `OddMath.SkewSign` supplies only basic algebraic
lemmas.
-/

namespace OddMath.LrPieriInduction

/-- A partition as a list of row lengths (weakly decreasing, positive;
checked by `isPartition`). -/
abbrev Partition := List Nat

/-- Rows after the first stay weakly below their predecessor and positive. -/
def checkFrom : Nat → Partition → Bool
  | _, [] => true
  | prev, b :: bs => decide (b ≤ prev) && decide (0 < b) && checkFrom b bs

/-- Weakly decreasing positive row lengths. -/
def isPartition : Partition → Bool
  | [] => true
  | a :: rest => decide (0 < a) && checkFrom a rest

/-- Width `lam_1`: first-row length, `0` for the empty partition.
The outer induction of the proof is on this quantity. -/
def width : Partition → Nat
  | [] => 0
  | l :: _ => l

/-- Transpose: `lam^T_j` counts rows strictly longer than `j`.
The inner induction of the proof is lexicographic on this list. -/
def transpose (lam : Partition) : Partition :=
  List.map (fun j => ((lam.filter fun r => decide (j < r)).length))
    (List.range (width lam))

/-- Lexicographic `>=` on row-length lists (shorter list loses on prefix ties;
partitions have no trailing zeros so padding is unambiguous). -/
def lexGe : Partition → Partition → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => true
  | a :: as, b :: bs => if a == b then lexGe as bs else decide (b < a)

/-- `mu` extends `lam` by a vertical strip: coordinate-wise extension with at
most one new box per row (the e-right Pieri rule (3.10) sums over exactly
these `mu`). Missing rows of `lam` count as length `0`. -/
def isVertStrip : Partition → Partition → Bool
  | [], mu => mu.all (fun x => decide (x ≤ 1))
  | _ :: _, [] => false
  | l :: ls, m :: ms => decide (l ≤ m) && decide (m ≤ l + 1) && isVertStrip ls ms

/-- Strip size `|mu| - |lam|` (Pieri rule adds a strip of size `k`). -/
def stripSize (lam mu : Partition) : Nat := mu.sum - lam.sum

/-- Boxes of a row of length `rowLen` strictly East of column `c`. -/
def eastCount (rowLen c : Nat) : Nat := rowLen - (c + 1)

/-- Sign exponent for a box added in `row` at column `newCol`: boxes strictly
North of the added box (earlier rows) and strictly East of its column.
Paper gloss (Prop 3.7 proof): "The sign (-1)^{|i|lam|} counts boxes
NorthEast of the new box". A top-row addition sees nothing North. -/
def addedSignExp : Partition → Nat → Nat → Nat
  | [], _, _ => 0
  | _ :: _, 0, _ => 0
  | r :: rs, row + 1, newCol => eastCount r newCol + addedSignExp rs row newCol

/-- The `(-1)`-power sign of an added box. -/
def addedSign (lam : Partition) (row newCol : Nat) : Int :=
  (-1 : Int) ^ addedSignExp lam row newCol

/-- The empty vertical strip always qualifies. -/
theorem vertStrip_refl (lam : Partition) : isVertStrip lam lam = true := by
  induction lam with
  | nil => rfl
  | cons l ls ih => simp [isVertStrip, Nat.le_succ, ih]

/-- The empty strip adds no boxes. -/
theorem stripSize_self (lam : Partition) : stripSize lam lam = 0 := by
  unfold stripSize
  exact Nat.sub_self _

/-- A top-row addition sees no boxes North of it. -/
theorem addedSignExp_top (r : Nat) (rs : Partition) (c : Nat) :
    addedSignExp (r :: rs) 0 c = 0 := by
  rfl

/-- A `±1` lead squares to `1`. -/
theorem lead_sq (d : Int) (h : d = 1 ∨ d = -1) : d * d = 1 := by
  cases h with
  | inl h1 => simp [h1]
  | inr h2 => simp [h2]

/-- Multiplying by a `±1` lead twice is the identity. -/
theorem lead_cancel (d x : Int) (h : d = 1 ∨ d = -1) : d * (d * x) = x := by
  have hsq : d * d = 1 := lead_sq d h
  calc d * (d * x) = (d * d) * x := by rw [mul_assoc]
    _ = 1 * x := by rw [hsq]
    _ = x := one_mul x

/-- A `±1`-lead equation determines its unknown (the leading-`±1`
cancellation the paper invokes when solving for each `s_lam`). -/
theorem solve_head (d p s : Int) (hlead : d = 1 ∨ d = -1)
    (h : d * p = d * s) : p = s := by
  have h2 : d * (d * p) = d * (d * s) := by rw [h]
  rw [lead_cancel d p hlead, lead_cancel d s hlead] at h2
  exact h2

/-- Top shape: the same `±1` lead and the same elementary product determine
the top (lexicographically largest) value for both families. -/
theorem solve_one (d P S Prod : Int) (hlead : d = 1 ∨ d = -1)
    (hP : d * P = Prod) (hS : d * S = Prod) : P = S :=
  solve_head d P S hlead (by rw [hP, hS])

/-- Two-shape chain: the top value is pinned by `solve_one`, then the lower
equation `d0 * x_0 + c * x_1 = Prod0` -- shared signs `d0, c` and shared
product `Prod0` for both families -- pins the lower value. -/
theorem solve_two (d0 d1 c P0 P1 S0 S1 Prod0 Prod1 : Int)
    (h0 : d0 = 1 ∨ d0 = -1) (h1 : d1 = 1 ∨ d1 = -1)
    (hTopP : d1 * P1 = Prod1) (hTopS : d1 * S1 = Prod1)
    (hLowP : d0 * P0 + c * P1 = Prod0)
    (hLowS : d0 * S0 + c * S1 = Prod0) :
    P0 = S0 ∧ P1 = S1 := by
  have h1eq : P1 = S1 := solve_head d1 P1 S1 h1 (by rw [hTopP, hTopS])
  refine ⟨?_, h1eq⟩
  have hC : c * P1 = c * S1 := by rw [h1eq]
  have hLow : d0 * P0 = d0 * S0 := by omega
  exact solve_head d0 P0 S0 h0 hLow

/-- Three-shape chain (the pattern of the paper: leading `±1` at every
level, each equation seeing only the target and already-solved larger
shapes, identical signs and products for both families). -/
theorem solve_three (d0 d1 d2 e1 a b P0 P1 P2 S0 S1 S2 Prod0 Prod1 Prod2 : Int)
    (h0 : d0 = 1 ∨ d0 = -1) (h1 : d1 = 1 ∨ d1 = -1) (h2 : d2 = 1 ∨ d2 = -1)
    (hTopP : d2 * P2 = Prod2) (hTopS : d2 * S2 = Prod2)
    (hMidP : d1 * P1 + e1 * P2 = Prod1)
    (hMidS : d1 * S1 + e1 * S2 = Prod1)
    (hLowP : d0 * P0 + a * P1 + b * P2 = Prod0)
    (hLowS : d0 * S0 + a * S1 + b * S2 = Prod0) :
    P0 = S0 ∧ P1 = S1 ∧ P2 = S2 := by
  have h2eq : P2 = S2 := solve_head d2 P2 S2 h2 (by rw [hTopP, hTopS])
  have h1eq : P1 = S1 := by
    have he : e1 * P2 = e1 * S2 := by rw [h2eq]
    have hMid : d1 * P1 = d1 * S1 := by omega
    exact solve_head d1 P1 S1 h1 hMid
  have h0eq : P0 = S0 := by
    have ha : a * P1 = a * S1 := by rw [h1eq]
    have hb : b * P2 = b * S2 := by rw [h2eq]
    have hLow : d0 * P0 = d0 * S0 := by omega
    exact solve_head d0 P0 S0 h0 hLow
  exact ⟨h0eq, h1eq, h2eq⟩

end OddMath.LrPieriInduction
