import OddMath.SkewSign

/-!
# LR Leg B: Pieri-induction skeleton (`s^p = s^s`, Theorem 3.8 second half)

Paper: Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1,
Theorem 3.8 proof, paper lines 508-520 (snapshot
an unpublished note).
Design: an unpublished note, §4 Leg B.

What this module proves (sorry-free):
- (B3) Partition combinatorics for the induction measure: `width`,
  `transpose` (`lam^T_j = #{i : lam_i > j}`), lexicographic `lexGe`, and the
  vertical-strip predicate `isVertStrip` (the e-right Pieri rule (3.10) sums
  over `mu` obtained from `lam` by adding a vertical strip). The paper
  inducts on width, and within a width lexicographically on `lam^T`.
- (B3) The single-box NE sign model `addedSignExp`/`addedSign` following the
  paper's own proof gloss ("The sign (-1)^{|i|lam|} counts boxes NorthEast
  of the new box", Prop 3.7 proof): boxes strictly North of the added box
  and strictly East of its column.
- (B4) The triangular solve: `solve_one`/`solve_two`/`solve_three`. The paper
  argues both families satisfy `s_{(lam^T_1)} ... s_{(lam^T_r)} = sum_mu ± s_mu`
  with each `mu` of width `<= r`, lexicographically `>= lam`, leading
  coefficient `±1`, and -- crucially -- the SAME signs `±` for both
  families (this sameness is what the B2 transfer buys); hence both equal the
  same expression in the elementary functions. These theorems are that solve
  step at one/two/three-shape depth with explicit shared signs and shared
  elementary products: same matrix, same right-hand side `=>` same solution.

Scope (NOT this module, recorded as hypotheses, never asserted):
- (B1) The column base case `lam = (1^k)` (Lemma 3.5, eq (3.5)) is the shared
  `Prod` input both families agree on -- modeled here as the hypothesis that
  both families share each `Prod`, verified only on finite fixtures.
- (B2) The psi1-psi2 transfer of the h-right plactic Pieri rule (3.8) to the
  e-right form (3.10) with the same signs as the s^s rule (3.7) is the
  hypothesis that both families share each coefficient matrix entry
  (`d` leads, `c`/`e`/`a`/`b` signs). The paper asserts it in one sentence;
  its sign-preservation content is an obligation of a successor, not proved here.
- No `s^K`/`s^p`/`s^s` definitions (non-tautology guard: the three Schur
  objects stay independent in `formal-statements/lr-theorem38.lean`, untouched
  here), no Lemma 3.5/Prop 3.6/Prop 3.7 statements, no Theorem 3.8 comparison.
  Finite fixtures in `OddMath/Tests/LrLegBFixtures.lean` are development aids
  (`SUPPORTED_LOW_DEGREE` at most), never a proof of the published theorem.

Conventions: English Ferrers coordinates (rows down, columns right) per
the sign convention, matching the Leg A module `OddMath.LrLegA`.
Imports `OddMath.SkewSign` for the shared core-algebra prelude only
(documented here; no mathematical dependence -- same pattern as Leg A,
since bare core lacks generic `mul_assoc`/`mul_one`).
-/

namespace OddMath.LrLegB

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
The B3 outer induction is on this quantity. -/
def width : Partition → Nat
  | [] => 0
  | l :: _ => l

/-- Transpose: `lam^T_j` counts rows strictly longer than `j`.
The B3 inner induction is lexicographic on this list. -/
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
  | cons l ls ih => simp [isVertStrip, Nat.le_refl, Nat.le_succ, ih]

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

/-- A `±1`-lead equation determines its unknown (the B4 leading-`±1`
cancellation the paper invokes when solving for each `s_lam`). -/
theorem solve_head (d p s : Int) (hlead : d = 1 ∨ d = -1)
    (h : d * p = d * s) : p = s := by
  have h2 : d * (d * p) = d * (d * s) := by rw [h]
  rw [lead_cancel d p hlead, lead_cancel d s hlead] at h2
  exact h2

/-- B4 top shape: same `±1` lead and same elementary product determine
the top (lexicographically largest, successor-free) value for both families. -/
theorem solve_one (d P S Prod : Int) (hlead : d = 1 ∨ d = -1)
    (hP : d * P = Prod) (hS : d * S = Prod) : P = S :=
  solve_head d P S hlead (by rw [hP, hS])

/-- B4 two-shape chain: the top value is pinned by `solve_one`, then the lower
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

/-- B4 three-shape chain (the full paper pattern: leading `±1` at every
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

end OddMath.LrLegB
