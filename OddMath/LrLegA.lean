import OddMath.SkewSign

/-!
# LR Leg A: the per-tableau sign identity behind `s^K = s^p`

Paper: Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1.
Leg A is the first half of the proof of Theorem 3.8, eq. (3.9)
(`s^K_lam = s^p_lam = s^s_lam`): expanding the complete product
`h_mu = h_{mu_1} ... h_{mu_r}` as an odd-plactic signed sum and regrouping
by shape gives
  `h_mu = sum_lam sum_{T in SSYT(lam,mu)} (-1)^{NE(lam)+NE^<(T)} s^p_lam`,
while the Kostka expansion is `h_mu = sum_lam K_{lam,mu} s^K_lam`; since
both `{h_mu}` and `{s^K_lam}` are integral bases (Prop 2.3, eqs (2.8)-(2.9)),
it suffices to check the per-tableau sign identity
  `(-1)^{NE(lam)+NE^<(T)} = (-1)^{N(lam)+N^<(T)}`.

Box-count conventions (paper Sec 2.2, "Boxterpretations"): rows grow
downward (English diagrams), columns grow rightward. `North` is strict
(row above); `East` is strict (column right); a `^<` decoration counts
only boxes whose entry is strictly smaller than the reference box;
a count evaluated on a tableau sums over all boxes. Signs:
`sign(T) = (-1)^{N^<(T)}` for a tableau, `sign(T_lam) = (-1)^{N(lam)}`
for the row-reading tableau.

What this module proves (sorry-free):
- `perBox`: for one reference box `B`, if every North-but-not-NE box has
  a strictly smaller entry (the consequence of semistandardness the paper
  uses: "those Northwest are ignored by the left-hand sign, but the entry
  of such a box is necessarily less than that of B, so the right-hand
  sign is +1"), then
  `N + N^< = (NE + NE^<) + 2 * R` where `R` counts the non-NE North boxes.
- `global`: the summed identity over a box list (take `Bs = T` for the
  full tableau totals).
- `perBox_sign` / `global_sign`: the `(-1)`-power form of both.
- Grounding counters `countDirectNorth` / `countEastGt` / `countSouthWest`
  reproducing the paper's worked Example 2.4 values
  (dN = 16, E^> = 28, sW = 47); see the fixture suite.

Scope (NOT this module): the h-expansion regrouping (A1), the integral-basis
uniqueness step (A2, needs Prop 2.3), semistandard tableaux and Ferrers
shapes (the `Semistandard => per-box hypothesis` bridge is an obligation
of the Leg B successor), and the full `s^K = s^p` equality. Finite fixture
values are development aids (`SUPPORTED_LOW_DEGREE` at most), never a proof
of the published theorem.

Convention authority: the sign convention (increasing-index canonical
order, Koszul reorder signs; English Ferrers coordinates). This module
imports `OddMath.SkewSign` for the shared core-algebra prelude only
(`pow_succ`, `mul_assoc`, `mul_one` are not in bare Lean core); there is
no mathematical dependence on skew signs, and the axiom audit must still
show only the standard triple with no `sorryAx`.
-/

namespace OddMath.LrLegA

/-- A tableau box: 0-indexed English coordinates (rows grow downward,
columns grow rightward) with an entry in the positive alphabet. -/
structure TBox where
  row : Nat
  col : Nat
  entry : Nat

/-- A tableau is an explicit finite list of boxes. -/
abbrev Tableau := List TBox

/-- Strict North: `A` sits in a row above `B`'s row (paper Sec 2.2). -/
def isNorth (A B : TBox) : Bool := decide (A.row < B.row)

/-- Strict East: `A` sits in a column right of `B`'s column. -/
def isEast (A B : TBox) : Bool := decide (B.col < A.col)

/-- Strict West: `A` sits in a column left of `B`'s column. -/
def isWest (A B : TBox) : Bool := decide (A.col < B.col)

/-- Same column (neither East nor West): the `dN` (directly North) case. -/
def isSameCol (A B : TBox) : Bool := A.col == B.col

/-- South-or-same row (non-strict South): the `sW` row condition. -/
def isSouthOrSame (A B : TBox) : Bool := decide (B.row ≤ A.row)

/-- Strictly smaller entry than the reference box (`^<` decoration). -/
def isLtEntry (A B : TBox) : Bool := decide (A.entry < B.entry)

/-- Strictly greater entry than the reference box (`^>` decoration). -/
def isGtEntry (A B : TBox) : Bool := decide (B.entry < A.entry)

/-- N(B): boxes of `T` strictly North of `B`. -/
def countNorth : Tableau → TBox → Nat
  | [], _ => 0
  | A :: T, B => (if isNorth A B then 1 else 0) + countNorth T B

/-- NE(B): boxes of `T` strictly North and strictly East of `B`. -/
def countNE : Tableau → TBox → Nat
  | [], _ => 0
  | A :: T, B =>
      (if isNorth A B then (if isEast A B then 1 else 0) else 0) + countNE T B

/-- N^<(B): North boxes with strictly smaller entry. -/
def countNorthLt : Tableau → TBox → Nat
  | [], _ => 0
  | A :: T, B =>
      (if isNorth A B then (if isLtEntry A B then 1 else 0) else 0)
        + countNorthLt T B

/-- NE^<(B): North-East boxes with strictly smaller entry. -/
def countNELt : Tableau → TBox → Nat
  | [], _ => 0
  | A :: T, B =>
      (if isNorth A B then
        (if isEast A B then (if isLtEntry A B then 1 else 0) else 0)
       else 0) + countNELt T B

/-- R(B): North boxes that are NOT strictly East (the NW boxes plus the
same-column North boxes). The paper's argument ignores exactly these on
the left-hand side. -/
def countRest : Tableau → TBox → Nat
  | [], _ => 0
  | A :: T, B =>
      (if isNorth A B then (if isEast A B then 0 else 1) else 0)
        + countRest T B

/-- dN(B): directly-North boxes (North, same column). Grounding counter. -/
def countDirectNorth : Tableau → TBox → Nat
  | [], _ => 0
  | A :: T, B =>
      (if isNorth A B then (if isSameCol A B then 1 else 0) else 0)
        + countDirectNorth T B

/-- E^>(B): East boxes with strictly greater entry. Grounding counter. -/
def countEastGt : Tableau → TBox → Nat
  | [], _ => 0
  | A :: T, B =>
      (if isEast A B then (if isGtEntry A B then 1 else 0) else 0)
        + countEastGt T B

/-- sW(B): south-or-same-row and strictly-West boxes. Grounding counter. -/
def countSouthWest : Tableau → TBox → Nat
  | [], _ => 0
  | A :: T, B =>
      (if isSouthOrSame A B then (if isWest A B then 1 else 0) else 0)
        + countSouthWest T B

/-- Total of a per-box count over a box list. -/
def totalNorth (T : Tableau) : Tableau → Nat
  | [] => 0
  | B :: Bs => countNorth T B + totalNorth T Bs

/-- Total of the NE count over a box list. -/
def totalNE (T : Tableau) : Tableau → Nat
  | [] => 0
  | B :: Bs => countNE T B + totalNE T Bs

/-- Total of the N^< count over a box list. -/
def totalNorthLt (T : Tableau) : Tableau → Nat
  | [] => 0
  | B :: Bs => countNorthLt T B + totalNorthLt T Bs

/-- Total of the NE^< count over a box list. -/
def totalNELt (T : Tableau) : Tableau → Nat
  | [] => 0
  | B :: Bs => countNELt T B + totalNELt T Bs

/-- Total of the non-NE North count over a box list. -/
def totalRest (T : Tableau) : Tableau → Nat
  | [] => 0
  | B :: Bs => countRest T B + totalRest T Bs

/-- Total of the directly-North count (grounding). -/
def totalDirectNorth (T : Tableau) : Tableau → Nat
  | [] => 0
  | B :: Bs => countDirectNorth T B + totalDirectNorth T Bs

/-- Total of the E^> count (grounding). -/
def totalEastGt (T : Tableau) : Tableau → Nat
  | [] => 0
  | B :: Bs => countEastGt T B + totalEastGt T Bs

/-- Total of the sW count (grounding). -/
def totalSouthWest (T : Tableau) : Tableau → Nat
  | [] => 0
  | B :: Bs => countSouthWest T B + totalSouthWest T Bs

/-- Left-hand Leg A sign: `(-1)^{NE+NE^<}` (the plactic h-expansion side). -/
def signLeft (T Bs : Tableau) : Int :=
  (-1 : Int) ^ (totalNE T Bs + totalNELt T Bs)

/-- Right-hand Leg A sign: `(-1)^{N+N^<}` (the Kostka side). -/
def signRight (T Bs : Tableau) : Int :=
  (-1 : Int) ^ (totalNorth T Bs + totalNorthLt T Bs)

/-- Helper: a `Bool` that is not `true` is `false`. -/
theorem bool_false_of_not_true {b : Bool} (h : ¬ b = true) :
    b = false := by
  cases hb : b with
  | true => exact absurd hb h
  | false => rfl

/-- Per-box Leg A parity identity (the paper's per-box argument).
For a fixed box `B`, the North boxes split into NE boxes (counted by both
sides) and non-NE North boxes (counted twice on the right: once in `N`
and once in `N^<`, using the hypothesis). Hence the two exponents differ
by exactly `2 * R`. -/
theorem perBox (T : Tableau) (B : TBox) :
    (∀ A ∈ T, isNorth A B = true → isEast A B = false →
      isLtEntry A B = true) →
    countNorth T B + countNorthLt T B
      = countNE T B + countNELt T B + 2 * countRest T B := by
  induction T with
  | nil => intro _; rfl
  | cons A T ih =>
      intro H
      have Hmem : A ∈ A :: T := by simp
      have Ht : ∀ A' ∈ T, isNorth A' B = true → isEast A' B = false →
          isLtEntry A' B = true := by
        intro A' hA' hN hE
        exact H A' ((List.mem_cons).mpr (Or.inr hA')) hN hE
      have tail := ih Ht
      simp only [countNorth, countNE, countNorthLt, countNELt, countRest]
      by_cases hN : isNorth A B = true
      · by_cases hE : isEast A B = true
        · by_cases hL : isLtEntry A B = true
          · simp only [hN, hE, hL, if_true, if_false, Bool.false_eq_true]
            omega
          · simp only [hN, hE, hL, if_true, if_false, Bool.false_eq_true]
            omega
        · have hEf : isEast A B = false := bool_false_of_not_true hE
          have hL : isLtEntry A B = true := H A Hmem hN hEf
          simp only [hN, hE, hL, if_true, if_false, Bool.false_eq_true]
          omega
      · simp only [hN, if_true, if_false, Bool.false_eq_true]
        omega

/-- Summed Leg A parity identity over a box list (take `Bs = T`). -/
theorem global (T Bs : Tableau) :
    (∀ B ∈ Bs, ∀ A ∈ T, isNorth A B = true → isEast A B = false →
      isLtEntry A B = true) →
    totalNorth T Bs + totalNorthLt T Bs
      = totalNE T Bs + totalNELt T Bs + 2 * totalRest T Bs := by
  induction Bs with
  | nil => intro _; rfl
  | cons B Bs ih =>
      intro H
      have Hmem : B ∈ B :: Bs := by simp
      have HB : ∀ A ∈ T, isNorth A B = true → isEast A B = false →
          isLtEntry A B = true := H B Hmem
      have Htail : ∀ B' ∈ Bs, ∀ A ∈ T, isNorth A B' = true →
          isEast A B' = false → isLtEntry A B' = true := by
        intro B' hB' A hN hE hL
        exact H B' ((List.mem_cons).mpr (Or.inr hB')) A hN hE hL
      have hPB := perBox T B HB
      have hIH := ih Htail
      simp only [totalNorth, totalNE, totalNorthLt, totalNELt, totalRest]
      omega

/-- `(-1)^2 = 1` over the integers, by evaluation. -/
theorem neg_one_sq : (-1 : Int) ^ 2 = 1 := by decide

/-- Adding 2 to an exponent does not change `(-1)^·`. -/
theorem neg_one_pow_add_two (m : Nat) : (-1 : Int) ^ (m + 2) = (-1 : Int) ^ m := by
  have h1 : m + 2 = (m + 1) + 1 := by omega
  have h2 : (-1 : Int) * -1 = 1 := by decide
  rw [h1, pow_succ, pow_succ, mul_assoc, h2, mul_one]

/-- Equal-up-to-an-even-number exponents give equal `(-1)` powers. -/
theorem sign_of_eq_add_two_mul (x y K : Nat) (h : x = y + 2 * K) :
    (-1 : Int) ^ x = (-1 : Int) ^ y := by
  subst h
  induction K generalizing y with
  | zero => simp
  | succ K ih =>
      have e : y + 2 * (K + 1) = (y + 2 * K) + 2 := by omega
      rw [e, neg_one_pow_add_two]
      exact ih y

/-- Per-box sign identity in `(-1)`-power form. -/
theorem perBox_sign (T : Tableau) (B : TBox)
    (H : ∀ A ∈ T, isNorth A B = true → isEast A B = false →
      isLtEntry A B = true) :
    (-1 : Int) ^ (countNE T B + countNELt T B)
      = (-1 : Int) ^ (countNorth T B + countNorthLt T B) := by
  exact (sign_of_eq_add_two_mul _ _ _ (perBox T B H)).symm

/-- Global Leg A sign identity: `(-1)^{NE+NE^<} = (-1)^{N+N^<}`. -/
theorem global_sign (T Bs : Tableau)
    (H : ∀ B ∈ Bs, ∀ A ∈ T, isNorth A B = true → isEast A B = false →
      isLtEntry A B = true) :
    signLeft T Bs = signRight T Bs := by
  show (-1 : Int) ^ (totalNE T Bs + totalNELt T Bs)
    = (-1 : Int) ^ (totalNorth T Bs + totalNorthLt T Bs)
  exact (sign_of_eq_add_two_mul _ _ _ (global T Bs H)).symm

end OddMath.LrLegA
