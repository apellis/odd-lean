import OddMath.LrLegA

/-! Hand-derived LR Leg A fixtures, written BEFORE the module exists (TDD red step).

Paper: Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1.
Leg A (Thm 3.8 proof, first half): the h-expansion sign identity
  (-1)^{NE(lam)+NE^<(T)} = (-1)^{N(lam)+N^<(T)}
for every tableau T (all counts per paper Sec 2.2 boxterpretations:
North = strictly above row; East = strictly right column; ^< = entry
strictly smaller than the reference box; totals sum over all boxes).

Values below are hand-derived in an unpublished script (exact Python model
of the Sec 2.2 counting rules) BEFORE any Lean is written:
- F1 single box: all totals 0.
- F2 row (2), entries [1,1]: no North boxes anywhere; N = NE = 0.
- F3 column (1^2), entries [1],[2]: bottom box sees N=1, NE=0, N^<=1,
  NE^<=0 (the Lemma 3.5 column micro-instance: exponents 0 vs 2).
- F4 shape (2,1), rows [1,1],[2]: bottom box N=2, NE=1, N^<=2, NE^<=1.
- F5 paper Example 2.4, rows [1,1,2,2],[2,3,3,4],[3,4,4],[5,6]:
  grounding totals dN=16, E^>=28, sW=47 (paper p.8, exact match required);
  Leg A totals NE+NE^< = 55, N+N^< = 117 (diff 62, even), both signs -1.
This file MUST fail to elaborate until `OddMath.LrLegA` exists.
-/
namespace OddMath.LrLegA.Tests

open OddMath.LrLegA

/- Kernel reduction depth: the F5 closed checks unfold 13x13 box
comparisons plus `(-1)^117`; that exceeds the default limit of 512. -/
set_option maxRecDepth 10000

/-- F1: a single box sees nothing North of itself. -/
def exSingle : Tableau := [⟨0, 0, 1⟩]

/-- F2: row shape (2) with weakly increasing entries; no North boxes. -/
def exRow2 : Tableau := [⟨0, 0, 1⟩, ⟨0, 1, 1⟩]

/-- F3: column shape (1^2); the Lemma 3.5 column micro-instance. -/
def exCol2 : Tableau := [⟨0, 0, 1⟩, ⟨1, 0, 2⟩]

/-- F4: shape (2,1) with rows [1,1],[2]. -/
def exShape21 : Tableau := [⟨0, 0, 1⟩, ⟨0, 1, 1⟩, ⟨1, 0, 2⟩]

/-- F5: paper Example 2.4 (Sec 2.2), rows [1,1,2,2],[2,3,3,4],[3,4,4],[5,6]. -/
def exEllis24 : Tableau :=
  [⟨0, 0, 1⟩, ⟨0, 1, 1⟩, ⟨0, 2, 2⟩, ⟨0, 3, 2⟩,
   ⟨1, 0, 2⟩, ⟨1, 1, 3⟩, ⟨1, 2, 3⟩, ⟨1, 3, 4⟩,
   ⟨2, 0, 3⟩, ⟨2, 1, 4⟩, ⟨2, 2, 4⟩,
   ⟨3, 0, 5⟩, ⟨3, 1, 6⟩]

-- F1: all totals vanish.
example : totalNorth exSingle exSingle = 0 := by decide
example : totalNE exSingle exSingle = 0 := by decide
example : signLeft exSingle exSingle = 1 := by decide
example : signRight exSingle exSingle = 1 := by decide

-- F2: a one-row tableau has no North boxes at all.
example : totalNorth exRow2 exRow2 = 0 := by decide
example : totalNE exRow2 exRow2 = 0 := by decide
example : totalNorthLt exRow2 exRow2 = 0 := by decide
example : totalNELt exRow2 exRow2 = 0 := by decide

-- F3: column micro-instance; exponents 0 (left) vs 2 (right), same sign.
example : totalNorth exCol2 exCol2 = 1 := by decide
example : totalNE exCol2 exCol2 = 0 := by decide
example : totalNorthLt exCol2 exCol2 = 1 := by decide
example : totalNELt exCol2 exCol2 = 0 := by decide
example : signLeft exCol2 exCol2 = 1 := by decide
example : signRight exCol2 exCol2 = 1 := by decide

-- F4: shape (2,1); bottom box contributes N=2, NE=1, N^<=2, NE^<=1.
example : totalNorth exShape21 exShape21 = 2 := by decide
example : totalNE exShape21 exShape21 = 1 := by decide
example : totalNorthLt exShape21 exShape21 = 2 := by decide
example : totalNELt exShape21 exShape21 = 1 := by decide
example : signLeft exShape21 exShape21 = 1 := by decide
example : signRight exShape21 exShape21 = 1 := by decide

-- F5 grounding: the paper's worked values dN=16, E^>=28, sW=47.
example : totalDirectNorth exEllis24 exEllis24 = 16 := by decide
example : totalEastGt exEllis24 exEllis24 = 28 := by decide
example : totalSouthWest exEllis24 exEllis24 = 47 := by decide

-- F5 Leg A totals: NE+NE^< = 55, N+N^< = 117; both signs -1.
example : totalNE exEllis24 exEllis24 = 31 := by decide
example : totalNELt exEllis24 exEllis24 = 24 := by decide
example : totalNorth exEllis24 exEllis24 = 62 := by decide
example : totalNorthLt exEllis24 exEllis24 = 55 := by decide
example : signLeft exEllis24 exEllis24 = -1 := by decide
example : signRight exEllis24 exEllis24 = -1 := by decide

/-- F5 hypothesis: every non-NE North box has a strictly smaller entry
(the semistandard consequence the paper's per-box argument uses). -/
example : ∀ B ∈ exEllis24, ∀ A ∈ exEllis24,
    isNorth A B = true → isEast A B = false → isLtEntry A B = true := by
  decide

/-- F5 end-to-end: the universal theorem applied to paper data. -/
example : signLeft exEllis24 exEllis24 = signRight exEllis24 exEllis24 :=
  global_sign exEllis24 exEllis24 (by decide)

end OddMath.LrLegA.Tests
