import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# General finite unitriangular uniqueness (`s^p = s^s` solve step, Theorem 3.8)

Paper: Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1,
Theorem 3.8 proof, paper lines 508-520 (snapshot
an unpublished note).
Design: an unpublished note
(the Leg B triangulation argument).

What this module proves (sorry-free):
- `tailSum`: the strictly-upper-triangular tail of one row:
  `∑ j, if i < j then C i j • F j else 0`. Only already-solved larger
  shapes appear, exactly the paper's "each equation seeing only the target
  and already-solved larger shapes" pattern.
- `RowSystem`: one unitriangular row equation
  `d i • F i + tailSum C F i = rhs i` for every `i`.
- `unique`: two families satisfying the same system -- the SAME `±1`
  leads `d`, the SAME coefficient matrix `C`, the SAME right-hand side
  `rhs` (this sameness is what the B2 transfer buys) -- coincide: `P = S`.
  Proof is strong backward induction from the top index down: the tail at
  `i` sees only indices `j > i`, so the induction hypothesis pins every
  tail value, the shared rows then give `d i • P i = d i • S i`, and the
  `±1` lead cancels.

Instantiation note (NOT formalized here): the paper applies this with
`n` = number of transposed column heights, `M` = the odd symmetric
function ring, `d`/`C` = the shared `±` signs from the e-right Pieri rule
(3.10), `rhs` = the shared elementary products, and `P`/`S` = the two
Schur families `s^p`/`s^s`. That instantiation is a successor obligation.

Scope (NOT this module, recorded as hypotheses, never asserted):
- No `s^K`/`s^p`/`s^s` definitions (non-tautology guard: the three Schur
  objects stay independent in `formal-statements/lr-theorem38.lean`,
  untouched here), no Lemma 3.5/Prop 3.6/Prop 3.7 statements, no
  Theorem 3.8 comparison, no psi1-psi2 transfer, no semistandard-tableau
  definitions.
- Finite fixtures in `OddMath/Tests/LrTriangularFixtures.lean` are
  development aids (`SUPPORTED_LOW_DEGREE` at most), never a proof of the
  published theorem.
-/

namespace OddMath.LrTriangular

open scoped BigOperators

variable {n : Nat} {M : Type*} [AddCommGroup M]

/-- Strictly-upper-triangular tail of row `i`: the signed combination of
already-solved larger shapes `F j` for `j > i`. -/
def tailSum (C : Fin n → Fin n → Int) (F : Fin n → M) (i : Fin n) : M :=
  ∑ j : Fin n, if i.val < j.val then C i j • F j else 0

/-- One unitriangular row equation at every index: `±1` lead on the target
plus the strictly-upper tail equals the shared right-hand side. -/
def RowSystem (d : Fin n → Int) (C : Fin n → Fin n → Int) (rhs : Fin n → M)
    (F : Fin n → M) : Prop :=
  ∀ i, d i • F i + tailSum C F i = rhs i

/-- The top row (`i.val + 1 = n`) has an empty tail: no index sits above it. -/
theorem tailSum_top (C : Fin n → Fin n → Int) (F : Fin n → M) (i : Fin n)
    (h : i.val + 1 = n) : tailSum C F i = 0 := by
  unfold tailSum
  apply Finset.sum_eq_zero
  intro j _
  have hlt := j.isLt
  rw [if_neg (by omega)]

/-- Tails agree when all larger shapes agree (each summand is either shared
or off). -/
theorem tail_congr (C : Fin n → Fin n → Int) (F G : Fin n → M) (i : Fin n)
    (h : ∀ j : Fin n, i.val < j.val → F j = G j) :
    tailSum C F i = tailSum C G i := by
  unfold tailSum
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hlt
  · rw [h j hlt]
  · rfl

/-- A `±1` integer lead is cancellable on any additive commutative group:
the lead determines its unknown. -/
theorem smul_cancel (d : Int) (hx : d = 1 ∨ d = -1) (x y : M)
    (h : d • x = d • y) : x = y := by
  cases hx with
  | inl h1 => rw [h1, one_zsmul, one_zsmul] at h; exact h
  | inr h2 => rw [h2, neg_one_zsmul, neg_one_zsmul] at h; exact neg_inj.mp h

/-- General finite unitriangular uniqueness: same `±1` leads, same matrix,
same right-hand side `=>` same solution. Strong backward induction from
the top index: the tail at `i` sees only `j > i`, pinned by the induction
hypothesis, leaving a `±1`-lead equation for the target. -/
theorem unique (d : Fin n → Int) (C : Fin n → Fin n → Int) (rhs : Fin n → M)
    (P S : Fin n → M)
    (hlead : ∀ i, d i = 1 ∨ d i = -1)
    (hP : RowSystem d C rhs P) (hS : RowSystem d C rhs S) :
    P = S := by
  suffices hall : ∀ i : Fin n, P i = S i from funext hall
  suffices key : ∀ k : Nat, ∀ i : Fin n, n - i.val ≤ k → P i = S i from
    fun i => key n i (Nat.sub_le _ _)
  intro k
  induction k with
  | zero =>
    intro i hi
    have hlt := i.isLt
    omega
  | succ k ih =>
    intro i hi
    have htail : ∀ j : Fin n, i.val < j.val → P j = S j := by
      intro j hlt
      exact ih j (by omega)
    have hte : tailSum C P i = tailSum C S i := tail_congr C P S i htail
    have hrowP := hP i
    have hrowS := hS i
    have hds : d i • P i = d i • S i := by
      rw [hte] at hrowP
      exact add_right_cancel (hrowP.trans hrowS.symm)
    exact smul_cancel (d i) (hlead i) (P i) (S i) hds

end OddMath.LrTriangular
