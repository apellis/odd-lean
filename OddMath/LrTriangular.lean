import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Uniqueness for finite unitriangular systems

The proof of `s^p = s^s` in Theorem 3.8 of Ellis, "The odd Littlewood-Richardson rule",
arXiv:1111.3932v1, solves a unitriangular system: each equation involves the target shape
and larger shapes that are already solved, with leading coefficient `±1`. This module proves
the uniqueness statement behind that step for an arbitrary finite index type.

Main results:
- `tailSum`: the strictly upper triangular part of a row,
  `∑ j, if i < j then C i j • F j else 0`.
- `RowSystem`: the unitriangular equations `d i • F i + tailSum C F i = rhs i` for every `i`.
- `unique`: two families satisfying the same system (the same `±1` leads `d`, the same
  coefficient matrix `C`, the same right-hand side `rhs`) coincide. The proof is strong
  backward induction from the top index: the tail at `i` involves only indices `j > i`, the
  shared rows give `d i • P i = d i • S i`, and the `±1` lead cancels.

In the paper, `n` is the number of shapes, `M` is the ring of odd symmetric functions,
`d` and `C` are the signs of the e-right Pieri rule (3.10), `rhs` are elementary products,
and `P`, `S` are the families `s^p`, `s^s`; that instantiation is not formalized here.
Theorem 3.8 is proved in `OddMath.Frontier.OddLRThm38`.
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
  rw [ite_eq_right (by omega)]

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
