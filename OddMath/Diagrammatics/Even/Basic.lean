import Mathlib.Logic.Equiv.Basic

/-!
# Even permutation diagrams: typed AST and endpoint semantics

Typed even-permutation diagram calculus per the fixed design (sections 2-4 of the
unpublished design notes): objects are strand counts, `swap k i` is the adjacent
permutation crossing on slots `i, i+1` (zero-based; Lean index 0 = paper
strand 1), and `seq below above` is vertical composition with chronological
order — `below` applied first, target above (EKL product direction).

This is the symmetric-group calculus, NOT the odd nilHecke calculus: equal
adjacent crossings cancel to the identity (proved in `Cancellation.lean`),
whereas the odd crossing satisfies `dᵢ² = 0` (R-2.07A / R-3.05, an explicit
non-goal of this module). No dot, thick-strand (`R-3.11`), or 0-Hecke
(`R-3.16`) constructors appear here.
-/
namespace OddMath.Diagrammatics.Even

/-- Typed even-permutation diagram terms. `swap k i` lives on `k+2` strands
with `i : Fin (k+1)` the zero-based left slot (`i ≤ k`, i.e. the schema
bound `left ≤ rank-2`). Ill-typed gluings such as `seq (id 2) (id 3)` are
rejected by the kernel: `Expr.seq` requires a shared middle boundary. -/
inductive Expr : Nat → Nat → Type where
  | id : (n : Nat) → Expr n n
  | swap : (k : Nat) → Fin (k + 1) → Expr (k + 2) (k + 2)
  | seq : {a b c : Nat} → Expr a b → Expr b c → Expr a c
  deriving DecidableEq

/-- Adjacent transposition on `k+2` strands, swapping slots `i` and `i+1`. -/
def adjacent (k : Nat) (i : Fin (k + 1)) : Equiv.Perm (Fin (k + 2)) :=
  Equiv.swap i.castSucc i.succ

/-- Endpoint (permutation) semantics: the symmetric-group representation.
`seq below above` denotes `Equiv.trans` in chronological order. -/
def denote : {a b : Nat} → Expr a b → (Fin a ≃ Fin b)
  | _, _, .id n => Equiv.refl _
  | _, _, .swap k i => adjacent k i
  | _, _, .seq below above => (denote below).trans (denote above)

/-- A single adjacent swap moves its left endpoint. -/
theorem adjacent_moves_left (k : Nat) (i : Fin (k + 1)) :
    adjacent k i i.castSucc = i.succ :=
  Equiv.swap_apply_left _ _

end OddMath.Diagrammatics.Even
