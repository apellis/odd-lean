import OddMath.SKM.BWWBoxSums
import Mathlib.Algebra.Module.Submodule.Lattice

/-! # Box sums of Brundan–Wang–Webster coefficients

The coefficient function `c p q = 1` on the box `p ≤ 2`, `q ≤ 1` and the family
`f p q = p` for `q = 0`, `0` otherwise: the box sum equals the corner term `2` plus the pure
terms `0 + 1` modulo the zero submodule, and the corner term alone is wrong by the pure term.
-/

namespace NonVacuity.BWWBoxSums
open OddMath.SKM.BWWBox

/-- The coefficients. -/
def c : ℕ → ℕ → ℤ := fun _ _ => 1

/-- A family supported on the row `q = 0`. -/
def f : ℕ → ℕ → ℤ := fun p q => if q = 0 then (p : ℤ) else 0

example : boxSum c 2 1 f - c 2 0 • f 2 0 - ∑ r ∈ Finset.range 2, c r 0 • f r 0 ∈
    (⊥ : Submodule ℤ ℤ) :=
  boxSum_sub_corner_sub_pure_mem c 2 1 f ⊥ fun p q hq => by
    simp [f, Nat.pos_iff_ne_zero.mp hq]

example : boxSum c 2 1 f = 3 := by decide

example : boxSum c 2 1 (fun p q => if p = 1 ∧ q = 0 then (5 : ℤ) else 0) = c 1 0 • 5 :=
  boxSum_single_pure c 1 (by norm_num) 5

end NonVacuity.BWWBoxSums
