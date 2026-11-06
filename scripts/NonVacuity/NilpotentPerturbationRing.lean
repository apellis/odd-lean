import OddMath.Algebra.NilpotentPerturbationRing
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Non-vacuity: nilpotent perturbation in an algebra

Over `ℤ/4` with the ideal `(2)`, whose square is zero, in the noncommutative algebra of
`2 × 2` matrices: `1 + 2M` is a unit for every `M`, and `u² + 2u` is a unit for `u` a unit.
-/

namespace NonVacuity.NilpotentPerturbationRing

open OddMath.Algebra

theorem two_sq : Ideal.span {(2 : ZMod 4)} ^ 2 = ⊥ := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot]
  decide

example (M : Matrix (Fin 2) (Fin 2) (ZMod 4)) : IsUnit (1 + (2 : ZMod 4) • M) :=
  isUnit_add_of_mem_smul_top (Ideal.span {(2 : ZMod 4)}) two_sq isUnit_one
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)

example {u : Matrix (Fin 2) (Fin 2) (ZMod 4)} (hu : IsUnit u) :
    IsUnit (((1 : (ZMod 4)ˣ) : ZMod 4) • u ^ 2 +
      ∑ p ∈ Finset.range 2, (if p = 1 then (2 : ZMod 4) else 0) • u ^ p) :=
  isUnit_smul_pow_add_sum (Ideal.span {(2 : ZMod 4)}) two_sq hu 1 2 _ fun p _ => by
    split_ifs
    · exact Ideal.mem_span_singleton_self _
    · exact Ideal.zero_mem _

end NonVacuity.NilpotentPerturbationRing
