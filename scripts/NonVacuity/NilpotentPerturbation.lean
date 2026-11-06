import OddMath.Algebra.NilpotentPerturbation
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Non-vacuity: nilpotent perturbation

`OddMath.Algebra.isIso_add_of_mem_smul` over `ℤ/4` with the ideal `(2)`, whose square is zero:
the identity of `ℤ/4` plus `2` times the identity is an isomorphism.
-/

open CategoryTheory OddMath.Algebra

example : IsIso (𝟙 (ModuleCat.of (ZMod 4) (ZMod 4)) +
    (2 : ZMod 4) • 𝟙 (ModuleCat.of (ZMod 4) (ZMod 4))) :=
  isIso_add_of_mem_smul (Ideal.span {(2 : ZMod 4)}) (N := 2)
    (by rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot]; decide) _
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)
