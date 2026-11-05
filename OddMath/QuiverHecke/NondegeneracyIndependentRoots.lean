/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteSwappedRightNegative
import OddMath.SKM.CScalarsExistence

/-!
# The Nondegeneracy Conjecture without supplied normalizations

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, Nondegeneracy
Conjecture, with the normalizations `c_{λ;i}` of (1.17).

`nondegeneracy_of_symmetrizer` proves the conjecture for every supplied `cs : CScalars Sc`. When
the simple roots are linearly independent over `ℤ` in the weight group (the paper's setting), a
choice of normalizations exists (`CScalars.nonempty_of_linearIndependent`), so the statement is
not vacuous for any homogeneous scalars there. This file records the combined statement.

At parity identically zero the presentation `pres D Sc` is the even Kac–Moody 2-category of
BE2 Definition 1.5 with general scalars `tᵢⱼ`, `sᵢⱼ^{pq}` (every super sign is `1`, and the odd
bubble and `SYM[d]` factors do not occur), so the statement includes even nondegeneracy for
homogeneous scalars over commutative rings with `2` invertible and arbitrary sets of colours.

## Main results

* `exists_nondegeneracy_of_linearIndependent`: for symmetrizable data with `ℤ`-linearly
  independent simple roots, homogeneous scalars and `2` invertible, normalizations exist and the
  conjecture holds for each of them.
-/

namespace OddMath.QuiverHecke

universe u w

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X}

/-- **The conjecture with normalizations constructed**: for a symmetrizable Cartan superdatum
whose simple roots are linearly independent over `ℤ`, homogeneous scalars over a commutative ring
with `2` invertible, normalizations `c_{λ;i}` exist, and the Nondegeneracy Conjecture holds for
every choice of them. -/
theorem exists_nondegeneracy_of_linearIndependent (sy : SKM.Symmetrizer D)
    (hα : LinearIndependent ℤ D.α) {R : Type w} [CommRing R] (h₂ : IsUnit (2 : R))
    {Sc : SKM.Scalars D R} (hh : Sc.Homogeneous) :
    Nonempty (SKM.CScalars Sc) ∧ ∀ cs : SKM.CScalars Sc, SKM.NondegeneracyConjecture cs :=
  ⟨SKM.CScalars.nonempty_of_linearIndependent Sc hα,
    fun cs => nondegeneracy_of_symmetrizer sy h₂ hh cs⟩

end OddMath.QuiverHecke
