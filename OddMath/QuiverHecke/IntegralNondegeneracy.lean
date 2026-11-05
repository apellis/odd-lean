/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteSwappedRightNegative
import OddMath.SKM.IntegralNondegeneracy

/-! # Nondegeneracy of the integral form

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, for the integral form of the presentation (Definition 1.5 with the
integral relations imposed when `2` is not a unit), in the research scope of
`FieldScopeBoundary.md`.

* `integral_nondegeneracy_of_symmetrizer`: the conjecture for a symmetrizable Cartan superdatum
  and homogeneous parameters over every commutative ring, with no condition on `2`. It is
  `nondegeneracy_of_symmetrizer` over the universal parameter ring with `2` inverted, transported
  by `SKM.IntegralNondegeneracy.nondegeneracyConjecture_of_universal`.
-/

namespace OddMath.QuiverHecke

universe u w

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X}

/-- **The Nondegeneracy Conjecture for the integral form** (Brundan–Ellis, arXiv:1701.04133v2,
§8) for a symmetrizable Cartan superdatum and homogeneous parameters over every commutative ring.
The scalars carry no condition on `2`. -/
theorem integral_nondegeneracy_of_symmetrizer (sy : SKM.Symmetrizer D) {k : Type w}
    [CommRing k] {Sc : SKM.IntegralScalars D k} (hh : Sc.Homogeneous)
    (cs : SKM.CScalars Sc) : SKM.NondegeneracyConjecture cs :=
  SKM.IntegralNondegeneracy.nondegeneracyConjecture_of_universal
    (nondegeneracy_of_symmetrizer sy (SKM.UniversalPolynomialParameters.two_isUnit D)
      (SKM.UniversalPolynomialParameters.homogeneous D)
      (SKM.UniversalPolynomialParameters.normalizations D)) hh cs

end OddMath.QuiverHecke
