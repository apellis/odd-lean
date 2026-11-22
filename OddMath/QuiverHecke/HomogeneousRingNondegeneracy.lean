/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.TruncatedReesNondegeneracy

/-! # The conjecture for homogeneous parameters over commutative rings, directly

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, for homogeneous parameters (1.31) and a symmetrizable Cartan
superdatum.

`nondegeneracy_of_symmetrizer` reaches commutative rings with `2` invertible from
characteristic-zero fields (`SKM.nondegeneracyConjecture_of_charZeroField`). The swapped vacuum
route itself only uses the parameters through the two inputs of the supported action
(`SectorActionInputs`), and for homogeneous parameters these hold over every commutative ring
(`sectorActionInputs_of_homogeneous`). This file applies the route directly over the ring.

## Main results

* `nondegeneracy_of_homogeneous_commRing`: the Nondegeneracy Conjecture for homogeneous scalars
  over a commutative ring, by `nondegeneracy_of_sectorActionInputs`, without passing through
  fields. It adds no condition on `2` beyond the one in `SKM.Scalars` (BE2 §1: `2` is a unit
  when some colour is odd), so for purely even data it holds over every commutative ring.
  Colours, weights and the ring lie in one universe, as for the swapped route;
  `nondegeneracy_of_symmetrizer` allows a ring in any universe, with `2` invertible.
-/

namespace OddMath.QuiverHecke

universe u

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X}

/-- **The Nondegeneracy Conjecture for homogeneous parameters over a commutative ring**
(Brundan–Ellis, arXiv:1701.04133v2, §8): for a symmetrizable Cartan superdatum, homogeneous
scalars over a commutative ring `K` and every normalization `cs`, the chosen matching families
are bases. Proved by the swapped vacuum route over `K` itself
(`nondegeneracy_of_sectorActionInputs`), not by reduction to fields. -/
theorem nondegeneracy_of_homogeneous_commRing (sy : SKM.Symmetrizer D) {K : Type u} [CommRing K]
    {Sc : SKM.Scalars D K} (hh : Sc.Homogeneous) (cs : SKM.CScalars Sc) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_sectorActionInputs (sectorActionInputs_of_homogeneous sy hh) cs

end OddMath.QuiverHecke
