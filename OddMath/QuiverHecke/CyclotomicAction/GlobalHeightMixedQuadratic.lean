/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightMixedSlides
import OddMath.QuiverHecke.CyclotomicAction.MixedComparison
import OddMath.QuiverHecke.CyclotomicAction.AppendCoordinates
import OddMath.QuiverHecke.CyclotomicAction.MoveHomSnoc

/-!
# The distinct-colour quadratic relation on two inductions from every height

The algebra half of the quadratic relations (1.7) of Brundan–Ellis, arXiv:1701.04133v2,
Definition 1.5, for distinct colours, at every height of the extended tower. On the words
`w j i`, the square of the last-pair crossing is the explicit two-colour polynomial
`Q_{ji}` (`affineLastCrossing_mixed`). Writing `A = φᵢ(y_j)` for the appended dot,
`B = y_i` for the new last dot and `e = φᵢφⱼ(1)` for the two-colour idempotent,

  `c_{ij} c_{ji} = e · Q_{ji}(A, B)`

in the affine algebra (`affineLastCrossing_mul_mixed`) and at every height
(`heightLastCrossing_mul_mixed`), where `Q_{ji}(A, B) = t_{ji} 1` if `d_{ji} = 0` and otherwise

  `Q_{ji}(A, B) = ∑_{0<p<d_{ji}, 0<q<d_{ij}} s_{ji}^{pq} A^p B^q + t_{ji} A^{d_{ji}} + t_{ij} B^{d_{ij}}`.

This is an identity of algebra elements; no parameter change is made here.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The explicit two-colour quadratic polynomial in two elements of a `k`-algebra. -/
def pairQuadPoly {R : Type*} [Ring R] [Algebra k R] (i j : I) (A B : R) : R :=
  if D.d i j = 0 then (Sc.t i j : k) • 1 else
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      Sc.s i j p q • (A ^ p * B ^ q) +
      ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

variable [Fintype I]

section PairDiag
variable (i j : I) (n : ℕ)

variable {i j n}

variable (i j n)

private abbrev pairB (w : Word I n) : End (wordObj D Sc (appendWord i (appendWord j w))) :=
  dotE D Sc (appendWord i (appendWord j w)).1 (w.1.length + 1)

variable {i j}

end PairDiag

section Height
open CyclotomicAction
variable (a : I → _root_.Polynomial k) {i j : I}

end Height

end OddMath.QuiverHecke
