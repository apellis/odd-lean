/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Square
import OddMath.QuiverHecke.CyclotomicAction.CrossingTransformation

/-!
# Mixed quadratic comparison on cyclotomic composition corners

Ports the algebraic comparison input of
`Categorification/KLR/CyclotomicAction/MixedComparison.lean` and the quadratic
calculation of `Categorification/KLR/CyclotomicAction/Square.lean`.
The quotient element on the right is the explicit polynomial in the two
positioned dots, not a freely specified square. Signed right multiplication
introduces the super-opposite sign. This is an upward quadratic comparison;
it does not assert the mixed induction–restriction Mackey isomorphism.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The explicit two-colour quadratic polynomial evaluated in a word endomorphism ring. -/
def wordQuadratic (i j : I) (t : List I) (r : ℕ) : End ((pres D Sc).obj (ob D t)) :=
  if D.d i j = 0 then (Sc.t i j : k) • 1 else
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      Sc.s i j p q • (dotE D Sc t r ^ p * dotE D Sc t (r + 1) ^ q) +
      ((Sc.t i j : k) • dotE D Sc t r ^ D.dn i j +
        (Sc.t j i : k) • dotE D Sc t (r + 1) ^ D.dn j i)

variable [Fintype I]

/-- Sum the displayed quadratic polynomial over the old-word corners. -/
def affinePairQuadratic (i j : I) (n : ℕ) : Hn D Sc (n + 1 + 1) :=
  ∑ w : Word I n, FiniteHomMatrix.single (appendWord j (appendWord i w))
    (appendWord j (appendWord i w))
    (wordQuadratic D Sc i j (appendWord j (appendWord i w)).1 w.1.length)

end OddMath.QuiverHecke
