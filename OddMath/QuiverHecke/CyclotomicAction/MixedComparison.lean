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

variable [Fintype I]

end OddMath.QuiverHecke
