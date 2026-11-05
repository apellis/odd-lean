/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerGrading
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetDot

/-!
# Graded right-dot square for the moving-strand map

The polynomial-variable portion of KKO I, arXiv:1206.5933v2,
Proposition 8.4: the existing right dots have degree `D.parity i` on
`qSourceSpace` and `qTargetSpace`, and the even map Q intertwines them.
The coefficient involution is retained, including on the shifted target.
These are graded right operators, not assertions of signed left-superlinearity.
No full right-superalgebra action, QP identity, or local inversion is concluded.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

end OddMath.QuiverHecke
