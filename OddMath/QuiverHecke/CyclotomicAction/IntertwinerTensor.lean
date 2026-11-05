/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerCorners

/-!
# Balanced tensor descent of the moving-strand element

The underlying left-module map of KKO I, arXiv:1206.5933v2, Proposition 8.4.
We use the existing `InductionAlong.Ind` balanced tensor, not a free tensor.
The parity involution is placed on the right action of the first factor:
`a ⋅ r = a ξ(φ_i^{p(β)}(r))`. Moving this involution to the coefficient
factor gives the action underlying `Π_i^{p(β)} R^Λ(β)`.

`contentQ` descends for every coefficient module, hence also for the
cyclotomic quotient. It is the content-β component in the height algebra;
the other content blocks map to zero. No projectivity or flatness is used.
This module does not supply the parity grading or the signed right `t_i`
action, and therefore does not assert the full superbimodule proposition.
-/

noncomputable section
namespace OddMath.QuiverHecke
open Categorification

variable {I k X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

end OddMath.QuiverHecke
