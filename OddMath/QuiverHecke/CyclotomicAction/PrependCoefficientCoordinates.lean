/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.PrependTensorCoordinates
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightCoefficient

/-!
# Shifted cyclotomic prepend coordinates

The balanced extension (9)–(10) of `PrependCoordinates.md` for the prescribed
shifted coefficient. The equivalence is additive, and right coefficient
compatibility is proved separately using the commuting twisted left action.
Polynomial parity, rather than even polynomial support, is required.
No cancellation, grading on the tensor, or full QP identity is asserted.
-/

noncomputable section
open Categorification
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (r : ℕ)
local notation "C" => InductionAlong.Corner (prependAlgebra D Sc i (r+1) :
  Hn D Sc (r+1) →ₙ+* Hn D Sc (r+1+1))
local notation "T" => InductionAlong.Ind (StringDiagrams.SuperBimodule.toSVec (qCoefficient D Sc i β a ha r)) (prependAlgebra D Sc i (r+1) :
  Hn D Sc (r+1) →ₙ+* Hn D Sc (r+1+1))

end OddMath.QuiverHecke
