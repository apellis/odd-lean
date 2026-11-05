/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContentTensor

/-!
# Shifted target tensor over the content algebra

For KKO I, arXiv:1206.5933v2, Proposition 8.4, `contentTargetEquiv`
compares the tensor over the unital content algebra with the target content
summand. Its coefficient is a submodule of the existing parity-shifted
coefficient, not a ring. Inclusion and cuts give the two maps.
The downstream map `contentTensorShiftedQ` retains the prescribed representatives.
These are underlying left-module comparisons, not graded identifications.
Finite colours, positive height and polynomial parity remain hypotheses.
-/

noncomputable section
open Categorification MulOpposite
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

/-- The content submodule of the prescribed shifted coefficient. -/
def qContentCoefficient : Submodule (Hn D Sc (n + 1)) (qCoefficient D Sc i β a ha n).toSVec where
  carrier := {b | contentIdempotent D Sc (n + 1) β • b = b}
  zero_mem' := smul_zero _
  add_mem' {b c} hx hy := by
    change _ • (b + c) = b + c
    rw [smul_add, hx, hy]
  smul_mem' r b hb := by
    change contentIdempotent D Sc (n + 1) β • (r • b) = r • b
    rw [← mul_smul, contentIdempotent_central, mul_smul, hb]

/-- Restrict the existing shifted action to the unital content corner. -/
instance qContentCoefficientModule :
    Module (ContentAlgebra D Sc β n) (qContentCoefficient D Sc i β a ha n) where
  smul r b := ⟨r.1 • b.1, (qContentCoefficient D Sc i β a ha n).smul_mem r.1 b.2⟩
  one_smul b := Subtype.ext b.2
  mul_smul r s b := Subtype.ext (mul_smul r.1 s.1 b.1)
  smul_zero r := Subtype.ext (smul_zero r.1)
  smul_add r b c := Subtype.ext (smul_add r.1 b.1 c.1)
  zero_smul b := Subtype.ext (zero_smul _ b.1)
  add_smul r s b := Subtype.ext (add_smul r.1 s.1 b.1)

end OddMath.QuiverHecke
