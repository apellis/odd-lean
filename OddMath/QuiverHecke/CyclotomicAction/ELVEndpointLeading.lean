/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendSignedMovingSupport
import OddMath.QuiverHecke.CyclotomicAction.ELVEndpointPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQPLeading
/-! # Actual endpoint ELV highest coefficient and ordered numerator cancellation

`endpointELV_top` and `endpointELV_above` prove the leading unit and support
bound of the literal finite polynomial for every cutoff and colour. The
leading action retains the full old-Hom parity twist. Direct finite maximal
append support proves its regularity and, with the independently proved
QP factor regularity, `appendProjection_qp_endpointELV_regular` cancels the
actual ordered numerator from `DeformedBoundaryDivision.md` §3.
No injectivity on the final full cyclotomic quotient is used or claimed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def appendCoefficientTerm (i : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (d : ℕ) :
    hom D Sc cutoff (v ++ [i]) (v ++ [i]) :=
  a ⊗ₜ[k] (dotE D Sc (v ++ [i]) v.length ^ d : End _)

theorem append_coefficient_monomial (i : I) (v : List I) (d : ℕ)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    appendCoefficientTerm D Sc cutoff i v a d =
      appendMovingPower D Sc cutoff i v d ≫
        rightContext D Sc cutoff [i] v v (ELVPScalar.scalar D Sc cutoff v a) := by
  rw [ELVPScalar.rightContext_scalar]
  exact (affineUnit_comp_scalar D Sc cutoff (dotE D Sc (v ++ [i]) v.length ^ d) a).symm

end OddMath.QuiverHecke.ELVOld
