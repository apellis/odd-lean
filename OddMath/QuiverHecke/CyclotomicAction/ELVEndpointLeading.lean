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

@[simp] theorem appendCoefficientTerm_one (i : I) (v : List I) (d : ℕ) :
    appendCoefficientTerm D Sc cutoff i v 1 d = appendMovingPower D Sc cutoff i v d := rfl

theorem append_coefficient_monomial (i : I) (v : List I) (d : ℕ)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    appendCoefficientTerm D Sc cutoff i v a d =
      appendMovingPower D Sc cutoff i v d ≫
        rightContext D Sc cutoff [i] v v (ELVPScalar.scalar D Sc cutoff v a) := by
  rw [ELVPScalar.rightContext_scalar]
  exact (affineUnit_comp_scalar D Sc cutoff (dotE D Sc (v ++ [i]) v.length ^ d) a).symm

theorem append_coefficient_monomial_above (i : I) (v w : List I) (d : ℕ)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (h : hom D Sc cutoff (v ++ [i]) w) (x : AppendIdx i v w)
    (hbound : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, d + t.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff 0 x
      (appendProjection D Sc cutoff i v w
        (appendCoefficientTerm D Sc cutoff i v a d ≫ h)) = 0 := by
  rw [append_coefficient_monomial, appendMovingPower_rightContext_twist, Category.assoc]
  have H := appendOldSource_signedMovingPower_above D Sc cutoff 0 x d
    (twist k (d • D.parity i) (ELVPScalar.scalar D Sc cutoff v a))
    (appendOldCoordinateEquiv D Sc cutoff 0 i v w (appendProjection D Sc cutoff i v w h)) hbound
  rw [appendOldReconstruct_coordinateEquiv] at H
  exact H

/-- The literal endpoint ELV polynomial has unit leading coefficient.
On arbitrary old coefficients its highest action retains the total parity twist. -/
theorem endpointELV_top (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) (q : AppendIdx.Tail i v w)
    (hmax : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, t.1.1 ≤ q.1.1) :
    appendOldCoordinate D Sc cutoff 0 (q.representative.shift (cutoff i))
      (appendProjection D Sc cutoff i v w (endpointELV D Sc cutoff i v ≫ h)) =
    oldTwist D Sc cutoff (cutoff i • D.parity i) v q.representative.oldTarget
      ((appendOldCoordinateEquiv D Sc cutoff 0 i v w
        (appendProjection D Sc cutoff i v w h)) q) := by
  have hl (j : Fin (cutoff i)) :
      appendOldCoordinate D Sc cutoff 0 (q.representative.shift (cutoff i))
        (appendProjection D Sc cutoff i v w
          (appendCoefficientTerm D Sc cutoff i v (singleCoefficient D cutoff i j.castSucc) j.val ≫ h)) = 0 := by
    apply append_coefficient_monomial_above D Sc cutoff i v w j.val _ h
    intro t ht
    have hh := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change j.val + t.1.1 < cutoff i + q.representative.1.1
    omega
  change appendOldCoordinate D Sc cutoff 0 (q.representative.shift (cutoff i))
    (appendProjection D Sc cutoff i v w
      ((∑ j : Fin (cutoff i + 1), appendCoefficientTerm D Sc cutoff i v
        (singleCoefficient D cutoff i j) j.val) ≫ h)) = _
  rw [Fin.sum_univ_castSucc, Preadditive.add_comp,
    Preadditive.sum_comp, map_add, map_sum, map_add, map_sum]
  simp only [Fin.val_castSucc, hl, Finset.sum_const_zero, zero_add,
    singleCoefficient_top, Fin.val_last, appendCoefficientTerm_one]
  exact signedAppendMovingPower_coordinate D Sc cutoff 0 q (cutoff i)
    (appendProjection D Sc cutoff i v w h)

/-- Direct finite append support proves regularity of the actual endpoint ELV polynomial. -/
theorem appendProjection_endpointELV_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w (endpointELV D Sc cutoff i v ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  let f := appendOldCoordinateEquiv D Sc cutoff 0 i v w
    (appendProjection D Sc cutoff i v w h)
  suffices hf : f = 0 by
    exact (appendOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have he := endpointELV_top D Sc cutoff i v w h q hmax
  rw [hh, map_zero] at he
  have hz : oldTwist D Sc cutoff (cutoff i • D.parity i) v q.representative.oldTarget (f q) = 0 := he.symm
  have H := congrArg (oldTwist D Sc cutoff (cutoff i • D.parity i) v q.representative.oldTarget) hz
  rw [oldTwist_twice, map_zero] at H
  exact (DFinsupp.mem_support_iff.mp hq) H
/-- The literal polynomial never produces support above cutoff plus input degree. -/
theorem endpointELV_above (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) (x : AppendIdx i v w)
    (hbound : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, cutoff i + t.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff 0 x
      (appendProjection D Sc cutoff i v w (endpointELV D Sc cutoff i v ≫ h)) = 0 := by
  change appendOldCoordinate D Sc cutoff 0 x
    (appendProjection D Sc cutoff i v w
      ((∑ j : Fin (cutoff i + 1), appendCoefficientTerm D Sc cutoff i v
        (singleCoefficient D cutoff i j) j.val) ≫ h)) = 0
  rw [Preadditive.sum_comp, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  apply append_coefficient_monomial_above D Sc cutoff i v w j.val _ h x
  intro t ht
  have hh := hbound t ht
  have hj := j.isLt
  omega

/-- Direct append-side cancellation for the actual ordered reverse numerator.
This uses the concrete top-coefficient proofs for both factors. -/
theorem appendProjection_qp_endpointELV_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
        endpointELV D Sc cutoff i v ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  exact appendProjection_endpointELV_regular D Sc cutoff i v w h
    (appendProjection_qpProduct_regular D Sc cutoff i v w (endpointELV D Sc cutoff i v ≫ h) hh)

end OddMath.QuiverHecke.ELVOld
