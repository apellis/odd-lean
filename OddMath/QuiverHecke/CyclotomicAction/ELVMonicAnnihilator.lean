/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMonicPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVEndpointPolynomial

/-! # Actual full-cyclotomic moving-dot annihilator

The concrete monic polynomial evaluates into the full cyclotomic ideal, by
sandwiching the first-position relation between the reverse and moving chains.
Only the scalar parity sign is removed; no chain norm is cancelled. Together
with `ELVMonicOldCoefficients`, this supplies the old-coefficient recurrence
needed for bounded moving-exponent reduction at arbitrary content.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Polynomial
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem endpointNorm_endpointELV_mem_ideal (i : I) (v : List I) :
    affineUnit D Sc cutoff _ _ (endpointNorm D Sc i [] v) ≫ endpointELV D Sc cutoff i v ∈
      ideal D Sc cutoff (v ++ [i]) (v ++ [i]) := by
  have h := comp_ideal D Sc cutoff
    (affineUnit D Sc cutoff _ _ (reverseMoveHom D Sc i [] v))
    (ideal_comp D Sc cutoff (relation_mem D Sc cutoff i v) (move D Sc cutoff i v))
  rw [relation_comp_move, Linear.comp_smul, ← Category.assoc] at h
  change sign k ((cutoff i • D.parity i) * (D.parity i * wordSumParity D v)) •
    ((affineUnit D Sc cutoff _ _ (reverseMoveHom D Sc i [] v) ≫
      affineUnit D Sc cutoff _ _ (moveHom D Sc i [] v)) ≫ endpointELV D Sc cutoff i v) ∈ _ at h
  rw [← affineUnit_comp, reverseMoveHom_comp_moveHom_eq_endpointNorm] at h
  have hh := (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).smul_mem
    (sign k ((cutoff i • D.parity i) * (D.parity i * wordSumParity D v))) h
  simpa only [sign_smul_sign_smul] using hh

theorem affineUnitEndHom_smul (w : List I) (c : k)
    (f : End ((pres D Sc).obj (ob D w))) :
    affineUnitEndHom D Sc cutoff w (c • f) = c • affineUnitEndHom D Sc cutoff w f :=
  (affineUnit D Sc cutoff w w).map_smul c f

theorem monicELVEndpointProduct_eval_mem_ideal (i : I) (v : List I) :
    (monicELVEndpointProduct D Sc cutoff i v).eval₂ (RingHom.id (End (obj D Sc cutoff (v ++ [i]))))
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) ∈
        ideal D Sc cutoff (v ++ [i]) (v ++ [i]) := by
  let f : End (obj D Sc cutoff (v ++ [i])) := endpointELV D Sc cutoff i v
  let n : End ((pres D Sc).obj (ob D (v ++ [i]))) := endpointNorm D Sc i [] v
  let c : k := ((((endpointOldDotEntries D Sc (v ++ [i]) 0 v).map fun z =>
    (endpointNormLeadingUnit D Sc z.1 i)⁻¹).prod : kˣ) : k)
  have he : (monicELVEndpointProduct D Sc cutoff i v).eval₂
      (RingHom.id (End (obj D Sc cutoff (v ++ [i]))))
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) =
      f * affineUnitEndHom D Sc cutoff (v ++ [i]) (c • n) := by
    simpa only [f, n, c, endpointELV, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul] using monicELVEndpointProduct_eval D Sc cutoff i v
  rw [he, affineUnitEndHom_smul, End.mul_def, Linear.smul_comp]
  exact Submodule.smul_mem _ c (endpointNorm_endpointELV_mem_ideal D Sc cutoff i v)

def monicELVEndpointValue (i : I) (v : List I) : End (obj D Sc cutoff (v ++ [i])) :=
  (monicELVEndpointProduct D Sc cutoff i v).eval₂ (RingHom.id _)
    (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length))

/-- A concrete monic polynomial kills the last dot in the full cyclotomic quotient. -/
theorem monicELVEndpointProduct_annihilates (i : I) (v : List I) :
    (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
      (monicELVEndpointValue D Sc cutoff i v) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (monicELVEndpointProduct_eval_mem_ideal D Sc cutoff i v)

end OddMath.QuiverHecke.ELVOld
