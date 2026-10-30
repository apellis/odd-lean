/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPrependCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendRelations
import OddMath.QuiverHecke.AppendBasis
import OddMath.QuiverHecke.HomDimension
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Signed ELV append PBW normalization

Input-side append PBW coordinates with the full ELV coefficient algebra.
The coefficient parity twist is retained when moving a coefficient into
its old block. These affine coordinates precede descent through the
append-old relation span; no quotient independence is asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Affine input PBW coordinates with the full ELV coefficient algebra. -/
def appendAffineEquiv (i : I) (v w : List I) :
    hom D Sc cutoff (v ++ [i]) w ≃ₗ[k]
      (AppendIdx i v w →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  (TensorProduct.congr (LinearEquiv.refl k _)
    (appendBasis D Sc (i := i) (s := v) (t := w)).repr).trans
      (TensorProduct.finsuppScalarRight k k _ _)

@[simp] theorem appendAffineEquiv_tmul (i : I) (v w : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (f : (pres D Sc).obj (ob D (v ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (x : AppendIdx i v w) :
    appendAffineEquiv D Sc cutoff i v w (a ⊗ₜ[k] f) x =
      (appendBasis D Sc).repr f x • a := by
  change TensorProduct.finsuppScalarRight k k _ _
    ((TensorProduct.congr (LinearEquiv.refl k _) (appendBasis D Sc).repr) (a ⊗ₜ[k] f)) x = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.finsuppScalarRight_apply_tmul_apply]

@[simp] theorem appendAffineEquiv_symm_single {i : I} {v w : List I}
    (x : AppendIdx i v w) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (appendAffineEquiv D Sc cutoff i v w).symm (Finsupp.single x a) =
      a ⊗ₜ[k] appendElt D Sc x := by
  change (TensorProduct.congr (LinearEquiv.refl k _) (appendBasis D Sc).repr).symm
    ((TensorProduct.finsuppScalarRight k k _ _).symm (Finsupp.single x a)) = _
  rw [TensorProduct.finsuppScalarRight_symm_apply_single, TensorProduct.congr_symm_tmul]
  simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply, Module.Basis.repr_symm_single,
    one_smul, appendBasis_apply]

/-- New dots and moving crossings, with no old normal form or coefficient. -/
def appendTail {i : I} {v w : List I} (x : AppendIdx i v w) :
    (pres D Sc).obj (ob D (x.oldTarget ++ [i])) ⟶ (pres D Sc).obj (ob D w) :=
  cl D Sc _ _ (((List.replicate x.1.1 v.length).map PG.dot) ++
    cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹))
    (by simpa only [tgt_append, tgt_map_dot, x.moving_target] using
      sChain_pl (x.oldTarget ++ [i]) (((List.replicate x.1.1 v.length).map PG.dot) ++
        cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹)))

/-- The existing input-side basis has old-first categorical orientation. -/
theorem appendElt_insert_tail {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendElt D Sc x = affineRightContext D Sc [i] v x.oldTarget x.old.nf ≫
      appendTail D Sc x := by
  rw [appendElt_eq_comp, cl_comp]
  rfl

/-- Parity of the new dots and moving crossings, excluding the old block. -/
def appendTailParity {i : I} {v w : List I} (x : AppendIdx i v w) : ZMod 2 :=
  ((pl (x.oldTarget ++ [i]) (((List.replicate x.1.1 v.length).map PG.dot) ++
    cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹))).map
      fun z => z.2.1.parity D).sum

theorem appendTail_mem {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendTail D Sc x ∈ parity (R := k) _ _ (appendTailParity D x) :=
  Presentation.diag_mem_homDeg' (degree_parity_mkD D _ _)

/-- Moving a homogeneous coefficient into the old block retains its Koszul sign. -/
theorem append_insert_coefficient {i : I} {v w : List I} (x : AppendIdx i v w)
    {q : ZMod 2} (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff q) :
    rightContext D Sc cutoff [i] v x.oldTarget (a ⊗ₜ[k] x.old.nf) ≫
      (((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x) :
        hom D Sc cutoff (x.oldTarget ++ [i]) w) =
      koszulSign q (appendTailParity D x) • (a ⊗ₜ[k] appendElt D Sc x) := by
  rw [rightContext_tmul]
  change BoxProd.tmulHom (X := obj D Sc cutoff (v ++ [i]))
    (Y := obj D Sc cutoff (x.oldTarget ++ [i])) (SuperalgebraCat.ofElem a) _ ≫
    BoxProd.tmulHom (X := obj D Sc cutoff (x.oldTarget ++ [i]))
    (Y := obj D Sc cutoff w) (SuperalgebraCat.ofElem 1) _ = _
  rw [BoxProd.tmulHom_comp_tmulHom ha _ (SuperalgebraCat.ofElem 1)
    (appendTail_mem D Sc x)]
  change koszulSign q (appendTailParity D x) •
    ((1 * a) ⊗ₜ[k] (affineRightContext D Sc [i] v x.oldTarget x.old.nf ≫ appendTail D Sc x)) = _
  rw [one_mul, ← appendElt_insert_tail]

/-- Source-order normalization works for arbitrary, not only homogeneous, coefficients. -/
theorem append_insert_twisted_coefficient {i : I} {v w : List I}
    (x : AppendIdx i v w) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    rightContext D Sc cutoff [i] v x.oldTarget
        (coefficientTwist D cutoff (appendTailParity D x) a ⊗ₜ[k] x.old.nf) ≫
      (((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x) :
        hom D Sc cutoff (x.oldTarget ++ [i]) w) = a ⊗ₜ[k] appendElt D Sc x := by
  induction a using DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff) with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Limits.zero_comp]
  | add a b ha hb =>
    simp only [map_add, TensorProduct.add_tmul, Preadditive.add_comp, ha, hb]
  | @homogeneous q a =>
    have ht : coefficientTwist D cutoff (appendTailParity D x) a =
        sign k (appendTailParity D x * q) • (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
      twist_of_mem _ a.property
    rw [ht, ← TensorProduct.smul_tmul', map_smul, Linear.smul_comp,
      append_insert_coefficient D Sc cutoff x a a.property, koszulSign_smul (R := k),
      mul_comm q, sign_smul_sign_smul]


end OddMath.QuiverHecke.ELVOld
