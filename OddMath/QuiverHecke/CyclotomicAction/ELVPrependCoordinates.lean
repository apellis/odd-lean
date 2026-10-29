/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldBalancedTensor
import OddMath.QuiverHecke.PrependBasis
import OddMath.QuiverHecke.HomDimension
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# ELV coefficient normalization of prepend PBW coordinates

The affine input PBW basis underlying KKO I, arXiv:1206.5933v2,
Lemma 8.1 (p. 39), extended to the coefficient algebra of
`DeformedGlobalQP.md` §1. The extension to exterior coefficients is not
attributed to KKO. The existing `PrependIdx`, `prependBasis`, and
`ELVOld.balancedEquiv` are used throughout.

`prependAffineEquiv` is a proved affine coordinate equivalence, without
flatness. `balancedEquiv_prependExpansion` compares its normalized finite
expansion with the old-only quotient. Each coefficient is first twisted by
the moving tail parity, then the entire old morphism is twisted by the
balance parity. Neither twist can be discarded for exterior coefficients.

The expansion is surjective, not asserted injective: its indices still
include old normal forms. Regrouping those indices into old quotient Hom
coefficients, with a proved inverse, remains necessary for moving-dot
cancellation. No moving cyclotomic polynomial is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Affine input PBW coordinates with the full ELV coefficient algebra. -/
def prependAffineEquiv (i : I) (v w : List I) :
    hom D Sc cutoff (i :: v) w ≃ₗ[k]
      (PrependIdx i v w →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  (TensorProduct.congr (LinearEquiv.refl k _)
    (prependBasis D Sc (i := i) (s := v) (t := w)).repr).trans
      (TensorProduct.finsuppScalarRight k k _ _)

@[simp] theorem prependAffineEquiv_tmul (i : I) (v w : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (f : (pres D Sc).obj (ob D (i :: v)) ⟶ (pres D Sc).obj (ob D w))
    (x : PrependIdx i v w) :
    prependAffineEquiv D Sc cutoff i v w (a ⊗ₜ[k] f) x =
      (prependBasis D Sc).repr f x • a := by
  change TensorProduct.finsuppScalarRight k k _ _
    ((TensorProduct.congr (LinearEquiv.refl k _) (prependBasis D Sc).repr) (a ⊗ₜ[k] f)) x = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.finsuppScalarRight_apply_tmul_apply]

@[simp] theorem prependAffineEquiv_symm_single {i : I} {v w : List I}
    (x : PrependIdx i v w) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (prependAffineEquiv D Sc cutoff i v w).symm (Finsupp.single x a) =
      a ⊗ₜ[k] prependElt D Sc x := by
  change (TensorProduct.congr (LinearEquiv.refl k _) (prependBasis D Sc).repr).symm
    ((TensorProduct.finsuppScalarRight k k _ _).symm (Finsupp.single x a)) = _
  rw [TensorProduct.finsuppScalarRight_symm_apply_single, TensorProduct.congr_symm_tmul]
  simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply, Module.Basis.repr_symm_single,
    one_smul, prependBasis_apply]

/-- New dots and moving crossings, with no old normal form or coefficient. -/
def prependTail {i : I} {v w : List I} (x : PrependIdx i v w) :
    (pres D Sc).obj (ob D (i :: x.oldTarget)) ⟶ (pres D Sc).obj (ob D w) :=
  cl D Sc _ _ (((List.replicate x.1.1 0).map PG.dot) ++
    cw (Categorification.TypeA.canWord (v.length + 1) x.1.2.2.2.1⁻¹))
    (by simpa only [tgt_append, tgt_map_dot, x.moving_target] using
      sChain_pl (i :: x.oldTarget) (((List.replicate x.1.1 0).map PG.dot) ++
        cw (Categorification.TypeA.canWord (v.length + 1) x.1.2.2.2.1⁻¹)))

/-- The existing input-side basis has old-first categorical orientation. -/
theorem prependElt_insert_tail {i : I} {v w : List I} (x : PrependIdx i v w) :
    prependElt D Sc x = affineInsert D Sc i v x.oldTarget x.old.nf ≫
      prependTail D Sc x := by
  rw [prependElt_eq_comp, cl_comp]
  rfl

/-- Parity of the new dots and moving crossings, excluding the old block. -/
def prependTailParity {i : I} {v w : List I} (x : PrependIdx i v w) : ZMod 2 :=
  ((pl (i :: x.oldTarget) (((List.replicate x.1.1 0).map PG.dot) ++
    cw (Categorification.TypeA.canWord (v.length + 1) x.1.2.2.2.1⁻¹))).map
      fun z => z.2.1.parity D).sum

theorem prependTail_mem {i : I} {v w : List I} (x : PrependIdx i v w) :
    prependTail D Sc x ∈ parity (R := k) _ _ (prependTailParity D x) :=
  Presentation.diag_mem_homDeg' (degree_parity_mkD D _ _)

/-- Moving a homogeneous coefficient into the old block retains its Koszul sign. -/
theorem prepend_insert_coefficient {i : I} {v w : List I} (x : PrependIdx i v w)
    {q : ZMod 2} (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff q) :
    insert D Sc cutoff i v x.oldTarget (a ⊗ₜ[k] x.old.nf) ≫
      (((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) :
        hom D Sc cutoff (i :: x.oldTarget) w) =
      koszulSign q (prependTailParity D x) • (a ⊗ₜ[k] prependElt D Sc x) := by
  rw [insert_tmul]
  change BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
    (Y := obj D Sc cutoff (i :: x.oldTarget)) (SuperalgebraCat.ofElem a) _ ≫
    BoxProd.tmulHom (X := obj D Sc cutoff (i :: x.oldTarget))
    (Y := obj D Sc cutoff w) (SuperalgebraCat.ofElem 1) _ = _
  rw [BoxProd.tmulHom_comp_tmulHom ha _ (SuperalgebraCat.ofElem 1)
    (prependTail_mem D Sc x)]
  change koszulSign q (prependTailParity D x) •
    ((1 * a) ⊗ₜ[k] (affineInsert D Sc i v x.oldTarget x.old.nf ≫ prependTail D Sc x)) = _
  rw [one_mul, ← prependElt_insert_tail]

/-- The signed old block is transferred through the proved balanced equivalence. -/
theorem balancedEquiv_prepend_coefficient (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) {q : ZMod 2}
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff q) :
    balancedEquiv D Sc cutoff p i v w
      (balancedTmul D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x)
        ((ideal D Sc cutoff v x.oldTarget).mkQ (twist k p (a ⊗ₜ[k] x.old.nf)))) =
      koszulSign q (prependTailParity D x) •
        projection D Sc cutoff i v w
          ((prependAffineEquiv D Sc cutoff i v w).symm (Finsupp.single x a)) := by
  rw [balancedEquiv_tmul, twist_twist, prepend_insert_coefficient D Sc cutoff x a ha,
    map_zsmul, prependAffineEquiv_symm_single]

/-- Coefficient parity involution, distinct from total parity on old Homs. -/
def coefficientTwist (r : ZMod 2) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff :=
  twist k r (X := SuperalgebraCat.star (SKM.SYM.elvCoefficientParity (k := k) D cutoff))
    (Y := SuperalgebraCat.star (SKM.SYM.elvCoefficientParity (k := k) D cutoff))

/-- Source-order normalization works for arbitrary, not only homogeneous, coefficients. -/
theorem prepend_insert_twisted_coefficient {i : I} {v w : List I}
    (x : PrependIdx i v w) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    insert D Sc cutoff i v x.oldTarget
        (coefficientTwist D cutoff (prependTailParity D x) a ⊗ₜ[k] x.old.nf) ≫
      (((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) :
        hom D Sc cutoff (i :: x.oldTarget) w) = a ⊗ₜ[k] prependElt D Sc x := by
  induction a using DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff) with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Limits.zero_comp]
  | add a b ha hb =>
    simp only [map_add, TensorProduct.add_tmul, Preadditive.add_comp, ha, hb]
  | @homogeneous q a =>
    have ht : coefficientTwist D cutoff (prependTailParity D x) a =
        sign k (prependTailParity D x * q) • (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
      twist_of_mem _ a.property
    rw [ht, ← TensorProduct.smul_tmul', map_smul, Linear.smul_comp,
      prepend_insert_coefficient D Sc cutoff x a a.property, koszulSign_smul (R := k),
      mul_comm q, sign_smul_sign_smul]

/-- The full old coefficient, first normalized across the tail and then twisted in total parity. -/
def prependOldCoefficient (p : ZMod 2) {i : I} {v w : List I} (x : PrependIdx i v w) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k] Old D Sc cutoff v x.oldTarget :=
  (ideal D Sc cutoff v x.oldTarget).mkQ.comp
    ((twist k p).comp
      (((TensorProduct.mk k _ _).flip x.old.nf).comp
        (coefficientTwist D cutoff (prependTailParity D x))))

/-- One normalized PBW term in the existing signed coend. -/
def prependBalancedTerm (p : ZMod 2) {i : I} {v w : List I} (x : PrependIdx i v w) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k] BalancedTensor D Sc cutoff p i v w :=
  (balanceRelations D Sc cutoff p i v w).mkQ.comp
    ((DirectSum.lof k (List I) _ x.oldTarget).comp
      (((TensorProduct.mk k _ _)
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x)).comp
          (prependOldCoefficient D Sc cutoff p x)))

theorem balancedEquiv_prependBalancedTerm (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    balancedEquiv D Sc cutoff p i v w (prependBalancedTerm D Sc cutoff p x a) =
      projection D Sc cutoff i v w (a ⊗ₜ[k] prependElt D Sc x) := by
  change balancedEquiv D Sc cutoff p i v w
    (balancedTmul D Sc cutoff p i _ ((ideal D Sc cutoff v x.oldTarget).mkQ
      (twist k p (coefficientTwist D cutoff (prependTailParity D x) a ⊗ₜ[k] x.old.nf)))) = _
  rw [balancedEquiv_tmul, twist_twist, prepend_insert_twisted_coefficient]

/-- Finite normalized PBW expansion into the proved balanced tensor, not a replacement tensor. -/
def prependBalancedExpansion (p : ZMod 2) (i : I) (v w : List I) :
    (PrependIdx i v w →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) →ₗ[k]
      BalancedTensor D Sc cutoff p i v w :=
  Finsupp.lsum k (prependBalancedTerm D Sc cutoff p)

@[simp] theorem prependBalancedExpansion_single (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    prependBalancedExpansion D Sc cutoff p i v w (Finsupp.single x a) =
      prependBalancedTerm D Sc cutoff p x a := Finsupp.lsum_single _ _ _ _

/-- Comparison of affine PBW coordinates with the old-only quotient through `balancedEquiv`. -/
theorem balancedEquiv_prependExpansion (p : ZMod 2) (i : I) (v w : List I)
    (f : PrependIdx i v w →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    balancedEquiv D Sc cutoff p i v w (prependBalancedExpansion D Sc cutoff p i v w f) =
      projection D Sc cutoff i v w ((prependAffineEquiv D Sc cutoff i v w).symm f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x a =>
    rw [prependBalancedExpansion_single, balancedEquiv_prependBalancedTerm,
      prependAffineEquiv_symm_single]

/-- Every balanced class has a normalized finite PBW expansion with old coefficients. -/
theorem prependBalancedExpansion_surjective (p : ZMod 2) (i : I) (v w : List I) :
    Function.Surjective (prependBalancedExpansion D Sc cutoff p i v w) := by
  intro z
  obtain ⟨h, hh⟩ := projection_surjective D Sc cutoff i v w
    (balancedEquiv D Sc cutoff p i v w z)
  refine ⟨prependAffineEquiv D Sc cutoff i v w h, ?_⟩
  apply (balancedEquiv D Sc cutoff p i v w).injective
  rw [balancedEquiv_prependExpansion, LinearEquiv.symm_apply_apply, hh]

/-- The exact kernel remains the old relation span; no moving polynomial is imposed. -/
theorem prependBalancedExpansion_eq_zero_iff (p : ZMod 2) (i : I) (v w : List I)
    (f : PrependIdx i v w →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    prependBalancedExpansion D Sc cutoff p i v w f = 0 ↔
      (prependAffineEquiv D Sc cutoff i v w).symm f ∈ relations D Sc cutoff i v w := by
  rw [← (balancedEquiv D Sc cutoff p i v w).map_eq_zero_iff,
    balancedEquiv_prependExpansion, projection_eq_zero_iff]

end OddMath.QuiverHecke.ELVOld
