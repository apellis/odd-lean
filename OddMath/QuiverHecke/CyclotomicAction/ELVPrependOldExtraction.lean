/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPrependCoordinates

/-!
# ELV old-Hom extraction from prepend PBW coordinates

The extraction step of `ELVPrependCoordinates.md`, needed for the old-only
coordinate comparison in `DeformedGlobalQP.md` §1. Only the old normal-form
component of the existing `PrependIdx` is replaced; the moving exponent and
inverse shuffle remain unchanged. No finite-colour or flatness assumption is used.

`prependExtractOld_insert_comp_tail` extracts arbitrary full-ELV old
composition. `prependExtractOldQuotient_insert_tail_eq_zero_iff` identifies
the old ideal on a prescribed tail. The coefficient-parity normalization
and total old-Hom parity twist are both retained.

These are affine extraction maps with values in old Homs or their quotient.
Descent on all old-relation generators, simultaneous regrouped coordinate
inversion, moving-square shift, and difference injectivity remain open.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace PrependIdx
variable {i : I} {v w : List I}
/-- Replace only the old normal form, keeping the moving exponent and shuffle. -/
def replaceOld (x : PrependIdx i v w) (y : NFIdx v x.oldTarget) : PrependIdx i v w :=
  ⟨(x.1.1, y.1.1, y.1.2, x.1.2.2.2), y.2.1, y.2.2.1, by
    have he := tgt_shift [i] v (cw (Categorification.TypeA.canWord v.length y.1.2))
    simp only [List.length_singleton, cw_map_shift, List.singleton_append] at he
    simpa only [prependCrossingWord, cw_append, tgt_append, he, y.tgt_cw]
      using x.moving_target⟩

theorem replaceOld_target (x : PrependIdx i v w) (y : NFIdx v x.oldTarget) :
    (x.replaceOld y).oldTarget = x.oldTarget := y.tgt_cw

theorem replaceOld_injective (x : PrependIdx i v w) : Function.Injective x.replaceOld := by
  intro y z h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun a : PrependIdx i v w => a.1.2.1) h)
    (congrArg (fun a : PrependIdx i v w => a.1.2.2.1) h)

end PrependIdx
namespace ELVOld

/-- Full coefficient coordinates on the old affine Hom. -/
def oldAffineEquiv (v t : List I) : hom D Sc cutoff v t ≃ₗ[k]
    (NFIdx v t →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  (TensorProduct.congr (LinearEquiv.refl k _) (basisNF D Sc v t).repr).trans
    (TensorProduct.finsuppScalarRight k k _ _)

@[simp] theorem oldAffineEquiv_symm_single {v t : List I} (y : NFIdx v t)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (oldAffineEquiv D Sc cutoff v t).symm (Finsupp.single y a) = a ⊗ₜ[k] y.nf := by
  change (TensorProduct.congr (LinearEquiv.refl k _) (basisNF D Sc v t).repr).symm
    ((TensorProduct.finsuppScalarRight k k _ _).symm (Finsupp.single y a)) = _
  rw [TensorProduct.finsuppScalarRight_symm_apply_single, TensorProduct.congr_symm_tmul]
  simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply, Module.Basis.repr_symm_single,
    one_smul, basisNF_apply]

/-- Coefficients of a fixed moving tail, with the mandatory coefficient-parity twist. -/
def prependTailCoefficients {i : I} {v w : List I} (x : PrependIdx i v w) :
    (NFIdx v x.oldTarget →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) →ₗ[k]
      (PrependIdx i v w →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  Finsupp.lsum k fun y => (Finsupp.lsingle (x.replaceOld y)).comp
    (coefficientTwist D cutoff (prependTailParity D x))

/-- Replacing the old index leaves the moving diagram unchanged. -/
theorem prependElt_replaceOld {i : I} {v w : List I} (x : PrependIdx i v w)
    (y : NFIdx v x.oldTarget) :
    prependElt D Sc (x.replaceOld y) =
      affineInsert D Sc i v x.oldTarget y.nf ≫ prependTail D Sc x := by
  change _ = ((pres D Sc).obj (ob D [i]) ◁ y.nf) ≫ _
  rw [whiskerLeft_nf]
  simp only [List.singleton_append]
  unfold prependTail prependElt
  rw [cl_comp]
  apply cl_eq_cl
  simp only [PrependIdx.gens, PrependIdx.replaceOld, List.length_singleton, List.map_append,
    dots_map_shift, cw_map_shift, List.append_assoc]

/-- The tail acts on every exterior coefficient by its coefficient-parity involution. -/
theorem insert_nf_tail {i : I} {v w : List I} (x : PrependIdx i v w)
    (y : NFIdx v x.oldTarget)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    insert D Sc cutoff i v x.oldTarget (a ⊗ₜ[k] y.nf) ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w) =
      coefficientTwist D cutoff (prependTailParity D x) a ⊗ₜ[k]
        prependElt D Sc (x.replaceOld y) := by
  induction a using DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff) with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Limits.zero_comp]
  | add a b ha hb =>
    simp only [map_add, TensorProduct.add_tmul, Preadditive.add_comp, ha, hb]
  | @homogeneous q a =>
    have ht : coefficientTwist D cutoff (prependTailParity D x) a =
        sign k (prependTailParity D x * q) • (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
      twist_of_mem _ a.property
    rw [insert_tmul]
    change BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
      (Y := obj D Sc cutoff (i :: x.oldTarget)) (SuperalgebraCat.ofElem a) _ ≫
      BoxProd.tmulHom (X := obj D Sc cutoff (i :: x.oldTarget))
      (Y := obj D Sc cutoff w) (SuperalgebraCat.ofElem 1) _ = _
    rw [BoxProd.tmulHom_comp_tmulHom a.property _ (SuperalgebraCat.ofElem 1)
      (prependTail_mem D Sc x)]
    change koszulSign q (prependTailParity D x) •
      ((1 * (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)) ⊗ₜ[k]
        (affineInsert D Sc i v x.oldTarget y.nf ≫ prependTail D Sc x)) = _
    rw [one_mul, ← prependElt_replaceOld, ht, TensorProduct.smul_tmul',
      koszulSign_smul (R := k), mul_comm q]

/-- Extracting an arbitrary old coefficient followed by a prescribed moving tail. -/
theorem prependAffineEquiv_insert_tail {i : I} {v w : List I} (x : PrependIdx i v w)
    (r : hom D Sc cutoff v x.oldTarget) :
    prependAffineEquiv D Sc cutoff i v w
      (insert D Sc cutoff i v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w)) =
      prependTailCoefficients D cutoff x (oldAffineEquiv D Sc cutoff v x.oldTarget r) := by
  obtain ⟨f, rfl⟩ := (oldAffineEquiv D Sc cutoff v x.oldTarget).symm.surjective r
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Limits.zero_comp]
  | add f g hf hg => simp only [map_add, Preadditive.add_comp, hf, hg]
  | single y a =>
    rw [oldAffineEquiv_symm_single, insert_nf_tail]
    rw [← prependAffineEquiv_symm_single, LinearEquiv.apply_symm_apply]
    rw [← oldAffineEquiv_symm_single, LinearEquiv.apply_symm_apply]
    simp only [prependTailCoefficients, Finsupp.lsum_single, LinearMap.comp_apply,
      Finsupp.lsingle_apply]

/-- Restrict the existing PBW coordinates to one moving tail and regroup the old basis.
The normalization includes total old-Hom parity, not merely coefficient parity. -/
def prependExtractOld (p : ZMod 2) {i : I} {v w : List I} (x : PrependIdx i v w) :
    hom D Sc cutoff (i :: v) w →ₗ[k] hom D Sc cutoff v x.oldTarget :=
  (twist k p).comp ((oldAffineEquiv D Sc cutoff v x.oldTarget).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff (prependTailParity D x))).comp
      ((Finsupp.lcomapDomain x.replaceOld x.replaceOld_injective).comp
        (prependAffineEquiv D Sc cutoff i v w).toLinearMap)))

/-- Actual extraction recovers an arbitrary old Hom coefficient, with its total twist. -/
theorem prependExtractOld_insert_tail (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    prependExtractOld D Sc cutoff p x
      (insert D Sc cutoff i v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w)) = twist k p r := by
  unfold prependExtractOld
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [prependAffineEquiv_insert_tail]
  have hc (f : NFIdx v x.oldTarget →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
      Finsupp.mapRange.linearMap (coefficientTwist D cutoff (prependTailParity D x))
        (Finsupp.lcomapDomain (R := k) x.replaceOld x.replaceOld_injective
          (prependTailCoefficients D cutoff x f)) = f := by
    induction f using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg]
    | single y a =>
      simp only [prependTailCoefficients, Finsupp.lsum_single, LinearMap.comp_apply,
        Finsupp.lsingle_apply, Finsupp.lcomapDomain_apply,
        Finsupp.comapDomain_single,
        Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
      congr 1
      exact twist_twist _ _
  rw [hc, LinearEquiv.symm_apply_apply]

/-- Extract arbitrary old composition in chronological (first-position) order. -/
theorem prependExtractOld_insert_comp_tail (p : ZMod 2) {i : I} {v s w : List I}
    (x : PrependIdx i v w) (r : hom D Sc cutoff v s)
    (b : hom D Sc cutoff s x.oldTarget) :
    prependExtractOld D Sc cutoff p x
      (insert D Sc cutoff i v s r ≫ insert D Sc cutoff i s x.oldTarget b ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w)) =
      twist k p (r ≫ b) := by
  rw [← Category.assoc, ← insert_comp, prependExtractOld_insert_tail]

/-- A genuine old-quotient coordinate, obtained from the affine extraction. -/
def prependExtractOldQuotient (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) :
    hom D Sc cutoff (i :: v) w →ₗ[k] Old D Sc cutoff v x.oldTarget :=
  (ideal D Sc cutoff v x.oldTarget).mkQ.comp (prependExtractOld D Sc cutoff p x)

@[simp] theorem prependExtractOldQuotient_insert_tail (p : ZMod 2)
    {i : I} {v w : List I} (x : PrependIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    prependExtractOldQuotient D Sc cutoff p x
      (insert D Sc cutoff i v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w)) =
      (ideal D Sc cutoff v x.oldTarget).mkQ (twist k p r) := by
  exact congrArg (ideal D Sc cutoff v x.oldTarget).mkQ
    (prependExtractOld_insert_tail D Sc cutoff p x r)

/-- On a fixed tail, the vanishing coordinate is exactly the old ideal. -/
theorem prependExtractOldQuotient_insert_tail_eq_zero_iff (p : ZMod 2)
    {i : I} {v w : List I} (x : PrependIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    prependExtractOldQuotient D Sc cutoff p x
      (insert D Sc cutoff i v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w)) = 0 ↔
      r ∈ ideal D Sc cutoff v x.oldTarget := by
  rw [prependExtractOldQuotient_insert_tail, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hr
    simpa only [twist_twist] using twist_ideal D Sc cutoff p hr
  · exact twist_ideal D Sc cutoff p

end ELVOld
end OddMath.QuiverHecke
