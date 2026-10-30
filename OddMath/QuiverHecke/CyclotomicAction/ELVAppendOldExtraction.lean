/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVPrependOldExtraction

/-!
# ELV old-Hom extraction from append PBW coordinates

The extraction step of `ELVPrependCoordinates.md`, needed for the old-only
coordinate comparison in `DeformedGlobalQP.md` §1. Only the old normal-form
component of the existing `AppendIdx` is replaced; the moving exponent and
inverse shuffle remain unchanged. No finite-colour or flatness assumption is used.

`appendExtractOld_insert_comp_tail` extracts arbitrary full-ELV old
composition. `appendExtractOldQuotient_insert_tail_eq_zero_iff` identifies
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

namespace AppendIdx
variable {i : I} {v w : List I}
/-- Replace only the old normal form, keeping the moving exponent and shuffle. -/
def replaceOld (x : AppendIdx i v w) (y : NFIdx v x.oldTarget) : AppendIdx i v w :=
  ⟨(x.1.1, y.1.1, y.1.2, x.1.2.2.2), y.2.1, y.2.2.1, by
    have he := tgt_append_right [i] (t := v)
      (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2))
    simpa only [appendCrossingWord, cw_append, tgt_append, he, y.tgt_cw]
      using x.moving_target⟩

theorem replaceOld_target (x : AppendIdx i v w) (y : NFIdx v x.oldTarget) :
    (x.replaceOld y).oldTarget = x.oldTarget := y.tgt_cw

theorem replaceOld_injective (x : AppendIdx i v w) : Function.Injective x.replaceOld := by
  intro y z h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun a : AppendIdx i v w => a.1.2.1) h)
    (congrArg (fun a : AppendIdx i v w => a.1.2.2.1) h)

end AppendIdx
namespace ELVOld

/-- Coefficients of a fixed moving tail, with the mandatory coefficient-parity twist. -/
def appendTailCoefficients {i : I} {v w : List I} (x : AppendIdx i v w) :
    (NFIdx v x.oldTarget →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) →ₗ[k]
      (AppendIdx i v w →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  Finsupp.lsum k fun y => (Finsupp.lsingle (x.replaceOld y)).comp
    (coefficientTwist D cutoff (appendTailParity D x))

/-- Replacing the old index leaves the moving diagram unchanged. -/
theorem appendElt_replaceOld {i : I} {v w : List I} (x : AppendIdx i v w)
    (y : NFIdx v x.oldTarget) :
    appendElt D Sc (x.replaceOld y) =
      affineRightContext D Sc [i] v x.oldTarget y.nf ≫ appendTail D Sc x := by
  change _ = (y.nf ▷ (pres D Sc).obj (ob D [i])) ≫ _
  rw [nf_whiskerRight]
  unfold appendTail appendElt
  rw [cl_comp]
  apply cl_eq_cl
  simp only [AppendIdx.gens, AppendIdx.replaceOld, List.append_assoc]

/-- The tail acts on every exterior coefficient by its coefficient-parity involution. -/
theorem append_insert_nf_tail {i : I} {v w : List I} (x : AppendIdx i v w)
    (y : NFIdx v x.oldTarget)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    rightContext D Sc cutoff [i] v x.oldTarget (a ⊗ₜ[k] y.nf) ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w) =
      coefficientTwist D cutoff (appendTailParity D x) a ⊗ₜ[k]
        appendElt D Sc (x.replaceOld y) := by
  induction a using DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff) with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Limits.zero_comp]
  | add a b ha hb =>
    simp only [map_add, TensorProduct.add_tmul, Preadditive.add_comp, ha, hb]
  | @homogeneous q a =>
    have ht : coefficientTwist D cutoff (appendTailParity D x) a =
        sign k (appendTailParity D x * q) • (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
      twist_of_mem _ a.property
    rw [rightContext_tmul]
    change BoxProd.tmulHom (X := obj D Sc cutoff (v ++ [i]))
      (Y := obj D Sc cutoff (x.oldTarget ++ [i])) (SuperalgebraCat.ofElem a) _ ≫
      BoxProd.tmulHom (X := obj D Sc cutoff (x.oldTarget ++ [i]))
      (Y := obj D Sc cutoff w) (SuperalgebraCat.ofElem 1) _ = _
    rw [BoxProd.tmulHom_comp_tmulHom a.property _ (SuperalgebraCat.ofElem 1)
      (appendTail_mem D Sc x)]
    change koszulSign q (appendTailParity D x) •
      ((1 * (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)) ⊗ₜ[k]
        (affineRightContext D Sc [i] v x.oldTarget y.nf ≫ appendTail D Sc x)) = _
    rw [one_mul, ← appendElt_replaceOld, ht, TensorProduct.smul_tmul',
      koszulSign_smul (R := k), mul_comm q]

/-- Extracting an arbitrary old coefficient followed by a prescribed moving tail. -/
theorem appendAffineEquiv_insert_tail {i : I} {v w : List I} (x : AppendIdx i v w)
    (r : hom D Sc cutoff v x.oldTarget) :
    appendAffineEquiv D Sc cutoff i v w
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w)) =
      appendTailCoefficients D cutoff x (oldAffineEquiv D Sc cutoff v x.oldTarget r) := by
  obtain ⟨f, rfl⟩ := (oldAffineEquiv D Sc cutoff v x.oldTarget).symm.surjective r
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Limits.zero_comp]
  | add f g hf hg => simp only [map_add, Preadditive.add_comp, hf, hg]
  | single y a =>
    rw [oldAffineEquiv_symm_single, append_insert_nf_tail]
    rw [← appendAffineEquiv_symm_single, LinearEquiv.apply_symm_apply]
    rw [← oldAffineEquiv_symm_single, LinearEquiv.apply_symm_apply]
    simp only [appendTailCoefficients, Finsupp.lsum_single, LinearMap.comp_apply,
      Finsupp.lsingle_apply]

/-- Restrict the existing PBW coordinates to one moving tail and regroup the old basis.
The normalization includes total old-Hom parity, not merely coefficient parity. -/
def appendExtractOld (p : ZMod 2) {i : I} {v w : List I} (x : AppendIdx i v w) :
    hom D Sc cutoff (v ++ [i]) w →ₗ[k] hom D Sc cutoff v x.oldTarget :=
  (twist k p).comp ((oldAffineEquiv D Sc cutoff v x.oldTarget).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff (appendTailParity D x))).comp
      ((Finsupp.lcomapDomain x.replaceOld x.replaceOld_injective).comp
        (appendAffineEquiv D Sc cutoff i v w).toLinearMap)))

/-- Actual extraction recovers an arbitrary old Hom coefficient, with its total twist. -/
theorem appendExtractOld_insert_tail (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    appendExtractOld D Sc cutoff p x
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w)) = twist k p r := by
  unfold appendExtractOld
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [appendAffineEquiv_insert_tail]
  have hc (f : NFIdx v x.oldTarget →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
      Finsupp.mapRange.linearMap (coefficientTwist D cutoff (appendTailParity D x))
        (Finsupp.lcomapDomain (R := k) x.replaceOld x.replaceOld_injective
          (appendTailCoefficients D cutoff x f)) = f := by
    induction f using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg]
    | single y a =>
      simp only [appendTailCoefficients, Finsupp.lsum_single, LinearMap.comp_apply,
        Finsupp.lsingle_apply, Finsupp.lcomapDomain_apply,
        Finsupp.comapDomain_single,
        Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
      congr 1
      exact twist_twist _ _
  rw [hc, LinearEquiv.symm_apply_apply]

/-- Extract arbitrary old composition in chronological (first-position) order. -/
theorem appendExtractOld_insert_comp_tail (p : ZMod 2) {i : I} {v s w : List I}
    (x : AppendIdx i v w) (r : hom D Sc cutoff v s)
    (b : hom D Sc cutoff s x.oldTarget) :
    appendExtractOld D Sc cutoff p x
      (rightContext D Sc cutoff [i] v s r ≫ rightContext D Sc cutoff [i] s x.oldTarget b ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w)) =
      twist k p (r ≫ b) := by
  rw [← Category.assoc, ← rightContext_comp, appendExtractOld_insert_tail]

/-- A genuine old-quotient coordinate, obtained from the affine extraction. -/
def appendExtractOldQuotient (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) :
    hom D Sc cutoff (v ++ [i]) w →ₗ[k] Old D Sc cutoff v x.oldTarget :=
  (ideal D Sc cutoff v x.oldTarget).mkQ.comp (appendExtractOld D Sc cutoff p x)

@[simp] theorem appendExtractOldQuotient_insert_tail (p : ZMod 2)
    {i : I} {v w : List I} (x : AppendIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    appendExtractOldQuotient D Sc cutoff p x
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w)) =
      (ideal D Sc cutoff v x.oldTarget).mkQ (twist k p r) := by
  exact congrArg (ideal D Sc cutoff v x.oldTarget).mkQ
    (appendExtractOld_insert_tail D Sc cutoff p x r)

/-- On a fixed tail, the vanishing coordinate is exactly the old ideal. -/
theorem appendExtractOldQuotient_insert_tail_eq_zero_iff (p : ZMod 2)
    {i : I} {v w : List I} (x : AppendIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    appendExtractOldQuotient D Sc cutoff p x
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w)) = 0 ↔
      r ∈ ideal D Sc cutoff v x.oldTarget := by
  rw [appendExtractOldQuotient_insert_tail, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hr
    simpa only [twist_twist] using twist_ideal D Sc cutoff p hr
  · exact twist_ideal D Sc cutoff p

end ELVOld
end OddMath.QuiverHecke
