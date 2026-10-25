/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LastDot
import OddMath.QuiverHecke.CyclotomicAction.SuperInduction
import StringDiagrams.Super.Functor

/-!
# The homogeneous dot on cyclotomic superinduction

Ports the dot construction of `Categorification/KLR/CyclotomicAction/Induction.lean`
using the last-dot relation from `CyclotomicAction/Slides.lean`.
For the signed-left, ordinary-right superbimodule convention the corner map is
`x ↦ (-1)^{|i||x|} x c`, not unsigned right multiplication by the last dot `c`.
No square, braid or KKO relation is asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams
open Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => inductionCorner D Sc i a ha n
local notation "GB" => cyclotomicParity D Sc a ha (n + 1)
local notation "GA" => cyclotomicParity D Sc a ha n
local notation "c" => cyclotomicLastDot D Sc i a n
local notation "d" => D.parity i

private theorem dot_mul_mem (x : CyclotomicAlgebra D Sc a (n + 1))
    (_hx : x ∈ inductionCornerSubmodule D Sc i a n) :
    x * c ∈ inductionCornerSubmodule D Sc i a n := by
  change (x * c) * cyclotomicAppend D Sc i a n 1 = x * c
  rw [mul_assoc, (cyclotomicLastDot_corner D Sc i a n).2]

/-- The parity sign followed by right multiplication by the last dot. -/
def inductionDotLinear : (P).toSVec ⟶ (P).toSVec :=
  SVec.ofHom ((P).toSVec.sgn d) ≫
    SVec.restrictHom ((SuperBimodule.regular GB).ract c) (dot_mul_mem D Sc i a n)

/-- The dot has the parity of the induction colour. -/
theorem inductionDotLinear_parity :
    inductionDotLinear D Sc i a ha n ∈ SVec.parityHom (P).toSVec (P).toSVec d := by
  change inductionDotLinear D Sc i a ha n ∈ parity (R := k) (P).toSVec (P).toSVec d
  unfold inductionDotLinear
  have hd := SVec.restrictHom_mem (hU := inductionCorner_odd_mem D Sc i a ha n)
    (hU' := inductionCorner_odd_mem D Sc i a ha n)
    ((SuperBimodule.regular GB).ract_mem d c
      (cyclotomicLastDot_parity D Sc i a ha n)) (dot_mul_mem D Sc i a n)
  simpa only [inductionCorner, inductionCornerSpace, SuperBimodule.regular, zero_add] using
    Supercategory.comp_mem (SVec.sgn_mem (P).toSVec d) hd

private theorem sgn_action {p : ZMod 2} {f : (P).toSVec ⟶ (P).toSVec}
    (hf : f ∈ SVec.parityHom (P).toSVec (P).toSVec p) (x : (P).toSVec) :
    (P).toSVec.sgn d (f x) = sign k (p * d) • f ((P).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

/-- Signed left linearity and ordinary right linearity use the concrete last-dot slide. -/
theorem inductionDotLinear_isHom :
    SuperBimodule.IsHom P P (inductionDotLinear D Sc i a ha n) := by
  apply (SuperBimodule.isHom_iff_of_mem (inductionDotLinear_parity D Sc i a ha n)).2
  constructor
  · intro p b hb
    apply SVec.hom_ext
    intro x
    have h := sgn_action D Sc i a ha n ((P).lact_mem p b hb) x
    apply Subtype.ext
    change ((P).toSVec.sgn d ((P).lact b x)).val * c =
      sign k (p * d) • (b * (((P).toSVec.sgn d x).val * c))
    rw [h]
    change (sign k (p * d) • (b * ((P).toSVec.sgn d x).val)) * c = _
    rw [smul_mul_assoc, mul_assoc]
  · intro r
    induction r using SuperBimodule.alg_induction_on GA with
    | zero => simp
    | add r s hr hs => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hr, hs]
    | hom p r hr =>
      apply SVec.hom_ext
      intro x
      have h := sgn_action D Sc i a ha n ((P).ract_mem p r hr) x
      apply Subtype.ext
      change ((P).toSVec.sgn d ((P).ract r x)).val * c =
        (((P).toSVec.sgn d x).val * c) * cyclotomicAppend D Sc i a n r
      rw [h]
      change (sign k (p * d) • (((P).toSVec.sgn d x).val *
        cyclotomicAppend D Sc i a n r)) * c = _
      rw [smul_mul_assoc, mul_assoc, cyclotomicLastDot_comm D Sc i a ha n hr,
        mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul, mul_assoc]

/-- The homogeneous dot endomorphism of the cyclotomic induction corner. -/
def inductionSuperDot : P ⟶ P :=
  ⟨inductionDotLinear D Sc i a ha n, inductionDotLinear_isHom D Sc i a ha n⟩

theorem inductionSuperDot_parity :
    inductionSuperDot D Sc i a ha n ∈ parity (R := k) P P d :=
  SuperBimodule.mem_parity_iff.2 (inductionDotLinear_parity D Sc i a ha n)

/-- On a homogeneous corner element the sign is explicit. -/
theorem inductionSuperDot_apply {p : ZMod 2} (x : (P).toSVec)
    (hx : x ∈ (P).toSVec.part p) :
    ((inductionSuperDot D Sc i a ha n).1 x).val =
      koszulSign p d • (x.val * c) := by
  change ((P).toSVec.sgn d x).val * c = _
  rw [SVec.sgn_apply_of_mem d hx]
  change (sign k (p * d) • x.val) * c = _
  rw [smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul]

/-- The last dot as a supernatural endomorphism of balanced-tensor induction. -/
def cyclotomicSuperInductionDot :
    SuperNatTrans k (cyclotomicSuperInduction D Sc i a ha n)
      (cyclotomicSuperInduction D Sc i a ha n) where
  app p M := if p = d then SuperBimodule.whiskerRight (inductionSuperDot D Sc i a ha n) M else 0
  app_mem p M := by
    split_ifs with h
    · subst p
      exact SuperBimodule.whiskerRight_mem P (inductionSuperDot_parity D Sc i a ha n) M
    · exact Submodule.zero_mem _
  naturality p M N q f hf := by
    change SuperBimodule.whiskerLeft P f ≫ (if p = d then
        SuperBimodule.whiskerRight (inductionSuperDot D Sc i a ha n) N else 0) =
      koszulSign p q • ((if p = d then
        SuperBimodule.whiskerRight (inductionSuperDot D Sc i a ha n) M else 0) ≫
          SuperBimodule.whiskerLeft P f)
    split_ifs with h
    · subst p
      rw [SuperBimodule.super_interchange P f (inductionSuperDot_parity D Sc i a ha n) hf,
        koszulSign_smul_smul]
    · simp

/-- Only the component of the induction colour's parity is nonzero. -/
theorem cyclotomicSuperInductionDot_homogeneous :
    (cyclotomicSuperInductionDot D Sc i a ha n).IsHomogeneous d := by
  intro q h
  funext M
  simp [cyclotomicSuperInductionDot, h]

end OddMath.QuiverHecke
