/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPrefixKilling
import OddMath.QuiverHecke.CyclotomicAction.ELVMovingShift
import OddMath.QuiverHecke.CyclotomicAction.PrefixQPRepeated

/-!
# Repeated-colour QP cancellation over ELV coefficients

The repeated-even step of `DeformedGlobalQP.md` §3 in the old-only quotient.
The library's even crossing convention contributes a minus sign, as in
`PrefixQPEquation.lean`; no coefficient or cyclotomic polynomial is cancelled.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Include an affine Hom with unit coefficient. -/
def affineUnit (v w : List I) :
    ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) →ₗ[k] hom D Sc cutoff v w :=
  TensorProduct.mk k (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) _ 1

theorem affineUnit_comp {v w z : List I}
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D w) ⟶ (pres D Sc).obj (ob D z)) :
    affineUnit D Sc cutoff v z (f ≫ g) =
      affineUnit D Sc cutoff v w f ≫ affineUnit D Sc cutoff w z g := by
  induction g using Supercategory.induction_on (R := k) (C := (pres D Sc).Presented) with
  | zero => simp only [Limits.comp_zero, map_zero]
  | add g h hg hh => simp only [Preadditive.comp_add, map_add, hg, hh]
  | hom q g hg =>
    symm
    change BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w)
      (SuperalgebraCat.ofElem 1) f ≫
        BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff z)
          (SuperalgebraCat.ofElem 1) g = _
    rw [BoxProd.tmulHom_comp_tmulHom
      (show (SuperalgebraCat.ofElem (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)) ∈
        parity (R := k) (obj D Sc cutoff v).fst (obj D Sc cutoff w).fst 0 from
        id_mem (R := k) _) f (SuperalgebraCat.ofElem 1) hg]
    simp only [koszulSign_zero_left, one_smul]
    change (1 * 1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] _ = _
    rw [one_mul]
    rfl

/-- Cancellation at any old position; the moving strand is never specialized. -/
theorem projection_even_difference_cancel (i : I) (hi : D.parity i = 0)
    (v z : List I) (a : ℕ) (h : hom D Sc cutoff (i :: v) z)
    (hh : projection D Sc cutoff i v z
      ((sourceDotPower D Sc cutoff (i :: v) (a + 1) 1 -
        sourceDotPower D Sc cutoff (i :: v) 0 1) ≫ h) = 0) :
    projection D Sc cutoff i v z h = 0 := by
  apply movingPower_eq_oldSource D Sc cutoff 0 i v z 1 (by simp [hi]) (by decide)
    (sourceDotPower D Sc cutoff v a 1)
  change projection D Sc cutoff i v z (movingPower D Sc cutoff i v 1 ≫ h) =
    projection D Sc cutoff i v z (insert D Sc cutoff i v v
      (sourceDotPower D Sc cutoff v a 1) ≫ h)
  rw [insert_sourceDotPower]
  rw [Preadditive.sub_comp, map_sub, sub_eq_zero] at hh
  exact hh.symm

/-- QP evaluated after the full first-position relation and an arbitrary continuation. -/
def qpEval (i : I) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: μ) ++ σ) z) :
    End ((pres D Sc).obj (ob D (i :: μ))) →ₗ[k] Target D Sc cutoff i (μ ++ σ) z :=
  (projection D Sc cutoff i (μ ++ σ) z).comp
    ((Linear.rightComp k _ (relation D Sc cutoff i (μ ++ σ) ≫ h)).comp
      ((rightContext D Sc cutoff σ (i :: μ) (i :: μ)).comp
        (affineUnit D Sc cutoff (i :: μ) (i :: μ))))

theorem qpEval_even_difference_cancel (i : I) (hi : D.parity i = 0)
    (μ σ z : List I) (a : ℕ) (ha : a < μ.length)
    (h : hom D Sc cutoff ((i :: μ) ++ σ) z)
    (f : End ((pres D Sc).obj (ob D (i :: μ))))
    (hf : qpEval D Sc cutoff i μ σ z h
      ((dotE D Sc (i :: μ) (a + 1) - dotE D Sc (i :: μ) 0) ≫ f) = 0) :
    qpEval D Sc cutoff i μ σ z h f = 0 := by
  apply projection_even_difference_cancel D Sc cutoff i hi (μ ++ σ) z a
  change projection D Sc cutoff i (μ ++ σ) z
    (rightContext D Sc cutoff σ (i :: μ) (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ)
        ((dotE D Sc (i :: μ) (a + 1) - dotE D Sc (i :: μ) 0) ≫ f)) ≫
      (relation D Sc cutoff i (μ ++ σ) ≫ h)) = 0 at hf
  rw [affineUnit_comp, rightContext_comp, Category.assoc] at hf
  have he : rightContext D Sc cutoff σ (i :: μ) (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ)
        (dotE D Sc (i :: μ) (a + 1) - dotE D Sc (i :: μ) 0)) =
      sourceDotPower D Sc cutoff (i :: (μ ++ σ)) (a + 1) 1 -
        sourceDotPower D Sc cutoff (i :: (μ ++ σ)) 0 1 := by
    rw [map_sub, map_sub]
    have ht (b : ℕ) (hb : b < (i :: μ).length) :
        rightContext D Sc cutoff σ (i :: μ) (i :: μ)
          (affineUnit D Sc cutoff (i :: μ) (i :: μ) (dotE D Sc (i :: μ) b)) =
        sourceDotPower D Sc cutoff (i :: (μ ++ σ)) b 1 := by
      change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        (dotE D Sc (i :: μ) b ▷ (pres D Sc).obj (ob D σ)) =
        (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          (dotE D Sc (i :: (μ ++ σ)) b ^ 1)
      rw [pow_one, dotE_whiskerRight D Sc (i :: μ) σ b hb]
      rfl
    rw [ht (a + 1) (by simp; omega), ht 0 (by simp)]
  rw [he] at hf
  exact hf

/-- The repeated-even recursion in every right context, with its surviving minus sign.
All exterior coefficients remain in the relation and in the arbitrary continuation. -/
theorem qp_repeated_even (i : I) (hi : D.parity i = 0) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: (μ ++ [i])) ++ σ) z) :
    qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (moveHom D Sc i [] (μ ++ [i]) ≫ lastToFirstHom D Sc i (μ ++ [i])) =
    -qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (moveWhisker D Sc i μ ≫
        (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) := by
  let E := dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) -
    dotE D Sc (i :: (μ ++ [i])) 0
  let A : (pres D Sc).obj (ob D (i :: (μ ++ [i]))) ⟶
      (pres D Sc).obj (ob D (i :: (μ ++ [i]))) := moveWhisker D Sc i μ ≫
    (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))
  let B := moveWhisker D Sc i μ ≫ lastToFirstHom D Sc i (μ ++ [i])
  have hK := allPrefix_relation_context D Sc cutoff i μ σ z h
  change projection D Sc cutoff i ((μ ++ [i]) ++ σ) z
    (rightContext D Sc cutoff σ _ _
      (affineUnit D Sc cutoff _ _ (moveHom D Sc i [] (μ ++ [i])) ≫
        affineUnit D Sc cutoff _ _
          (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) ≫
      relation D Sc cutoff i ((μ ++ [i]) ++ σ) ≫ h) = 0 at hK
  rw [← affineUnit_comp] at hK
  have hzero : qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (E ≫ (A + E ≫ B)) = 0 := by
    change qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (moveHom D Sc i [] (μ ++ [i]) ≫
        (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) = 0 at hK
    rw [moveHom_append_self, moveWhisker_comp_sameIntertwiner_even D Sc i hi μ] at hK
    simpa only [E, A, B, lastToFirstHom_append_self, Preadditive.add_comp,
      Preadditive.comp_add, Category.assoc] using hK
  have hc := qpEval_even_difference_cancel D Sc cutoff i hi (μ ++ [i]) σ z μ.length
    (by simp) h (A + E ≫ B) hzero
  rw [map_add] at hc
  rw [moveHom_lastToFirstHom_append_self_even D Sc i hi μ]
  exact eq_neg_of_add_eq_zero_right hc

end OddMath.QuiverHecke.ELVOld
