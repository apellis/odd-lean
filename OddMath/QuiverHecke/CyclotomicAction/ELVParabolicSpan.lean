/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendBalance
import OddMath.QuiverHecke.ShuffleBasis
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Output-parabolic spanning over full ELV coefficients

The affine spanning input (C) of `DeformedIdealSum.md`, in matrix-Hom
coordinates. The shuffle precedes the two parabolic normal forms in diagram
order; hence it follows the parabolic factor in algebra order. Tensoring the
proved affine basis equivalence retains the whole exterior coefficient algebra
and requires no flatness. No cyclotomic polynomial is moved through a factor.

`ideal_le_of_parabolic_terms` is the consumer for (IS2): it reduces containment
of the full cyclotomic ideal to the explicitly displayed shuffle/parabolic
terms. Parabolic normality and the short/long shuffle calculation are still
required to put these terms in the append-old span plus the prescribed W image.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Full-coefficient output-parabolic coordinates, before any cyclotomic quotient. -/
def shuffleAffineEquiv {t l r : List I} (hN : l.length + r.length = t.length) :
    hom D Sc cutoff t (l ++ r) ≃ₗ[k]
      (ShIdx hN →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  (TensorProduct.congr (LinearEquiv.refl k _) (shuffleBasis D Sc hN).repr).trans
    (TensorProduct.finsuppScalarRight k k _ _)

@[simp] theorem shuffleAffineEquiv_symm_single {t l r : List I}
    (hN : l.length + r.length = t.length) (x : ShIdx hN)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (shuffleAffineEquiv D Sc cutoff hN).symm (Finsupp.single x a) =
      a ⊗ₜ[k] shElt D Sc x := by
  change (TensorProduct.congr (LinearEquiv.refl k _) (shuffleBasis D Sc hN).repr).symm
    ((TensorProduct.finsuppScalarRight k k _ _).symm (Finsupp.single x a)) = _
  rw [TensorProduct.finsuppScalarRight_symm_apply_single, TensorProduct.congr_symm_tmul]
  simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply, Module.Basis.repr_symm_single,
    one_smul, shuffleBasis_apply]

/-- A unit-coefficient affine prefix introduces no coefficient sign. -/
theorem affineUnit_comp_coefficient {v w z : List I}
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D w) ⟶ (pres D Sc).obj (ob D z))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    affineUnit D Sc cutoff v w f ≫ (a ⊗ₜ[k] g : hom D Sc cutoff w z) =
      a ⊗ₜ[k] (f ≫ g) := by
  induction g using Supercategory.induction_on (R := k) (C := (pres D Sc).Presented) with
  | zero => simp only [TensorProduct.tmul_zero, Limits.comp_zero]
  | add g h hg hh =>
    have hadd := Preadditive.comp_add _ _ _ (affineUnit D Sc cutoff v w f)
      (a ⊗ₜ[k] g : hom D Sc cutoff w z) (a ⊗ₜ[k] h : hom D Sc cutoff w z)
    rw [TensorProduct.tmul_add, hadd, hg, hh, Preadditive.comp_add,
      TensorProduct.tmul_add]
  | hom q g hg =>
    change BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w)
      (SuperalgebraCat.ofElem 1) f ≫
        BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff z)
          (SuperalgebraCat.ofElem a) g = _
    rw [BoxProd.tmulHom_comp_tmulHom
      (show (SuperalgebraCat.ofElem (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)) ∈
        parity (R := k) (obj D Sc cutoff v).fst (obj D Sc cutoff w).fst 0 from
        id_mem (R := k) _) f (SuperalgebraCat.ofElem a) hg]
    simp only [koszulSign_zero_left, one_smul]
    change (a * 1) ⊗ₜ[k] (f ≫ g) = _
    rw [mul_one]

/-- The two block normal forms with an arbitrary full ELV coefficient. -/
def shuffleParabolic {t l r : List I} {hN : l.length + r.length = t.length}
    (x : ShIdx hN) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    hom D Sc cutoff (shL t l.length x.1.1 ++ shR t l.length x.1.1) (l ++ r) :=
  a ⊗ₜ[k] (((pres D Sc).obj (ob D (shL t l.length x.1.1)) ◁ x.2.2.nf) ≫
    (x.2.1.nf ▷ (pres D Sc).obj (ob D r)))

/-- The coefficient stays in the parabolic factor, with the shuffle on the required side. -/
theorem shuffle_parabolic_factorization {t l r : List I}
    {hN : l.length + r.length = t.length} (x : ShIdx hN)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    affineUnit D Sc cutoff _ _ (shPsi D Sc l.length x.1.1) ≫
      shuffleParabolic D Sc cutoff x a = a ⊗ₜ[k] shElt D Sc x := by
  exact affineUnit_comp_coefficient D Sc cutoff _ _ a

/-- The concrete finite parabolic terms span the full Hom, including exterior coefficients. -/
theorem hom_mem_of_shuffle_parabolic {t l r : List I}
    (hN : l.length + r.length = t.length) (S : Submodule k (hom D Sc cutoff t (l ++ r)))
    (hS : ∀ (x : ShIdx hN) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff),
      affineUnit D Sc cutoff _ _ (shPsi D Sc l.length x.1.1) ≫
        shuffleParabolic D Sc cutoff x a ∈ S)
    (f : hom D Sc cutoff t (l ++ r)) : f ∈ S := by
  obtain ⟨c, rfl⟩ := (shuffleAffineEquiv D Sc cutoff hN).symm.surjective f
  induction c using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using S.zero_mem
  | add c d hc hd => simpa only [map_add] using S.add_mem hc hd
  | single x a =>
    rw [shuffleAffineEquiv_symm_single]
    rw [← shuffle_parabolic_factorization]
    exact hS x a

/-- Length-mismatched full coefficient Homs vanish; no finite colour type is needed. -/
theorem hom_eq_zero_of_length_ne {v w : List I} (h : v.length ≠ w.length)
    (f : hom D Sc cutoff v w) : f = 0 := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => rw [hf, hg, add_zero]
  | tmul a f =>
    have hf : f = 0 := hom_eq_zero_of_content_ne D Sc (fun hc => h (by
      have hh := congrArg Multiset.card hc
      simpa using hh)) f
    rw [hf, TensorProduct.tmul_zero]

/-- There is no old first-position relation at the empty word. -/
theorem ideal_nil (w : List I) : ideal D Sc cutoff [] w = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨j, t, a, b, rfl⟩
  rw [hom_eq_zero_of_length_ne D Sc cutoff (by simp : ([] : List I).length ≠
    (j :: t).length) a, Limits.zero_comp]
  exact Submodule.zero_mem _

/-- In particular the append-old span is zero when the old word is empty. -/
theorem appendRelations_nil (i : I) (w : List I) :
    appendRelations D Sc cutoff i [] w = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨t, r, hr, b, rfl⟩
  rw [ideal_nil, Submodule.mem_bot] at hr
  rw [hr, map_zero, Limits.zero_comp]
  exact Submodule.zero_mem _

/-- Output-parabolic reduction of full ideal containment. The remaining hypothesis is
on explicit shuffle terms, not on the ideal itself or a cyclotomic quotient. -/
theorem ideal_le_of_parabolic_terms (v w : List I)
    (S : Submodule k (hom D Sc cutoff v w))
    (hS : ∀ (j : I) (t : List I) (hN : [j].length + t.length = v.length)
      (x : ShIdx hN) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
      (b : hom D Sc cutoff (j :: t) w),
      (affineUnit D Sc cutoff _ _ (shPsi D Sc [j].length x.1.1) ≫
        shuffleParabolic D Sc cutoff x a) ≫ relation D Sc cutoff j t ≫ b ∈ S) :
    ideal D Sc cutoff v w ≤ S := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, t, f, b, rfl⟩
  by_cases hN : [j].length + t.length = v.length
  · let L : hom D Sc cutoff v (j :: t) →ₗ[k] hom D Sc cutoff v w :=
      (Linear.rightComp k _ b).comp (Linear.rightComp k _ (relation D Sc cutoff j t))
    rw [← Category.assoc]
    change f ∈ S.comap L
    apply hom_mem_of_shuffle_parabolic D Sc cutoff hN (S.comap L) _ f
    intro x a
    change ((_ ≫ _) ≫ relation D Sc cutoff j t) ≫ b ∈ S
    simpa only [Category.assoc] using hS j t hN x a b
  · have hlen : v.length ≠ (j :: t).length := by
      simp only [List.length_cons, List.length_nil] at hN ⊢
      omega
    have hf := hom_eq_zero_of_length_ne D Sc cutoff hlen f
    rw [hf, Limits.zero_comp]
    exact S.zero_mem

/-- The precise remaining shuffle calculation for (IS2), with its prescribed W image. -/
theorem ideal_le_appendRelations_sup_range_of_parabolic_terms (i : I) (v w : List I)
    (hS : ∀ (j : I) (t : List I) (hN : [j].length + t.length = (v ++ [i]).length)
      (x : ShIdx hN) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
      (b : hom D Sc cutoff (j :: t) w),
      (affineUnit D Sc cutoff _ _ (shPsi D Sc [j].length x.1.1) ≫
        shuffleParabolic D Sc cutoff x a) ≫ relation D Sc cutoff j t ≫ b ∈
          appendRelations D Sc cutoff i v w ⊔
            LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v))) :
    ideal D Sc cutoff (v ++ [i]) w ≤ appendRelations D Sc cutoff i v w ⊔
      LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v)) :=
  ideal_le_of_parabolic_terms D Sc cutoff (v ++ [i]) w _ hS

end OddMath.QuiverHecke.ELVOld
