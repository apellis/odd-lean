/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.CoefficientPolynomialTransport
import OddMath.QuiverHecke.ELVCyclotomicSeparation

/-!
# ELV coefficient-quotient transport

The coefficient-sensitive transport of `DeformedProjectiveResolution.md` §1 (1),
with the finite coefficient algebra of ELV (3.24)–(3.27). The quotient is by
`elvCoefficientIdeal`, including its even-cutoff top relation, not by an
ordinary polynomial ideal. The target is the coefficient-quotient tensor
module; no balanced QP identity or categorical action is asserted here.
-/

noncomputable section
open scoped TensorProduct
namespace OddMath.SKM.SYM
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X)

/-- The finite ELV coefficient algebra, retaining the exterior generators. -/
abbrev ELVCoefficientAlgebra (cutoff : I → ℕ) :=
  (elvCoefficientIdeal D k cutoff).ringCon.Quotient

def elvCoefficientQuotient (cutoff : I → ℕ) :
    SYM D k →ₐ[k] ELVCoefficientAlgebra (k := k) D cutoff :=
  (elvCoefficientIdeal D k cutoff).ringCon.mkₐ k

theorem elvCoefficientQuotient_eq_zero {cutoff : I → ℕ} {a : SYM D k}
    (ha : a ∈ elvCoefficientIdeal D k cutoff) :
    elvCoefficientQuotient D cutoff a = 0 := Quotient.sound ha

/-- Every elementary generator beyond its colour's finite rank vanishes. -/
theorem elvCoefficientQuotient_elementary (cutoff : I → ℕ) (i : I) (r : ℕ)
    (hr : elvElementaryRank D cutoff i ≤ r) :
    elvCoefficientQuotient (k := k) D cutoff (e D k i r) = 0 := by
  apply elvCoefficientQuotient_eq_zero
  exact TwoSidedIdeal.subset_span (Or.inl ⟨i, r, hr, rfl⟩)

/-- The top relation is retained also at cutoff zero, where it kills delta. -/
theorem elvCoefficientQuotient_top (cutoff : I → ℕ)
    (i : {i : I // D.parity i = 1}) (he : cutoff i.1 % 2 = 0) :
    elvCoefficientQuotient (k := k) D cutoff
      (delta D k i * elvChi D k i (cutoff i.1 / 2)) = 0 := by
  apply elvCoefficientQuotient_eq_zero
  exact TwoSidedIdeal.subset_span (Or.inr ⟨i, he, rfl⟩)

theorem elvChi_mem_even (i : {i : I // D.parity i = 1}) (r : ℕ) :
    polynomialExteriorEquiv D k (elvChi D k i r) ∈ polynomialExteriorParity D k 0 := by
  cases r with
  | zero => simpa [elvChi] using
      (SetLike.GradedOne.one_mem : (1 : PolynomialExterior D k) ∈ polynomialExteriorParity D k 0)
  | succ r => exact polynomialExterior_e_mem_even D k i.1 r

theorem elvCoefficient_mem_parity (i : {i : I // D.parity i = 1}) (n : ℕ) :
    polynomialExteriorEquiv D k (elvCoefficient D k i n) ∈
      polynomialExteriorParity D k (n : ZMod 2) := by
  have hn : (n : ZMod 2) = (n % 2 : ℕ) := by
    simpa only [ZMod.val_natCast] using (ZMod.natCast_zmod_val (n : ZMod 2)).symm
  unfold elvCoefficient
  split_ifs with he
  · rw [hn, he, Nat.cast_zero]
    exact elvChi_mem_even D i _
  · have ho : n % 2 = 1 := by omega
    rw [hn, ho, Nat.cast_one, map_mul]
    simpa only [add_zero] using SetLike.mul_mem_graded
      (polynomialExterior_delta_mem_odd D k i) (elvChi_mem_even D i (n / 2))

/-- The coefficient of x^j has parity N-j, including exterior coefficients. -/
theorem elvMonicCoefficient_mem_parity (i : {i : I // D.parity i = 1})
    (N : ℕ) (j : Fin (N + 1)) :
    polynomialExteriorEquiv D k (elvMonicCoefficient D k i N j) ∈
      polynomialExteriorParity D k ((N : ZMod 2) - j.val • D.parity i.1) := by
  have hj : j.val ≤ N := Nat.le_of_lt_succ j.isLt
  rw [elvMonicCoefficient, map_smul, i.property, nsmul_eq_mul, mul_one,
    ← Nat.cast_sub hj]
  exact Submodule.smul_mem _ _ (elvCoefficient_mem_parity D i (N - j.val))
end OddMath.SKM.SYM

namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- Base change of an affine Hom module to the exact finite ELV coefficient algebra. -/
abbrev ELVCoefficientHom (cutoff : I → ℕ) (t t' : List I) :=
  SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ⊗[k]
    ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))

/-- The canonical coefficient-quotient map; no flatness or descent premise. -/
def elvHomQuotient (cutoff : I → ℕ) (t t' : List I) :
    (coefficientObj D Sc t ⟶ coefficientObj D Sc t') →ₗ[k]
      ELVCoefficientHom D Sc cutoff t t' :=
  (TensorProduct.map (SKM.SYM.elvCoefficientQuotient D cutoff).toLinearMap
    (LinearMap.id : _ →ₗ[k] _)).comp (sourceTensorEquiv D Sc t t').symm.toLinearMap

@[simp] theorem elvHomQuotient_source (cutoff : I → ℕ) {t t' : List I}
    (a : SKM.SYM D k) (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    elvHomQuotient D Sc cutoff t t' (sourceCoefficientHom D Sc a f) =
      SKM.SYM.elvCoefficientQuotient D cutoff a ⊗ₜ[k] f := by
  change TensorProduct.map _ _ ((sourceTensorEquiv D Sc t t').symm
    (sourceTensorEquiv D Sc t t' (a ⊗ₜ[k] f))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul]
  rfl

/-- All elements of the coefficient ideal, not just polynomial truncations, vanish. -/
theorem elvHomQuotient_kills {cutoff : I → ℕ} {t t' : List I}
    {a : SKM.SYM D k} (ha : a ∈ SKM.SYM.elvCoefficientIdeal D k cutoff)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    elvHomQuotient D Sc cutoff t t' (sourceCoefficientHom D Sc a f) = 0 := by
  rw [elvHomQuotient_source, SKM.SYM.elvCoefficientQuotient_eq_zero D ha,
    TensorProduct.zero_tmul]

/-- The ELV polynomial at any strand, with the existing normalized left coefficients. -/
def elvDotPolynomial (i : {i : I // D.parity i = 1}) (w : List I) (r N : ℕ) :
    End (coefficientObj D Sc w) :=
  coefficientDotPolynomial D Sc w r N (SKM.SYM.elvMonicCoefficient D k i N)

/-- The quotient polynomial retains precisely the images of the ELV coefficients. -/
theorem elvHomQuotient_dotPolynomial (cutoff : I → ℕ)
    (i : {i : I // D.parity i = 1}) (w : List I) (r N : ℕ) :
    elvHomQuotient D Sc cutoff w w (elvDotPolynomial D Sc i w r N) =
      ∑ j : Fin (N + 1),
        SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.elvMonicCoefficient D k i N j)
          ⊗ₜ[k] (dotE D Sc w r ^ j.val : End _) := by
  simp only [elvDotPolynomial, coefficientDotPolynomial, map_sum, elvHomQuotient_source]

/-- At the first strand this is exactly the pre-existing ELV cyclotomic generator. -/
theorem elvDotPolynomial_first (i : {i : I // D.parity i = 1}) (tail : List I) (N : ℕ) :
    elvDotPolynomial D Sc i (i.1 :: tail) 0 N = elvCyclotomic D Sc i tail N := by
  unfold elvDotPolynomial coefficientDotPolynomial elvCyclotomic deformedCyclotomic
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [dotE_pow, firstDotPower, List.map_replicate]

/-- In the finite coefficient quotient the entire ELV polynomial has the
common sign (-1)^(N p(i) p(ν)). No moving-dot cyclotomic relation is imposed. -/
theorem elvDotPolynomial_transport (cutoff : I → ℕ)
    (i : {i : I // D.parity i = 1}) (l ν : List I) :
    elvHomQuotient D Sc cutoff _ _
      (elvDotPolynomial D Sc i (l ++ i.1 :: ν) l.length (cutoff i.1) ≫
        sourceCoefficientHom D Sc 1 (moveHom D Sc i.1 l ν)) =
      sign k ((cutoff i.1 : ZMod 2) * (D.parity i.1 * wordSumParity D ν)) •
        elvHomQuotient D Sc cutoff _ _
          (sourceCoefficientHom D Sc 1 (moveHom D Sc i.1 l ν) ≫
            elvDotPolynomial D Sc i (l ++ ν ++ [i.1]) (l.length + ν.length) (cutoff i.1)) := by
  unfold elvDotPolynomial
  rw [coefficientDotPolynomial_comp_moveHom D Sc i.1 l ν (cutoff i.1)
    (SKM.SYM.elvMonicCoefficient D k i (cutoff i.1)) (cutoff i.1 : ZMod 2)
    (SKM.SYM.elvMonicCoefficient_mem_parity D i (cutoff i.1)), map_smul]

/-- Old-strand ELV transport uses the parity of the entire moving chain. -/
theorem elvDotPolynomial_old_transport (cutoff : I → ℕ) (i : I)
    (x : {i : I // D.parity i = 1}) (v m l : List I) :
    elvHomQuotient D Sc cutoff _ _
      (elvDotPolynomial D Sc x (l ++ i :: (m ++ x.1 :: v))
          (l.length + 1 + m.length) (cutoff x.1) ≫
        sourceCoefficientHom D Sc 1 (moveHom D Sc i l (m ++ x.1 :: v))) =
      sign k ((cutoff x.1 : ZMod 2) * (D.parity i * wordSumParity D (m ++ x.1 :: v))) •
        elvHomQuotient D Sc cutoff _ _
          (sourceCoefficientHom D Sc 1 (moveHom D Sc i l (m ++ x.1 :: v)) ≫
            elvDotPolynomial D Sc x (l ++ (m ++ x.1 :: v) ++ [i])
              (l.length + m.length) (cutoff x.1)) := by
  unfold elvDotPolynomial
  rw [coefficientDotPolynomial_mem_comp_moveHom D Sc i x.1 v m l (cutoff x.1)
    (SKM.SYM.elvMonicCoefficient D k x (cutoff x.1)) (cutoff x.1 : ZMod 2)
    (SKM.SYM.elvMonicCoefficient_mem_parity D x (cutoff x.1)), map_smul]
end OddMath.QuiverHecke
