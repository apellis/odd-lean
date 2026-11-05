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

/-- The ELV polynomial at any strand, with the existing normalized left coefficients. -/
def elvDotPolynomial (i : {i : I // D.parity i = 1}) (w : List I) (r N : ℕ) :
    End (coefficientObj D Sc w) :=
  coefficientDotPolynomial D Sc w r N (SKM.SYM.elvMonicCoefficient D k i N)

/-- At the first strand this is exactly the pre-existing ELV cyclotomic generator. -/
theorem elvDotPolynomial_first (i : {i : I // D.parity i = 1}) (tail : List I) (N : ℕ) :
    elvDotPolynomial D Sc i (i.1 :: tail) 0 N = elvCyclotomic D Sc i tail N := by
  unfold elvDotPolynomial coefficientDotPolynomial elvCyclotomic deformedCyclotomic
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [dotE_pow, firstDotPower, List.map_replicate]

end OddMath.QuiverHecke
