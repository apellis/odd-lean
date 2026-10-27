/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerGrading
import OddMath.QuiverHecke.CyclotomicAction.SignedPolynomialTransport
import OddMath.QuiverHecke.WeightedCoefficientSeparation

/-!
# Coefficient-polynomial transport through an intertwiner chain

The full source-coefficient transport identity of
`docs/Nondegeneracy/DeformedProjectiveResolution.md`, §1, equation (1),
supporting the repeated-colour QP step in `DeformedGlobalQP.md`, §3.
The affine dot transport is supplied by the existing KKO I (8.13) lemmas.

A coefficient of degree m in a polynomial of total parity P has parity
P - m p(x). Its Koszul sign and the dot sign combine to P times the
parity of the entire intertwiner chain. Odd coefficients are not central:
the composition is the existing `sourceCoefficientHom` composition in
`CoefficientH`, retaining the full abstract SYM algebra.

Both moving and old strands are covered over any commutative ground ring
with the given scalar datum, without finite-colour or monicity assumptions.
Finite ELV coefficient quotient descent and the balanced QP induction are
separate obligations, not consequences claimed here.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

private theorem coefficientTransport_zsign (p : ZMod 2) :
    SKM.zsign k p = sign k p := by
  rcases parity_eq_zero_or_one p with h | h <;> simp [h, SKM.zsign]

private theorem coefficientTransport_pow_parity {A : H D Sc} (y : End A)
    {p : ZMod 2} (hy : y ∈ parity (R := k) A A p) (m : ℕ) :
    (y ^ m : End A) ∈ parity (R := k) A A (m • p) := by
  induction m with
  | zero => simpa only [pow_zero, zero_nsmul, End.one_def] using id_mem (R := k) A
  | succ m ih =>
    simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm] using comp_mem hy ih

/-- Finite dot polynomial with coefficients in the full abstract source algebra. -/
def coefficientDotPolynomial (w : List I) (r N : ℕ) (c : Fin (N + 1) → SKM.SYM D k) :
    End (coefficientObj D Sc w) :=
  ∑ m, sourceCoefficientHom D Sc (c m) (dotE D Sc w r ^ m.val)

private theorem coefficientTransport_sum {t t' : List I}
    (x : End ((pres D Sc).obj (ob D t)))
    (y : End ((pres D Sc).obj (ob D t')))
    (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    (p q P : ZMod 2) (N : ℕ) (c : Fin (N + 1) → SKM.SYM D k)
    (hy : y ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ q)
    (h : ∀ m : ℕ, (x ^ m : End _) ≫ g = sign k (m • (p * q)) •
      (g ≫ (y ^ m : End _)))
    (hc : ∀ m, SKM.SYM.polynomialExteriorEquiv D k (c m) ∈
      SKM.SYM.polynomialExteriorParity D k (P - m.val • p)) :
    (∑ m, sourceCoefficientHom D Sc (c m) (x ^ m.val)) ≫
        sourceCoefficientHom D Sc 1 g =
      sign k (P * q) • (sourceCoefficientHom D Sc 1 g ≫
        ∑ m, sourceCoefficientHom D Sc (c m) (y ^ m.val)) := by
  classical
  rw [Preadditive.sum_comp, Preadditive.comp_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have h1 : SKM.SYM.polynomialExteriorEquiv D k 1 ∈
      SKM.SYM.polynomialExteriorParity D k 0 := by
    rw [map_one]
    exact SetLike.GradedOne.one_mem
  rw [sourceCoefficientHom_comp D Sc (hc m) _ _ hg,
    sourceCoefficientHom_comp D Sc h1 _ _ (coefficientTransport_pow_parity D Sc y hy m.val),
    koszulSign_zero_left, one_smul, one_mul, mul_one, h,
    sourceCoefficientHom_smul_right, koszulSign_smul (R := k), smul_smul, ← sign_add]
  congr 2
  simp only [nsmul_eq_mul]
  ring

/-- Full source coefficients and the moving dot acquire a common total Koszul sign.
No centrality of odd coefficients is assumed. This is affine transport, not the
balanced QP induction or construction of the finite ELV action. -/
theorem coefficientDotPolynomial_comp_moveHom (i : I) (l ν : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) (P : ZMod 2)
    (hc : ∀ m, SKM.SYM.polynomialExteriorEquiv D k (c m) ∈
      SKM.SYM.polynomialExteriorParity D k (P - m.val • D.parity i)) :
    coefficientDotPolynomial D Sc (l ++ i :: ν) l.length N c ≫
        sourceCoefficientHom D Sc 1 (moveHom D Sc i l ν) =
      sign k (P * (D.parity i * wordSumParity D ν)) •
        (sourceCoefficientHom D Sc 1 (moveHom D Sc i l ν) ≫
          coefficientDotPolynomial D Sc (l ++ ν ++ [i]) (l.length + ν.length) N c) := by
  apply coefficientTransport_sum D Sc _ _ _ (D.parity i)
    (D.parity i * wordSumParity D ν) P N c
  · simpa only [List.append_assoc, List.append_nil, List.length_append] using
      positionedDot_parity D Sc (l ++ ν) [] i
  · exact moveHom_parity D Sc i l ν
  · intro m
    have he : D.parity i * (D.parity i * wordSumParity D ν) =
        D.parity i * wordSumParity D ν := by
      rcases parity_eq_zero_or_one (D.parity i) with hp | hp <;> simp [hp]
    rw [he, ← coefficientTransport_zsign]
    exact dot_pow_comp_moveHom D Sc i l ν m
  · exact hc

private theorem coefficientTransport_signed_pow {C : Type*} [Category C]
    [Preadditive C] [Linear k C] {A B : C}
    (x : End A) (y : End B) (g : A ⟶ B) (q : ZMod 2)
    (h : x ≫ g = SKM.zsign k q • (g ≫ y)) (m : ℕ) :
    (x ^ m : End A) ≫ g = SKM.zsign k (m • q) • (g ≫ (y ^ m : End B)) := by
  induction m with
  | zero => simp [End.one_def, SKM.zsign]
  | succ m ih =>
    rw [pow_succ, End.mul_def, Category.assoc, ih, Linear.comp_smul,
      ← Category.assoc, h, Linear.smul_comp, smul_smul, ← zsign_add_eq,
      pow_succ, End.mul_def, succ_nsmul, Category.assoc]

/-- An old strand polynomial has the same total coefficient-and-dot sign,
using the parity of the entire moving chain. -/
theorem coefficientDotPolynomial_mem_comp_moveHom (i x : I) (v m l : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) (P : ZMod 2)
    (hc : ∀ a, SKM.SYM.polynomialExteriorEquiv D k (c a) ∈
      SKM.SYM.polynomialExteriorParity D k (P - a.val • D.parity x)) :
    coefficientDotPolynomial D Sc (l ++ i :: (m ++ x :: v)) (l.length + 1 + m.length) N c ≫
        sourceCoefficientHom D Sc 1 (moveHom D Sc i l (m ++ x :: v)) =
      sign k (P * (D.parity i * wordSumParity D (m ++ x :: v))) •
        (sourceCoefficientHom D Sc 1 (moveHom D Sc i l (m ++ x :: v)) ≫
          coefficientDotPolynomial D Sc (l ++ (m ++ x :: v) ++ [i]) (l.length + m.length) N c) := by
  apply coefficientTransport_sum D Sc _ _ _ (D.parity x)
    (D.parity i * wordSumParity D (m ++ x :: v)) P N c
  · have he : (l ++ m) ++ x :: (v ++ [i]) = l ++ (m ++ x :: v) ++ [i] := by simp
    have hy := positionedDot_parity D Sc (l ++ m) (v ++ [i]) x
    rw [he] at hy
    simpa only [List.length_append] using hy
  · exact moveHom_parity D Sc i l (m ++ x :: v)
  · intro a
    rw [← coefficientTransport_zsign]
    exact coefficientTransport_signed_pow _ _ _ _
      (dot_mem_comp_moveHom D Sc i x v m l (m ++ x :: v) (by simp)) a
  · exact hc
end OddMath.QuiverHecke
