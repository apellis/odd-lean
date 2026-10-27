/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerParity

/-!
# Repeated-odd local cyclotomic error

The two-strand reduction needed for Kang–Kashiwara–Oh, arXiv:1206.5933v2,
Theorem 8.5 is a right factorization by the old cyclotomic relation.
The error `T g - (u² + v²)` transports every even power with the same
factor and every odd power with a second explicit factor. Homogeneous
central-coefficient polynomials therefore factor without cancelling a dot
difference. This is a local reduction, not a construction of P or a QP
identity for maps, and does not supply projectivity or multicolour induction.
-/

noncomputable section
namespace OddMath.OddNilHecke.Intertwiner
variable {A : Type*} [Ring A]

/-- The difference between the crossing-intertwiner product and its polynomial term. -/
def error (u v T : A) : A := T * element u v T - (u ^ 2 + v ^ 2)
/-- The right factor for an odd exponent of the first dot. -/
def oddError (u v T : A) : A :=
  (v ^ 2 + 2 * u * v - u ^ 2) - (v + u) * squareDiff u v * T

/-- Explicit error and its two generating dot transports in any odd nilHecke ring. -/
theorem error_local (u v T : A)
    (hsquare : T * T = 0) (hdots : u * v + v * u = 0)
    (hleft : T * u + v * T = 1) (hright : u * T + T * v = 1) :
    error u v T = (u ^ 2 + v ^ 2) - squareDiff u v * (v - u) * T ∧
    u ^ 2 * error u v T = error u v T * v ^ 2 ∧
    u * error u v T = oddError u v T * v := by
  have hvu : v * u = -(u * v) := eq_neg_of_add_eq_zero_right hdots
  have hTu : T * u = 1 - v * T := eq_sub_of_add_eq hleft
  have hTv : T * v = 1 - u * T := eq_sub_of_add_eq' hright
  have hvua (a : A) : v * (u * a) = -(u * (v * a)) := by
    rw [← mul_assoc, hvu, neg_mul, mul_assoc]
  have hTua (a : A) : T * (u * a) = a - v * (T * a) := by
    rw [← mul_assoc, hTu, sub_mul, one_mul, mul_assoc]
  have hTva (a : A) : T * (v * a) = a - u * (T * a) := by
    rw [← mul_assoc, hTv, sub_mul, one_mul, mul_assoc]
  have hTTa (a : A) : T * (T * a) = 0 := by
    rw [← mul_assoc, hsquare, zero_mul]
  unfold error oddError element squareDiff
  refine ⟨?_, ?_, ?_⟩ <;>
    noncomm_ring [hvu, hTu, hTv, hsquare, hvua, hTua, hTva, hTTa]

/-- Transport by every even power, proved by induction. -/
theorem error_even_pow (u v T : A)
    (hsquare : T * T = 0) (hdots : u * v + v * u = 0)
    (hleft : T * u + v * T = 1) (hright : u * T + T * v = 1) (n : ℕ) :
    u ^ (2 * n) * error u v T = error u v T * v ^ (2 * n) := by
  have h := (error_local u v T hsquare hdots hleft hright).2.1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add, pow_add,
      mul_assoc, h, ← mul_assoc, ih, mul_assoc]

/-- Transport by every odd power. -/
theorem error_odd_pow (u v T : A)
    (hsquare : T * T = 0) (hdots : u * v + v * u = 0)
    (hleft : T * u + v * T = 1) (hright : u * T + T * v = 1) (n : ℕ) :
    u ^ (2 * n + 1) * error u v T = oddError u v T * v ^ (2 * n + 1) := by
  rw [pow_succ', mul_assoc, error_even_pow u v T hsquare hdots hleft hright,
    ← mul_assoc, (error_local u v T hsquare hdots hleft hright).2.2,
    mul_assoc, ← pow_succ']

/-- The all-exponent local error factorization. -/
theorem error_pow (u v T : A)
    (hsquare : T * T = 0) (hdots : u * v + v * u = 0)
    (hleft : T * u + v * T = 1) (hright : u * T + T * v = 1) (m : ℕ) :
    u ^ m * error u v T =
      (if Even m then error u v T else oddError u v T) * v ^ m := by
  rcases Nat.even_or_odd m with hm | hm
  · rw [ite_eq_left hm]
    obtain ⟨n, rfl⟩ := hm
    simpa only [two_mul] using error_even_pow u v T hsquare hdots hleft hright n
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hm)]
    obtain ⟨n, rfl⟩ := hm
    exact error_odd_pow u v T hsquare hdots hleft hright n

variable {k : Type*} [CommRing k] [Algebra k A]

/-- Central-coefficient polynomials supported in one parity factor through the old relation.
The parity index need not be the degree; zero polynomials and constants are included. -/
theorem error_polynomial (u v T : A)
    (hsquare : T * T = 0) (hdots : u * v + v * u = 0)
    (hleft : T * u + v * T = 1) (hright : u * T + T * v = 1)
    (f : Polynomial k) (p : ℕ)
    (hf : ∀ m, f.coeff m ≠ 0 → (Even m ↔ Even p)) :
    Polynomial.aeval u f * T * element u v T -
      Polynomial.aeval u f * (u ^ 2 + v ^ 2) =
      (if Even p then error u v T else oddError u v T) * Polynomial.aeval v f := by
  rw [mul_assoc, ← mul_sub]
  change Polynomial.aeval u f * error u v T = _
  simp only [Polynomial.aeval_eq_sum_range, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hz : f.coeff m = 0
  · simp [hz]
  · rw [smul_mul_assoc, error_pow u v T hsquare hdots hleft hright,
      if_congr (hf m hz) rfl rfl, mul_smul_comm]
end OddMath.OddNilHecke.Intertwiner

namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification MulOpposite MonoidalCategory
open scoped Classical
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

private def prependEnd (i : I) {n : ℕ} (w : Word I n) :
    End (wordObj D Sc w) →ₐ[k] End (wordObj D Sc (prependWord i w)) where
  toFun := prependHom D Sc i w w
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    exact MonoidalSupercategory.whiskerLeft_id (R := k)
      ((pres D Sc).obj (ob D [i])) (wordObj D Sc w)
  map_mul' f g := by
    change _ ◁ (g ≫ f) = (_ ◁ g) ≫ (_ ◁ f)
    exact MonoidalSupercategory.whiskerLeft_comp (R := k) _ g f
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, map_smul]
    exact congrArg (c • ·) (MonoidalSupercategory.whiskerLeft_id (R := k)
      ((pres D Sc).obj (ob D [i])) (wordObj D Sc w))

omit [Fintype I] in
private theorem prepend_dot (i : I) {n : ℕ} (w : Word I n) :
    prependHom D Sc i w w (dotE D Sc w.1 0) = dotE D Sc (i :: w.1) 1 := by
  simp [prependHom, dotE_eq, cl, wordObj, Presentation.diag_whiskerLeft, pl, PG.ld]
  apply Presentation.diag_eq_of_layers_eq
  cases w.1 <;> simp [mkD, layList, ob, lay, Layer.wl]

omit [Fintype I] in
/-- The shifted old relation is the polynomial in the second dot, including constants. -/
theorem prepend_generator_single (i : I) (a : I → _root_.Polynomial k) :
    prependAlgebra D Sc i 1 (cyclotomicGenerator D Sc a (⟨[i], rfl⟩ : Word I 1)) =
      FiniteHomMatrix.single (⟨[i, i], rfl⟩ : Word I 2) ⟨[i, i], rfl⟩
        (_root_.Polynomial.aeval (dotE D Sc [i, i] 1) (a i)) := by
  change prependLinear D Sc i 1 (FiniteHomMatrix.single _ _ _) = _
  rw [prependLinear_single]
  congr 1
  have h := _root_.Polynomial.aeval_algHom_apply
    (prependEnd D Sc i (⟨[i], rfl⟩ : Word I 1)) (dotE D Sc [i] 0) (a i)
  have hd : prependEnd D Sc i (⟨[i], rfl⟩ : Word I 1) (dotE D Sc [i] 0) =
      dotE D Sc [i, i] 1 := prepend_dot D Sc i ⟨[i], rfl⟩
  exact h.symm.trans (congrArg (fun z : End (wordObj D Sc
    (prependWord i (⟨[i], rfl⟩ : Word I 1))) => _root_.Polynomial.aeval z (a i)) hd)

/-- Any left multiple of an old relation vanishes in the prescribed shifted tensor. -/
theorem prepend_generator_tmul_zero (i : I) (β : Multiset I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (w : Word I (n + 1)) (r : Hn D Sc (n + 1 + 1))
    (b : (qCoefficient D Sc i β a ha n).toSVec) :
    InductionAlong.Ind.tmul
      ((r * prependAlgebra D Sc i (n + 1) (cyclotomicGenerator D Sc a w)) •
        InductionAlong.unitGen (prependAlgebra D Sc i (n + 1) :
          Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) b = 0 := by
  let φ := (prependAlgebra D Sc i (n + 1) :
    Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
  have he : (r * φ (cyclotomicGenerator D Sc a w)) • InductionAlong.unitGen φ =
      op (cyclotomicGenerator D Sc a w) • (r • InductionAlong.unitGen φ) := by
    apply Subtype.ext
    change (r * φ _) * φ 1 = (r * φ 1) * φ _
    rw [mul_assoc, ← map_mul, mul_one, mul_assoc, ← map_mul, one_mul]
    rfl
  change InductionAlong.Ind.tmul ((r * φ (cyclotomicGenerator D Sc a w)) •
    InductionAlong.unitGen φ) b = 0
  rw [he, InductionAlong.Ind.op_smul_tmul]
  have hb : cyclotomicGenerator D Sc a w • b = 0 := by
    change (qCoefficient D Sc i β a ha n).lact
      (cyclotomicMk D Sc a n (cyclotomicGenerator D Sc a w)) b = 0
    rw [cyclotomicMk_generator, map_zero]
    rfl
  rw [hb, InductionAlong.Ind.tmul_zero]

/-- The local cyclotomic error on the repeated word, in endomorphism multiplication order. -/
def repeatedOddError (i : I) (a : I → _root_.Polynomial k) :
    End ((pres D Sc).obj (ob D [i, i])) :=
  let u := dotE D Sc [i, i] 0
  let v := dotE D Sc [i, i] 1
  let T := crossE D Sc [i, i] 0
  _root_.Polynomial.aeval u (a i) * T * OddNilHecke.Intertwiner.element u v T -
    _root_.Polynomial.aeval u (a i) * (u ^ 2 + v ^ 2)

omit [Fintype I] in
/-- The old relation is a right factor; parity homogeneity allows either even or odd degree. -/
theorem repeatedOddError_factor (i : I) (hi : D.parity i = 1)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) :
    repeatedOddError D Sc i a =
      (if Even (a i).natDegree then
        OddNilHecke.Intertwiner.error (dotE D Sc [i, i] 0) (dotE D Sc [i, i] 1)
          (crossE D Sc [i, i] 0)
      else OddNilHecke.Intertwiner.oddError (dotE D Sc [i, i] 0) (dotE D Sc [i, i] 1)
          (crossE D Sc [i, i] 0)) * _root_.Polynomial.aeval (dotE D Sc [i, i] 1) (a i) := by
  have h : SignedNilHecke.OddTwo (dotE D Sc [i, i] 0) (dotE D Sc [i, i] 1)
      (crossE D Sc [i, i] 0) := oddTwo_block D Sc [] [] i hi
  apply OddNilHecke.Intertwiner.error_polynomial _ _ _ h.t_t
    (by rw [h.u_v, neg_add_cancel]) h.t_u h.u_t
  intro m hm
  have hp := ha i m hm
  rw [hi, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one] at hp
  rw [← ZMod.natCast_eq_zero_iff_even, ← ZMod.natCast_eq_zero_iff_even, hp]

/-- The repeated-odd error vanishes in the existing prepend tensor, for every left multiplier
and every element of the prescribed shifted coefficient. No cancellation or projectivity is used. -/
theorem repeatedOddError_tmul_zero (i : I) (hi : D.parity i = 1)
    (β : Multiset I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
    (r : Hn D Sc 2) (b : (qCoefficient D Sc i β a ha 0).toSVec) :
    InductionAlong.Ind.tmul
      ((r * FiniteHomMatrix.single (⟨[i, i], rfl⟩ : Word I 2) ⟨[i, i], rfl⟩
        (repeatedOddError D Sc i a)) •
        InductionAlong.unitGen (prependAlgebra D Sc i 1 : Hn D Sc 1 →ₙ+* Hn D Sc 2)) b = 0 := by
  let K := if Even (a i).natDegree then
    OddNilHecke.Intertwiner.error (dotE D Sc [i, i] 0) (dotE D Sc [i, i] 1)
      (crossE D Sc [i, i] 0)
    else OddNilHecke.Intertwiner.oddError (dotE D Sc [i, i] 0) (dotE D Sc [i, i] 1)
      (crossE D Sc [i, i] 0)
  have he : FiniteHomMatrix.single (⟨[i, i], rfl⟩ : Word I 2) ⟨[i, i], rfl⟩
      (repeatedOddError D Sc i a) =
      FiniteHomMatrix.single (⟨[i, i], rfl⟩ : Word I 2) ⟨[i, i], rfl⟩ K *
        prependAlgebra D Sc i 1 (cyclotomicGenerator D Sc a (⟨[i], rfl⟩ : Word I 1)) := by
    rw [prepend_generator_single, FiniteHomMatrix.single_mul_single]
    exact congrArg (FiniteHomMatrix.single (⟨[i, i], rfl⟩ : Word I 2) ⟨[i, i], rfl⟩)
      (repeatedOddError_factor D Sc i hi a ha)
  rw [he, ← mul_assoc]
  exact prepend_generator_tmul_zero D Sc i β a ha 0 ⟨[i], rfl⟩ _ b
end OddMath.QuiverHecke
