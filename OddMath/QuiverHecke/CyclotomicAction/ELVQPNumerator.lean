/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMonicPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVEndpointLeading
import Mathlib.Algebra.Polynomial.Div

/-! # Ordered endpoint–QP numerator normalization

The polynomial here uses append QP factors, not full reverse-chain norm factors.
Its endpoint factor is kept on the left in endomorphism multiplication.
This is the numerator for the right-division step of
`DeformedBoundaryDivision.md` §3 and §5.
-/
noncomputable section
open CategoryTheory Polynomial
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The old dot is constant and the last dot is the polynomial variable. -/
def appendQPPolynomialFactor (i : I) (v : List I) (b : ℕ) :
    Polynomial (End ((pres D Sc).obj (ob D (v ++ [i])))) :=
  let j := v.getD b i
  let a := dotE D Sc (v ++ [i]) b
  if j = i then
    if D.parity i = 1 then C (a ^ 2) + X ^ 2 else -1
  else if D.d i j = 0 then C (algebraMap k _ (Sc.t i j : k))
  else IntertwinerMeet.qLeft (C a) X (D.dn j i) (D.dn i j)
    (Sc.t j i : k) (Sc.t i j : k) (fun p q => Sc.s i j q p)

theorem appendQPPolynomialFactor_leadingCoeff (i : I) (v : List I) (b : ℕ) :
    (appendQPPolynomialFactor D Sc i v b).leadingCoeff =
      algebraMap k _ (appendQPUnit D Sc i (v.getD b i) : k) := by
  unfold appendQPPolynomialFactor appendQPUnit
  dsimp only
  split_ifs with hj hp hd
  · have hm := monic_X_pow_add_C (dotE D Sc (v ++ [i]) b ^ 2) (by decide : (2 : ℕ) ≠ 0)
    simpa only [add_comm, Units.val_one, map_one] using hm.leadingCoeff
  · simp
  · simp
  · have hn : 0 < D.dn i (v.getD b i) := by
      have hc := D.dn_cast (Ne.symm hj)
      omega
    exact qLeft_polynomial_leadingCoeff _ _ _ hn _ _ _

def normalizedAppendQPPolynomialFactor (i : I) (v : List I) (b : ℕ) :
    Polynomial (End ((pres D Sc).obj (ob D (v ++ [i])))) :=
  C (algebraMap k _ ((appendQPUnit D Sc i (v.getD b i))⁻¹ : kˣ)) *
    appendQPPolynomialFactor D Sc i v b

theorem normalizedAppendQPPolynomialFactor_monic (i : I) (v : List I) (b : ℕ) :
    (normalizedAppendQPPolynomialFactor D Sc i v b).Monic := by
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [appendQPPolynomialFactor_leadingCoeff, ← map_mul]
  simp

/-- Ordered append-QP product, with inverse scalar units in each factor. -/
def normalizedAppendQPPolynomial (i : I) (v : List I) :
    Polynomial (End ((pres D Sc).obj (ob D (v ++ [i])))) :=
  ((List.range v.length).map (normalizedAppendQPPolynomialFactor D Sc i v)).prod

theorem normalizedAppendQPPolynomial_monic (i : I) (v : List I) :
    (normalizedAppendQPPolynomial D Sc i v).Monic := by
  have H (l : List ℕ) :
      ((l.map (normalizedAppendQPPolynomialFactor D Sc i v)).prod).Monic := by
    induction l with
    | nil => exact monic_one
    | cons b l ih =>
      exact (normalizedAppendQPPolynomialFactor_monic D Sc i v b).mul ih
  exact H _

/-- The endpoint polynomial remains on the left; no commutative End instance is used. -/
def normalizedEndpointQPPolynomial (i : I) (v : List I) :
    Polynomial (End (obj D Sc cutoff (v ++ [i]))) :=
  movingELVPolynomial D Sc cutoff i v *
    (normalizedAppendQPPolynomial D Sc i v).map (affineUnitEndHom D Sc cutoff _)

theorem normalizedEndpointQPPolynomial_monic (i : I) (v : List I) :
    (normalizedEndpointQPPolynomial D Sc cutoff i v).Monic :=
  (movingELVPolynomial_monic D Sc cutoff i v).mul
    ((normalizedAppendQPPolynomial_monic D Sc i v).map _)

theorem appendOldDot_pow_commute (i : I) (v : List I) (b : ℕ) (hb : b < v.length)
    (n : ℕ) (hn : (n : ZMod 2) * D.parity (v.getD b i) = 0) :
    Commute (dotE D Sc (v ++ [i]) b ^ n) (dotE D Sc (v ++ [i]) v.length) := by
  have hv : v = v.take b ++ [v.getD b i] ++ v.drop (b + 1) := by
    induction v generalizing b with
    | nil => simp at hb
    | cons j v ih =>
      cases b with
      | zero => simp
      | succ b => simpa using congrArg (List.cons j) (ih b (by simpa using hb) (by simpa using hn))
  have h := norm_oldDot_pow_commute D Sc (v.take b) (v.drop (b + 1)) (v.getD b i) i n hn
  rw [← hv] at h
  simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hb), List.length_drop,
    show b + 1 + (v.length - (b + 1)) = v.length by omega] using h

theorem appendQPPolynomialFactor_coeffCommute (i : I) (v : List I) (b : ℕ)
    (hb : b < v.length) :
    NormCoeffCommute (dotE D Sc (v ++ [i]) v.length)
      (appendQPPolynomialFactor D Sc i v b) := by
  have hc (n : ℕ) (hn : (n : ZMod 2) * D.parity (v.getD b i) = 0) :
      NormCoeffCommute (dotE D Sc (v ++ [i]) v.length)
        ((C (dotE D Sc (v ++ [i]) b) : Polynomial _) ^ n) := by
    simpa only [← map_pow] using NormCoeffCommute.const
      (appendOldDot_pow_commute D Sc i v b hb n hn)
  have hx := NormCoeffCommute.X (x := dotE D Sc (v ++ [i]) v.length)
  unfold appendQPPolynomialFactor
  dsimp only
  split_ifs with hj hp hd
  · have h2 := hc 2 (by rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul])
    exact (by simpa only [map_pow] using h2.add (hx.pow 2))
  · have ho : NormCoeffCommute (dotE D Sc (v ++ [i]) v.length) (1 : Polynomial _) := by
      convert NormCoeffCommute.const (Commute.one_left (dotE D Sc (v ++ [i]) v.length)) using 1
      exact map_one C |>.symm
    exact ho.neg
  · exact NormCoeffCommute.const (Algebra.commutes _ _)
  · unfold IntertwinerMeet.qLeft
    apply NormCoeffCommute.add
    · apply NormCoeffCommute.sum
      intro p _
      apply NormCoeffCommute.sum
      intro q _
      by_cases hs : Sc.s i (v.getD b i) q p = 0
      · simp only [hs, zero_smul]
        simpa using (NormCoeffCommute.const (Commute.zero_left
          (dotE D Sc (v ++ [i]) v.length)))
      · apply NormCoeffCommute.smul
        apply NormCoeffCommute.mul _ (hx.pow q)
        exact hc p (zmod_two_eq_zero_of_ne_one fun hp =>
          hs ((Sc.s_symm _ _ _ _).trans (Sc.s_eq_zero _ _ _ _ hp)))
    · exact ((hc _ (dn_mul_parity D (v.getD b i) i)).smul _).add ((hx.pow _).smul _)

theorem appendQPPolynomialFactor_eval (i : I) (v : List I) (b : ℕ)
    (hb : b < v.length) :
    (appendQPPolynomialFactor D Sc i v b).eval₂ (RingHom.id _)
      (dotE D Sc (v ++ [i]) v.length) = appendQPFactor D Sc i v (v.getD b i) b := by
  unfold appendQPPolynomialFactor
  dsimp only
  split_ifs with hj hp hd
  · rw [hj, appendQPFactor_odd D Sc i hp v b hb hj]
    simp only [eval₂_add, eval₂_C, RingHom.id_apply, eval₂_X_pow]
  · simp only [appendQPFactor, hj, hp, ↓reduceIte, eval₂_neg, eval₂_one]
  · simp only [appendQPFactor, hj, qPoly, hd, ↓reduceIte, eval₂_C,
      RingHom.id_apply, Algebra.algebraMap_eq_smul_one]
  · rw [eval₂_qLeft]
    simp only [appendQPFactor, hj, ↓reduceIte, qPoly, hd]
    unfold IntertwinerMeet.qLeft
    rw [Finset.sum_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro p _
      by_cases hs : Sc.s i (v.getD b i) q p = 0
      · simp only [hs, zero_smul]
      · have hn : (p : ZMod 2) * D.parity (v.getD b i) = 0 :=
          zmod_two_eq_zero_of_ne_one fun hp =>
            hs ((Sc.s_symm _ _ _ _).trans (Sc.s_eq_zero _ _ _ _ hp))
        rw [(appendOldDot_pow_commute D Sc i v b hb p hn).pow_right q |>.eq]
    · exact add_comm _ _

theorem normalizedAppendQPPolynomial_list_coeffCommute (i : I) (v : List I)
    (l : List ℕ) (hl : ∀ b ∈ l, b < v.length) :
    NormCoeffCommute (dotE D Sc (v ++ [i]) v.length)
      ((l.map (normalizedAppendQPPolynomialFactor D Sc i v)).prod) := by
  induction l with
  | nil =>
    change NormCoeffCommute _ 1
    rw [← C_1]
    exact NormCoeffCommute.const (Commute.one_left _)
  | cons b l ih =>
    exact ((NormCoeffCommute.const (Algebra.commutes _ _)).mul
      (appendQPPolynomialFactor_coeffCommute D Sc i v b (hl b (by simp)))).mul
      (ih fun a ha => hl a (by simp [ha]))

theorem normalizedAppendQPPolynomial_coeffCommute (i : I) (v : List I) :
    NormCoeffCommute (dotE D Sc (v ++ [i]) v.length)
      (normalizedAppendQPPolynomial D Sc i v) :=
  normalizedAppendQPPolynomial_list_coeffCommute D Sc i v _
    (fun _ hb => List.mem_range.mp hb)

def appendQPInverseUnit (i : I) (v : List I) : kˣ :=
  ((List.range v.length).map fun b => (appendQPUnit D Sc i (v.getD b i))⁻¹).prod

theorem normalizedAppendQPPolynomial_eval (i : I) (v : List I) :
    (normalizedAppendQPPolynomial D Sc i v).eval₂ (RingHom.id _)
      (dotE D Sc (v ++ [i]) v.length) =
      algebraMap k _ (appendQPInverseUnit D Sc i v : k) * appendQPProduct D Sc i v := by
  have H (l : List ℕ) (hl : ∀ b ∈ l, b < v.length) :
      ((l.map (normalizedAppendQPPolynomialFactor D Sc i v)).prod).eval₂ (RingHom.id _)
        (dotE D Sc (v ++ [i]) v.length) =
      algebraMap k _ (((l.map fun b => (appendQPUnit D Sc i (v.getD b i))⁻¹).prod : kˣ) : k) *
        ((l.map fun b => appendQPFactor D Sc i v (v.getD b i) b).prod) := by
    induction l with
    | nil => simp
    | cons b l ih =>
      rw [List.map_cons, List.prod_cons]
      have ht := normalizedAppendQPPolynomial_list_coeffCommute D Sc i v l
        (fun a ha => hl a (by simp [ha]))
      rw [ht.eval_mul, ih (fun a ha => hl a (by simp [ha]))]
      have he : (normalizedAppendQPPolynomialFactor D Sc i v b).eval₂ (RingHom.id _)
          (dotE D Sc (v ++ [i]) v.length) =
          algebraMap k _ ((appendQPUnit D Sc i (v.getD b i))⁻¹ : kˣ) *
            appendQPFactor D Sc i v (v.getD b i) b := by
        unfold normalizedAppendQPPolynomialFactor
        rw [← Polynomial.algebraMap_apply, ← Algebra.smul_def, eval₂_id, eval_smul,
          ← eval₂_id, appendQPPolynomialFactor_eval D Sc i v b (hl b (by simp)), Algebra.smul_def]
      rw [he]
      simp only [List.map_cons, List.prod_cons, Units.val_mul, map_mul]
      rw [mul_assoc, ← mul_assoc (appendQPFactor D Sc i v (v.getD b i) b),
        ← Algebra.commutes, ← mul_assoc, ← mul_assoc]
      exact mul_assoc _ _ _
  exact H _ (fun b hb => List.mem_range.mp hb)

/-- Endomorphism-ring order is endpoint ELV times the normalized append-QP product. -/
def normalizedEndpointQPNumerator (i : I) (v : List I) : End (obj D Sc cutoff (v ++ [i])) :=
  affineUnitEndHom D Sc cutoff (v ++ [i])
    (algebraMap k _ (appendQPInverseUnit D Sc i v : k) * appendQPProduct D Sc i v) ≫
      endpointELV D Sc cutoff i v

/-- Evaluation recovers the literal ordered numerator, with its explicit inverse unit. -/
theorem normalizedEndpointQPPolynomial_eval (i : I) (v : List I) :
    (normalizedEndpointQPPolynomial D Sc cutoff i v).eval₂ (RingHom.id _)
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) =
      normalizedEndpointQPNumerator D Sc cutoff i v := by
  have hc : NormCoeffCommute
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length))
      ((normalizedAppendQPPolynomial D Sc i v).map (affineUnitEndHom D Sc cutoff _)) := by
    intro n
    simpa only [coeff_map] using
      ((normalizedAppendQPPolynomial_coeffCommute D Sc i v) n).map
        (affineUnitEndHom D Sc cutoff _)
  unfold normalizedEndpointQPPolynomial
  rw [hc.eval_mul, movingELVPolynomial_eval]
  change _ ≫ endpointELV D Sc cutoff i v = _ ≫ endpointELV D Sc cutoff i v
  congr 1
  rw [eval₂_map, RingHom.id_comp, eval₂_at_apply]
  exact congrArg (affineUnitEndHom D Sc cutoff _) (normalizedAppendQPPolynomial_eval D Sc i v)

/-- Polynomial right division with the concrete normalized numerator on the left.
This is a polynomial identity; evaluating arbitrary quotients requires their
coefficient commutation or the corresponding signed old-Hom action. -/
theorem normalizedEndpointQPPolynomial_rightDivision (i : I) (v : List I)
    (p : Polynomial (End (obj D Sc cutoff (v ++ [i])))) :
    p %ₘ normalizedEndpointQPPolynomial D Sc cutoff i v +
      normalizedEndpointQPPolynomial D Sc cutoff i v *
        (p /ₘ normalizedEndpointQPPolynomial D Sc cutoff i v) = p :=
  modByMonic_add_div _ _

theorem normalizedEndpointQPPolynomial_remainder_bound (i : I) (v : List I)
    (p : Polynomial (End (obj D Sc cutoff (v ++ [i])))) :
    p %ₘ normalizedEndpointQPPolynomial D Sc cutoff i v = 0 ∨
      (p %ₘ normalizedEndpointQPPolynomial D Sc cutoff i v).degree <
        (normalizedEndpointQPPolynomial D Sc cutoff i v).degree := by
  nontriviality (End (obj D Sc cutoff (v ++ [i])))
  exact Or.inr (degree_modByMonic_lt _ (normalizedEndpointQPPolynomial_monic D Sc cutoff i v))

/-- Right moving powers are evaluated on the right of the endpoint–QP numerator.
No commutation of the endpoint ELV coefficients with the moving dot is asserted. -/
theorem normalizedEndpointQPPolynomial_eval_right_power (i : I) (v : List I) (n : ℕ) :
    (normalizedEndpointQPPolynomial D Sc cutoff i v * X ^ n).eval₂ (RingHom.id _)
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) =
      normalizedEndpointQPNumerator D Sc cutoff i v *
      affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length) ^ n := by
  rw [((NormCoeffCommute.X).pow n).eval_mul, normalizedEndpointQPPolynomial_eval, eval₂_X_pow]

/-- Scalar normalization preserves the prescribed chronological numerator. -/
theorem normalizedEndpointQPNumerator_eq (i : I) (v : List I) :
    normalizedEndpointQPNumerator D Sc cutoff i v =
      (appendQPInverseUnit D Sc i v : k) •
        (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v) := by
  unfold normalizedEndpointQPNumerator
  rw [← Algebra.smul_def]
  change affineUnit D Sc cutoff _ _ ((appendQPInverseUnit D Sc i v : k) •
    appendQPProduct D Sc i v) ≫ endpointELV D Sc cutoff i v = _
  rw [map_smul, Linear.smul_comp]

/-- Cancellation is on the old-only append quotient, not the full-content quotient. -/
theorem normalizedEndpointQPNumerator_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (normalizedEndpointQPNumerator D Sc cutoff i v ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  rw [normalizedEndpointQPNumerator_eq, Linear.smul_comp, map_smul] at hh
  apply appendProjection_qp_endpointELV_regular D Sc cutoff i v w h
  rw [← Category.assoc]
  exact (appendQPInverseUnit D Sc i v).isUnit.smul_eq_zero.mp hh

end OddMath.QuiverHecke.ELVOld
