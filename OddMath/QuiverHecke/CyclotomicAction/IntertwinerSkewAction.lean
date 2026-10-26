/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightPolynomial
import Mathlib.Algebra.SkewPolynomial.Basic

/-!
# Parity-skew polynomials on the induced quotients

The right polynomial action in KKO I, Proposition 8.4. Coefficients are
written first: `c X^m` applies the coefficient and then the dots. Thus the
representation takes values in the ordinary opposite endomorphism ring,
not the super-opposite. The relation is `X c = φ(c) X`, where
`φ(c) = (-1)^(p(i)|c|) c`; no square-zero relation is imposed on `X`.
The coefficient action on the target retains its existing parity shift.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The parity sign is a ring endomorphism of the existing coefficient algebra. -/
def coefficientParityHom (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (p : ZMod 2) :
    CyclotomicAlgebra D Sc a n →+* CyclotomicAlgebra D Sc a n where
  toFun := (cyclotomicSuperspace D Sc a ha n).sgn p
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [SVec.sgn_apply_of_mem p (show (1 : CyclotomicAlgebra D Sc a n) ∈
      cyclotomicParity D Sc a ha n 0 from SetLike.GradedOne.one_mem)]
    simp
  map_mul' b c := by
    induction b using SuperBimodule.alg_induction_on (cyclotomicParity D Sc a ha n) with
    | zero => simp
    | add b b' hb hb' => simp only [add_mul, map_add, hb, hb']
    | hom q b hb =>
      induction c using SuperBimodule.alg_induction_on (cyclotomicParity D Sc a ha n) with
      | zero => simp
      | add c c' hc hc' => simp only [mul_add, map_add, hc, hc']
      | hom r c hc =>
        have hbc : b * c ∈ cyclotomicParity D Sc a ha n (q + r) :=
          SetLike.GradedMul.mul_mem hb hc
        rw [SVec.sgn_apply_of_mem p hbc,
          SVec.sgn_apply_of_mem p hb, SVec.sgn_apply_of_mem p hc]
        simp only [add_mul, sign_add, smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [mul_comm (sign k (q * p))]

/-- Powers of the parity twist, as the action required by Mathlib skew polynomials. -/
@[instance_reducible] def coefficientParityAction (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    MulSemiringAction (Multiplicative ℕ) (CyclotomicAlgebra D Sc a n) where
  smul m := coefficientParityHom D Sc a ha n ((m.toAdd : ZMod 2) * D.parity i)
  smul_zero m := map_zero _
  smul_add m := map_add _
  smul_one m := map_one _
  smul_mul m := map_mul _
  one_smul b := by
    change (cyclotomicSuperspace D Sc a ha n).sgn ((0 : ZMod 2) * D.parity i) b = b
    simp
  mul_smul m l b := by
    change (cyclotomicSuperspace D Sc a ha n).sgn
      (((m.toAdd + l.toAdd : ℕ) : ZMod 2) * D.parity i) b =
      ((cyclotomicSuperspace D Sc a ha n).sgn ((m.toAdd : ZMod 2) * D.parity i))
        ((cyclotomicSuperspace D Sc a ha n).sgn ((l.toAdd : ZMod 2) * D.parity i) b)
    rw [← LinearMap.comp_apply, SVec.sgn_comp_sgn, Nat.cast_add, add_mul]

/-- The exponent action is the corresponding total parity sign. -/
theorem coefficientParityAction_smul (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n m : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    letI := coefficientParityAction D Sc i a ha n
    Multiplicative.ofAdd m • c =
      coefficientParityHom D Sc a ha n ((m : ZMod 2) * D.parity i) c := rfl

/-- The coefficient right action, valued in the ordinary opposite ring. -/
def sourceRightCoefficientRing (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    CyclotomicAlgebra D Sc a n →+* (Module.End k (qSourceSpace D Sc i a ha n))ᵐᵒᵖ where
  toFun c := MulOpposite.op (sourceRightCoefficientLinear D Sc i a ha n c)
  map_zero' := by
    apply MulOpposite.unop_injective
    ext z
    exact LinearMap.congr_fun (sourceRightCoefficient_zero D Sc i a n) z
  map_add' b c := by
    apply MulOpposite.unop_injective
    ext z
    exact LinearMap.congr_fun (sourceRightCoefficient_add D Sc i a n b c) z
  map_one' := by
    apply MulOpposite.unop_injective
    ext z
    exact LinearMap.congr_fun (sourceRightCoefficient_one D Sc i a n) z
  map_mul' b c := by
    apply MulOpposite.unop_injective
    ext z
    exact LinearMap.congr_fun (sourceRightCoefficient_mul D Sc i a n b c) z

/-- The single-dot skew relation, with coefficient parity twisting. -/
theorem sourceRightCoefficientRing_twist (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    sourceRightCoefficientRing D Sc i a ha n (coefficientParityHom D Sc a ha n (D.parity i) c) *
        MulOpposite.op (sourceRightDotLinear D Sc i a ha n) =
      MulOpposite.op (sourceRightDotLinear D Sc i a ha n) * sourceRightCoefficientRing D Sc i a ha n c := by
  induction c using SuperBimodule.alg_induction_on (cyclotomicParity D Sc a ha n) with
  | zero => simp
  | add b c hb hc => simp only [map_add, add_mul, mul_add, hb, hc]
  | hom q c hc =>
    have hs : coefficientParityHom D Sc a ha n (D.parity i) c =
        sign k (D.parity i * q) • c := by
      exact (SVec.sgn_apply_of_mem (D.parity i) hc).trans (by rw [mul_comm])
    have h := sourceRightDot_coefficient D Sc i a ha n q c hc
    rcases parity_eq_zero_or_one (D.parity i * q) with he | he
    · simp only [he, sign_zero, one_smul] at hs h
      rw [hs]
      exact MulOpposite.unop_injective (by exact h)
    · simp only [he, sign_one, neg_one_smul] at hs h
      rw [hs, map_neg]
      apply MulOpposite.unop_injective
      change sourceRightDotLinear D Sc i a ha n * (-sourceRightCoefficientLinear D Sc i a ha n c) = _
      rw [mul_neg, Module.End.mul_eq_comp, h, neg_neg]
      rfl

/-- The coefficient right action, valued in the ordinary opposite ring. -/
def targetRightCoefficientRing (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    CyclotomicAlgebra D Sc a n →+* (Module.End k (qTargetSpace D Sc i β a ha n))ᵐᵒᵖ where
  toFun c := MulOpposite.op (targetRightCoefficientLinear D Sc i β a ha n c)
  map_zero' := by
    apply MulOpposite.unop_injective
    ext z
    exact LinearMap.congr_fun (targetRightCoefficient_zero D Sc i β a ha n) z
  map_add' b c := by
    apply MulOpposite.unop_injective
    ext z
    exact LinearMap.congr_fun (targetRightCoefficient_add D Sc i β a ha n b c) z
  map_one' := by
    apply MulOpposite.unop_injective
    ext z
    exact LinearMap.congr_fun (targetRightCoefficient_one D Sc i β a ha n) z
  map_mul' b c := by
    apply MulOpposite.unop_injective
    ext z
    exact LinearMap.congr_fun (targetRightCoefficient_mul D Sc i β a ha n b c) z

/-- The single-dot skew relation, with coefficient parity twisting. -/
theorem targetRightCoefficientRing_twist (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    targetRightCoefficientRing D Sc i β a ha n (coefficientParityHom D Sc a ha n (D.parity i) c) *
        MulOpposite.op (targetRightDotLinear D Sc i β a ha n) =
      MulOpposite.op (targetRightDotLinear D Sc i β a ha n) * targetRightCoefficientRing D Sc i β a ha n c := by
  induction c using SuperBimodule.alg_induction_on (cyclotomicParity D Sc a ha n) with
  | zero => simp
  | add b c hb hc => simp only [map_add, add_mul, mul_add, hb, hc]
  | hom q c hc =>
    have hs : coefficientParityHom D Sc a ha n (D.parity i) c =
        sign k (D.parity i * q) • c := by
      exact (SVec.sgn_apply_of_mem (D.parity i) hc).trans (by rw [mul_comm])
    have h := targetRightDot_coefficient D Sc i β a ha n q c hc
    rcases parity_eq_zero_or_one (D.parity i * q) with he | he
    · simp only [he, sign_zero, one_smul] at hs h
      rw [hs]
      exact MulOpposite.unop_injective (by exact h)
    · simp only [he, sign_one, neg_one_smul] at hs h
      rw [hs, map_neg]
      apply MulOpposite.unop_injective
      change targetRightDotLinear D Sc i β a ha n * (-targetRightCoefficientLinear D Sc i β a ha n c) = _
      rw [mul_neg, Module.End.mul_eq_comp, h, neg_neg]
      rfl

private theorem skew_power_relation {A B : Type*} [Ring A] [Ring B]
    [MulSemiringAction (Multiplicative ℕ) A] (f : A →+* B) (T : B)
    (h : ∀ c, f (Multiplicative.ofAdd 1 • c) * T = T * f c) (m : ℕ) (c : A) :
    f (Multiplicative.ofAdd m • c) * T ^ m = T ^ m * f c := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    have hm : Multiplicative.ofAdd (m + 1) =
        Multiplicative.ofAdd m * Multiplicative.ofAdd 1 := rfl
    rw [hm, mul_smul, pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc]

private def dotPowers {B : Type*} [Monoid B] (T : B) : Multiplicative ℕ →* B where
  toFun m := T ^ m.toAdd
  map_one' := pow_zero T
  map_mul' m l := pow_add T m.toAdd l.toAdd

/-- Multiplication-preserving right representation of the parity-skew polynomial ring. -/
def sourceRightSkew (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    letI := coefficientParityAction D Sc i a ha n
    _root_.SkewPolynomial (CyclotomicAlgebra D Sc a n) →+*
      (Module.End k (qSourceSpace D Sc i a ha n))ᵐᵒᵖ := by
  let := coefficientParityAction D Sc i a ha n
  refine SkewMonoidAlgebra.liftNCRingHom (sourceRightCoefficientRing D Sc i a ha n)
    (dotPowers (MulOpposite.op (sourceRightDotLinear D Sc i a ha n))) ?_
  intro c m
  apply skew_power_relation
  intro b
  simpa only [coefficientParityAction_smul, Nat.cast_one, one_mul] using
    sourceRightCoefficientRing_twist D Sc i a ha n b

/-- Coefficient-first normal order applies the coefficient before the dot power. -/
theorem sourceRightSkew_monomial (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n m : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    (sourceRightSkew D Sc i a ha n (_root_.SkewPolynomial.monomial m c)).unop =
      sourceRightDotLinear D Sc i a ha n ^ m * sourceRightCoefficientLinear D Sc i a ha n c := by
  simp [ sourceRightSkew, _root_.SkewPolynomial.monomial_def,
    SkewMonoidAlgebra.liftNCRingHom, SkewMonoidAlgebra.liftNC_single,
    sourceRightCoefficientRing, dotPowers]

/-- Multiplication-preserving right representation of the parity-skew polynomial ring. -/
def targetRightSkew (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    letI := coefficientParityAction D Sc i a ha n
    _root_.SkewPolynomial (CyclotomicAlgebra D Sc a n) →+*
      (Module.End k (qTargetSpace D Sc i β a ha n))ᵐᵒᵖ := by
  let := coefficientParityAction D Sc i a ha n
  refine SkewMonoidAlgebra.liftNCRingHom (targetRightCoefficientRing D Sc i β a ha n)
    (dotPowers (MulOpposite.op (targetRightDotLinear D Sc i β a ha n))) ?_
  intro c m
  apply skew_power_relation
  intro b
  simpa only [coefficientParityAction_smul, Nat.cast_one, one_mul] using
    targetRightCoefficientRing_twist D Sc i β a ha n b

/-- Coefficient-first normal order applies the coefficient before the dot power. -/
theorem targetRightSkew_monomial (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n m : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    (targetRightSkew D Sc i β a ha n (_root_.SkewPolynomial.monomial m c)).unop =
      targetRightDotLinear D Sc i β a ha n ^ m * targetRightCoefficientLinear D Sc i β a ha n c := by
  simp [ targetRightSkew, _root_.SkewPolynomial.monomial_def,
    SkewMonoidAlgebra.liftNCRingHom, SkewMonoidAlgebra.liftNC_single,
    targetRightCoefficientRing, dotPowers]

/-- Dot-first order is coefficient-first order with the `m`th parity twist. -/
theorem sourceRightSkew_dotFirst (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n m : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    (sourceRightSkew D Sc i a ha n (_root_.SkewPolynomial.monomial m
      (coefficientParityHom D Sc a ha n ((m : ZMod 2) * D.parity i) c))).unop =
      sourceRightMonomial D Sc i a ha n m c := by
  let := coefficientParityAction D Sc i a ha n
  have h := skew_power_relation (sourceRightCoefficientRing D Sc i a ha n)
    (MulOpposite.op (sourceRightDotLinear D Sc i a ha n))
    (fun b => by simpa only [coefficientParityAction_smul, Nat.cast_one, one_mul] using
      sourceRightCoefficientRing_twist D Sc i a ha n b) m c
  rw [sourceRightSkew_monomial]
  exact congrArg MulOpposite.unop h

/-- The inverse order conversion uses the same twist, since it is involutive. -/
theorem sourceRightSkew_coefficientFirst (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n m : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    (sourceRightSkew D Sc i a ha n (_root_.SkewPolynomial.monomial m c)).unop =
      sourceRightMonomial D Sc i a ha n m
        (coefficientParityHom D Sc a ha n ((m : ZMod 2) * D.parity i) c) := by
  have h := sourceRightSkew_dotFirst D Sc i a ha n m
    (coefficientParityHom D Sc a ha n ((m : ZMod 2) * D.parity i) c)
  simpa only [coefficientParityHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    SVec.sgn_sgn_apply] using h

/-- The right-action multiplication law is reverse composition of endomorphisms. -/
theorem sourceRightSkew_mul (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    letI := coefficientParityAction D Sc i a ha n
    ∀ f g : _root_.SkewPolynomial (CyclotomicAlgebra D Sc a n),
      (sourceRightSkew D Sc i a ha n (f * g)).unop =
        (sourceRightSkew D Sc i a ha n g).unop * (sourceRightSkew D Sc i a ha n f).unop := by
  let := coefficientParityAction D Sc i a ha n
  intro f g
  exact congrArg MulOpposite.unop ((sourceRightSkew D Sc i a ha n).map_mul f g)

/-- Dot-first order is coefficient-first order with the `m`th parity twist. -/
theorem targetRightSkew_dotFirst (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n m : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    (targetRightSkew D Sc i β a ha n (_root_.SkewPolynomial.monomial m
      (coefficientParityHom D Sc a ha n ((m : ZMod 2) * D.parity i) c))).unop =
      targetRightMonomial D Sc i β a ha n m c := by
  let := coefficientParityAction D Sc i a ha n
  have h := skew_power_relation (targetRightCoefficientRing D Sc i β a ha n)
    (MulOpposite.op (targetRightDotLinear D Sc i β a ha n))
    (fun b => by simpa only [coefficientParityAction_smul, Nat.cast_one, one_mul] using
      targetRightCoefficientRing_twist D Sc i β a ha n b) m c
  rw [targetRightSkew_monomial]
  exact congrArg MulOpposite.unop h

/-- The inverse order conversion uses the same twist, since it is involutive. -/
theorem targetRightSkew_coefficientFirst (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n m : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    (targetRightSkew D Sc i β a ha n (_root_.SkewPolynomial.monomial m c)).unop =
      targetRightMonomial D Sc i β a ha n m
        (coefficientParityHom D Sc a ha n ((m : ZMod 2) * D.parity i) c) := by
  have h := targetRightSkew_dotFirst D Sc i β a ha n m
    (coefficientParityHom D Sc a ha n ((m : ZMod 2) * D.parity i) c)
  simpa only [coefficientParityHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    SVec.sgn_sgn_apply] using h

/-- The right-action multiplication law is reverse composition of endomorphisms. -/
theorem targetRightSkew_mul (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    letI := coefficientParityAction D Sc i a ha n
    ∀ f g : _root_.SkewPolynomial (CyclotomicAlgebra D Sc a n),
      (targetRightSkew D Sc i β a ha n (f * g)).unop =
        (targetRightSkew D Sc i β a ha n g).unop * (targetRightSkew D Sc i β a ha n f).unop := by
  let := coefficientParityAction D Sc i a ha n
  intro f g
  exact congrArg MulOpposite.unop ((targetRightSkew D Sc i β a ha n).map_mul f g)

/-- Q intertwines the two right representations for every skew polynomial. -/
theorem rightSkew_Q (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (f : _root_.SkewPolynomial (CyclotomicAlgebra D Sc a n)) :
    (targetRightSkew D Sc i β a ha n f).unop.comp
        (parityCyclotomicContentQLinear D Sc i β a ha n) =
      (parityCyclotomicContentQLinear D Sc i β a ha n).comp
        (sourceRightSkew D Sc i a ha n f).unop := by
  induction f using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single m c =>
    change (targetRightSkew D Sc i β a ha n (_root_.SkewPolynomial.monomial m.toAdd c)).unop.comp _ =
      (parityCyclotomicContentQLinear D Sc i β a ha n).comp (sourceRightSkew D Sc i a ha n (_root_.SkewPolynomial.monomial m.toAdd c)).unop
    rw [targetRightSkew_coefficientFirst, sourceRightSkew_coefficientFirst]
    exact rightMonomial_Q D Sc i β a ha n m.toAdd _
  | add f g hf hg =>
    rw [(targetRightSkew D Sc i β a ha n).map_add, (sourceRightSkew D Sc i a ha n).map_add]
    simp only [MulOpposite.unop_add, LinearMap.add_comp, LinearMap.comp_add, hf, hg]

end OddMath.QuiverHecke
