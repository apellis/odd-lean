/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Realization.Operators

/-!
# The operators `σ_a = s̃_a + f_a`

Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, §3.4, Theorem 3.8 and its proof, in the corner
`RCP_n` of Definition 3.10 (colours in `I`, Clifford generators only at odd positions).

Words are read from left to right here, while KKT number strands from right to left, so KKT's
position `a + 1` is our position `a`. Accordingly our

  `f_{p,q} = (y_p - y_q)⁻¹ e_{p,q} + (y_p + y_q)⁻¹ c_q c_p ec_{p,q}`

is KKT's `f_{q,p}` (with `e_{p,q}` the sum of the idempotents with equal colours at `p`, `q`, and
`ec_{p,q}` the part where this colour is odd), and `σ_a = s̃_a + f_{a,a+1}`.

The central elements are `R_{a,a+1} = Q̃_{a,a+1} - f_{a,a+1}²`, where `Q̃` is given by a
`PairFn`: a function of two colours and two variables which is natural for automorphisms,
symmetric, and even in the variable of an odd colour (KKT (3.6)).
-/

noncomputable section
open scoped TensorProduct
namespace OddMath.QuiverHecke.Realization

variable {I : Type*} {k : Type*} [CommRing k]

/-! ## Inverses of `y_p ∓ y_q` -/

theorem map_ringInverse {R : Type*} [CommRing R] (e : R ≃+* R) (x : R) :
    e (Ring.inverse x) = Ring.inverse (e x) := by
  by_cases h : IsUnit x
  · have h' : IsUnit (e x) := h.map e
    calc e (Ring.inverse x) = e (Ring.inverse x) * (e x * Ring.inverse (e x)) := by
          rw [Ring.mul_inverse_cancel _ h', mul_one]
      _ = e (Ring.inverse x * x) * Ring.inverse (e x) := by rw [map_mul]; ring
      _ = Ring.inverse (e x) := by rw [Ring.inverse_mul_cancel _ h, map_one, one_mul]
  · have h' : ¬ IsUnit (e x) := fun hu => h (by simpa using hu.map e.symm)
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', map_zero]

theorem ringInverse_neg {R : Type*} [CommRing R] (x : R) :
    Ring.inverse (-x) = -Ring.inverse x := by
  by_cases h : IsUnit x
  · have h' : IsUnit (-x) := h.neg
    calc Ring.inverse (-x) = Ring.inverse (-x) * (x * Ring.inverse x) := by
          rw [Ring.mul_inverse_cancel _ h, mul_one]
      _ = -(Ring.inverse (-x) * -x) * Ring.inverse x := by ring
      _ = -Ring.inverse x := by rw [Ring.inverse_mul_cancel _ h', neg_one_mul]
  · have h' : ¬ IsUnit (-x) := fun hu => h (by simpa using hu.neg)
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', neg_zero]

/-- `(y_p - y_q)⁻¹`, zero for `p = q`. -/
def hS (p q : ℕ) : K k := Ring.inverse (y p - y q)

/-- `(y_p + y_q)⁻¹`. -/
def hA (p q : ℕ) : K k := Ring.inverse (y p + y q)

theorem hS_mul {p q : ℕ} (h : p ≠ q) : hS (k := k) p q * (y p - y q) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_y_sub h)

theorem hA_mul {p q : ℕ} (h : p ≠ q) : hA (k := k) p q * (y p + y q) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_y_add h)

theorem hS_swap (p q : ℕ) : hS (k := k) q p = -hS p q := by
  rw [hS, hS, ← ringInverse_neg, neg_sub]

theorem hA_swap (p q : ℕ) : hA (k := k) q p = hA p q := by
  rw [hA, hA, add_comm]

@[simp] theorem permK_hS (σ : Equiv.Perm ℕ) (p q : ℕ) :
    permK σ (hS (k := k) p q) = hS (σ p) (σ q) := by
  rw [hS, hS, ← AlgEquiv.coe_ringEquiv, map_ringInverse]
  simp

@[simp] theorem permK_hA (σ : Equiv.Perm ℕ) (p q : ℕ) :
    permK σ (hA (k := k) p q) = hA (σ p) (σ q) := by
  rw [hA, hA, ← AlgEquiv.coe_ringEquiv, map_ringInverse]
  simp

theorem reflect_hS (s p q : ℕ) :
    reflect s (hS (k := k) p q) =
      Ring.inverse ((if p = s then -y p else y p) - (if q = s then -y q else y q)) := by
  rw [hS, ← AlgEquiv.coe_ringEquiv, map_ringInverse]
  simp

theorem reflect_hA (s p q : ℕ) :
    reflect s (hA (k := k) p q) =
      Ring.inverse ((if p = s then -y p else y p) + (if q = s then -y q else y q)) := by
  rw [hA, ← AlgEquiv.coe_ringEquiv, map_ringInverse]
  simp

theorem reflect_hS_left {p q : ℕ} (h : q ≠ p) : reflect p (hS (k := k) p q) = -hA p q := by
  rw [reflect_hS, hA, ← ringInverse_neg]
  simp only [h, ite_true, ite_false]
  ring_nf

theorem reflect_hS_right {p q : ℕ} (h : p ≠ q) : reflect q (hS (k := k) p q) = hA p q := by
  rw [reflect_hS, hA]
  simp only [h, ite_true, ite_false, sub_neg_eq_add]

theorem reflect_hS_of_ne {s p q : ℕ} (hp : p ≠ s) (hq : q ≠ s) :
    reflect s (hS (k := k) p q) = hS p q := by
  rw [reflect_hS, hS]
  simp only [hp, hq, ite_false]

theorem reflect_hA_left {p q : ℕ} (h : q ≠ p) : reflect p (hA (k := k) p q) = -hS p q := by
  rw [reflect_hA, hS, ← ringInverse_neg]
  simp only [h, ite_true, ite_false]
  ring_nf

theorem reflect_hA_right {p q : ℕ} (h : p ≠ q) : reflect q (hA (k := k) p q) = hS p q := by
  rw [reflect_hA, hS]
  simp only [h, ite_true, ite_false, ← sub_eq_add_neg]

theorem reflect_hA_of_ne {s p q : ℕ} (hp : p ≠ s) (hq : q ≠ s) :
    reflect s (hA (k := k) p q) = hA p q := by
  rw [reflect_hA, hA]
  simp only [hp, hq, ite_false]

/-! ## Computations with coefficient operators -/

theorem cliff_scalar_assoc (p : ℕ) (f : K k) (X : Module.End k (Coeff k)) :
    cliff p * (scalar f * X) = scalar (reflect p f) * (cliff p * X) := by
  rw [← mul_assoc, cliff_scalar, mul_assoc]

theorem scalar_scalar_assoc (f g : K k) (X : Module.End k (Coeff k)) :
    scalar f * (scalar g * X) = scalar (f * g) * X := by
  rw [← mul_assoc, scalar_mul]

theorem cliff_cliff_assoc (p : ℕ) (X : Module.End k (Coeff k)) :
    cliff p * (cliff p * X) = X := by
  rw [← mul_assoc, cliff_mul_self, one_mul]

theorem cliff_anticomm_assoc {p q : ℕ} (h : p ≠ q) (X : Module.End k (Coeff k)) :
    cliff p * (cliff q * X) = -(cliff q * (cliff p * X)) := by
  rw [← mul_assoc, cliff_anticomm h]
  rw [endNeg_mul, mul_assoc]

/-! ## Functions of two colours -/

/-- KKT's data `Q̃_{i,j}(u,v)` of (3.6), or a central element `R`: a function of two colours
(`none` beyond the end of a word) and two variables, natural for automorphisms of `K` and
symmetric in the two strands. -/
structure PairFn (I : Type*) (k : Type*) [CommRing k] where
  /-- The function. -/
  toFun : Option I → Option I → K k → K k → K k
  map' : ∀ (e : K k ≃ₐ[k] K k) i j u v, e (toFun i j u v) = toFun i j (e u) (e v)
  symm' : ∀ i j u v, toFun j i v u = toFun i j u v

namespace PairFn

variable (Φ : PairFn I k)

/-- Evenness in the variable of an odd colour (KKT (3.6), second condition). -/
def IsEven (par : I → ZMod 2) : Prop :=
  ∀ i j u v, par i = 1 → Φ.toFun (some i) j (-u) v = Φ.toFun (some i) j u v

/-- The value `Φ(ν_p, ν_q)(y_p, y_q)` on the component `ν`. -/
def val (p q : ℕ) (ν : Seq I) : K k := Φ.toFun (ν p) (ν q) (y p) (y q)

theorem permK_val (σ : Equiv.Perm ℕ) (p q : ℕ) (ν : Seq I) :
    permK σ (Φ.val p q (ν ∘ σ)) = Φ.val (σ p) (σ q) ν := by
  simp [val, Φ.map']

theorem val_symm (p q : ℕ) (ν : Seq I) : Φ.val q p ν = Φ.val p q ν := Φ.symm' _ _ _ _

theorem reflect_val {par : I → ZMod 2} (hΦ : Φ.IsEven par) {p q : ℕ} (hpq : p ≠ q) (s : ℕ)
    (ν : Seq I) (hs : oddAt par ν s) : reflect s (Φ.val p q ν) = Φ.val p q ν := by
  obtain ⟨i, hi, hpi⟩ := hs
  rw [val, Φ.map', reflect_y, reflect_y]
  by_cases hp : p = s
  · subst hp
    simp only [ite_true, Ne.symm hpq, ite_false, hi]
    exact hΦ _ _ _ _ hpi
  · by_cases hq : q = s
    · subst hq
      simp only [hp, ite_true, ite_false, hi]
      rw [← Φ.symm', hΦ _ _ _ _ hpi, Φ.symm']
    · simp only [hp, hq, ite_false]

end PairFn

/-! ## The operators `f_{p,q}` -/

variable [DecidableEq I]

/-- `(y_p - y_q)⁻¹` on the components with equal colours at `p` and `q`. -/
def hh (p q : ℕ) (ν : Seq I) : K k := if ν p = ν q then hS p q else 0

variable (par : I → ZMod 2)

/-- `f_{p,q} = h_{p,q} + c_q h_{p,q} c_p` (KKT (3.14), after the proof of Theorem 3.8). -/
def fpq (p q : ℕ) : Module.End k (V k I) :=
  mulK (hh p q) + clif par q * mulK (hh p q) * clif par p

/-- The coefficient operator of `f_{p,q}` on the component `ν`. -/
def fP (p q : ℕ) (ν : Seq I) : Module.End k (Coeff k) :=
  if ν p = ν q then
    scalar (hS p q) + if oddAt par ν p then cliff q * scalar (hS p q) * cliff p else 0
  else 0

omit [DecidableEq I] in
theorem oddAt_congr {ν : Seq I} {p q : ℕ} (h : ν p = ν q) : oddAt par ν p ↔ oddAt par ν q := by
  unfold oddAt; rw [h]

theorem fpq_eq_diag (p q : ℕ) : fpq (k := k) (I := I) par p q = diag (fP par p q) := by
  rw [fpq, mulK, clif, clif, ← diag_mul', ← diag_mul', ← diag_add]
  congr 1
  ext1 ν
  unfold fP hh
  by_cases h : ν p = ν q
  · have hpq := oddAt_congr par h
    by_cases ho : oddAt par ν p
    · simp [h, ho, hpq.mp ho]
    · simp [h, ho, mt hpq.mpr ho]
  · simp [h]

theorem fP_swap {p q : ℕ} (h : p ≠ q) (ν : Seq I) : fP (k := k) par q p ν = -fP par p q ν := by
  unfold fP
  by_cases hν : ν p = ν q
  · have hpq := oddAt_congr par hν
    rw [ite_eq_left hν.symm, ite_eq_left hν]
    by_cases ho : oddAt par ν p
    · rw [ite_eq_left (hpq.mp ho), ite_eq_left ho, hS_swap, mul_assoc, mul_assoc,
        cliff_scalar_assoc, cliff_scalar_assoc, map_neg, reflect_hS_left (Ne.symm h), reflect_hS_right h, neg_neg,
        cliff_anticomm h, scalar_neg, endMul_neg]
      abel
    · rw [ite_eq_right (mt hpq.mpr ho), ite_eq_right ho, hS_swap, scalar_neg]
      abel
  · rw [ite_eq_right (Ne.symm hν), ite_eq_right hν, endNeg_zero]

theorem fpq_swap {p q : ℕ} (h : p ≠ q) :
    fpq (k := k) (I := I) par q p = -fpq par p q := by
  rw [fpq_eq_diag, fpq_eq_diag, ← diag_neg]
  exact congrArg diag (funext (fP_swap par h))

theorem hh_comp (p q : ℕ) (ν : Seq I) (σ : Equiv.Perm ℕ) :
    permK σ (hh (k := k) p q (ν ∘ σ)) = hh (σ p) (σ q) ν := by
  unfold hh
  simp only [Function.comp_apply]
  split_ifs <;> simp

/-- Covariance of `f_{p,q}` under `s̃_a` (used in the proof of Theorem 3.8). -/
theorem tw_fpq (a : ℕ) (r : Seq I → K k)
    (hr : ∀ s ν, oddAt par ν s → reflect s (r ν) = r ν) (p q : ℕ) :
    tw a r * fpq par p q = fpq par (sw a p) (sw a q) * tw a r := by
  have h1 := tw_mulK a r (hh (k := k) (I := I) p q)
  have h2 := tw_clif par a r p (hr _)
  have h3 := tw_clif par a r q (hr _)
  have hh' : (fun ν : Seq I => permK (sw a) (hh (k := k) p q (ν ∘ sw a))) =
      hh (sw a p) (sw a q) :=
    funext fun ν => hh_comp p q ν (sw a)
  rw [hh'] at h1
  rw [fpq, fpq, mul_add, add_mul, h1, ← mul_assoc, ← mul_assoc, h3, mul_assoc (clif par _),
    h1, mul_assoc, mul_assoc, h2, ← mul_assoc, ← mul_assoc]

/-! ## The relations among the `f_{p,q}` -/

theorem hS_cycle {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    hS (k := k) a b * hS b c + hS b c * hS c a + hS c a * hS a b = 0 := by
  have e1 := hS_mul (k := k) hab
  have e2 := hS_mul (k := k) hbc
  have e3 := hS_mul (k := k) hca
  linear_combination (-(hS a b * hS b c)) * e3 + (-(hS b c * hS c a)) * e1 +
    (-(hS c a * hS a b)) * e2

theorem cliff_word {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) :
    cliff (k := k) b * (cliff a * (cliff c * cliff b)) = cliff a * cliff c := by
  rw [← mul_assoc, cliff_anticomm hab.symm, endNeg_mul, mul_assoc, cliff_anticomm_assoc hbc,
    cliff_mul_self, mul_one, endMul_neg]
  abel

/-- `f_{p,q}` on a component where `p` and `q` have the same odd colour. -/
def fO (p q : ℕ) : Module.End k (Coeff k) :=
  scalar (hS p q) + cliff q * scalar (hS p q) * cliff p

/-- The sum of the four conjugations in KKT's proof of (3.15). -/
def tri (a b c : ℕ) (X : Module.End k (Coeff k)) : Module.End k (Coeff k) :=
  X + cliff b * X * cliff a + cliff c * X * cliff b + cliff a * X * cliff c

theorem tri_add (a b c : ℕ) (X Y : Module.End k (Coeff k)) :
    tri a b c (X + Y) = tri a b c X + tri a b c Y := by
  simp only [tri, mul_add, add_mul]
  abel

theorem tri_rot (a b c : ℕ) (X : Module.End k (Coeff k)) : tri b c a X = tri a b c X := by
  simp only [tri]
  abel

theorem tri_zero (a b c : ℕ) : tri (k := k) a b c 0 = 0 := by
  simp [tri]

set_option linter.unusedSimpArgs false in
/-- KKT, proof of (3.15): `f_{a,b} f_{b,c}` is the sum of four conjugates of
`h_{a,b} h_{b,c}`. -/
theorem fO_mul_fO {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    fO a b * fO b c = tri a b c (scalar (hS (k := k) a b * hS b c)) := by
  have hca' := hca.symm
  have h4 : (cliff b * scalar (hS a b) * cliff a) * (cliff c * scalar (hS (k := k) b c) * cliff b) =
      cliff a * scalar (hS a b * hS b c) * cliff c := by
    simp only [mul_assoc, cliff_scalar_assoc, cliff_scalar, scalar_scalar_assoc, map_mul,
      reflect_hS_left, reflect_hS_right, reflect_hS_of_ne, reflect_hA_left, reflect_hA_right,
      reflect_hA_of_ne, map_neg, hab, hbc, hca, hab.symm, hbc.symm, hca', ne_eq,
      not_false_eq_true]
    rw [cliff_word hab hbc]
    congr 2
    ring
  have h2 : scalar (hS a b) * (cliff c * scalar (hS (k := k) b c) * cliff b) =
      cliff c * scalar (hS a b * hS b c) * cliff b := by
    simp only [mul_assoc, cliff_scalar_assoc, cliff_scalar, scalar_scalar_assoc, map_mul,
      reflect_hS_of_ne, hab, hbc, hca, hab.symm, hbc.symm, hca', ne_eq, not_false_eq_true]
  have h3 : (cliff b * scalar (hS a b) * cliff a) * scalar (hS (k := k) b c) =
      cliff b * scalar (hS a b * hS b c) * cliff a := by
    simp only [mul_assoc, cliff_scalar_assoc, cliff_scalar, scalar_scalar_assoc, map_mul,
      reflect_hS_of_ne, hab, hbc, hca, hab.symm, hbc.symm, hca', ne_eq, not_false_eq_true]
  rw [fO, fO, mul_add, add_mul, add_mul, h2, h3, h4, ← scalar_mul, tri]
  abel

/-- KKT (3.15) at an odd colour: `f_{a,b} f_{b,c} + f_{b,c} f_{c,a} + f_{c,a} f_{a,b} = 0`. -/
theorem fO_cycle {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    fO (k := k) a b * fO b c + fO b c * fO c a + fO c a * fO a b = 0 := by
  rw [fO_mul_fO hab hbc hca, fO_mul_fO hbc hca hab, fO_mul_fO hca hab hbc,
    tri_rot a b c (scalar (hS b c * hS c a)), tri_rot b c a (scalar (hS c a * hS a b)),
    tri_rot a b c (scalar (hS c a * hS a b)), ← tri_add, ← tri_add, ← scalar_add, ← scalar_add,
    hS_cycle hab hbc hca, scalar_zero, tri_zero]

theorem fP_eq_zero {p q : ℕ} {ν : Seq I} (h : ν p ≠ ν q) : fP (k := k) par p q ν = 0 := by
  rw [fP, ite_eq_right h]

theorem fP_cycle {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (ν : Seq I) :
    fP (k := k) par a b ν * fP par b c ν + fP par b c ν * fP par c a ν +
      fP par c a ν * fP par a b ν = 0 := by
  by_cases h : ν a = ν b ∧ ν b = ν c
  · obtain ⟨h1, h2⟩ := h
    have h3 : ν c = ν a := (h1.trans h2).symm
    unfold fP
    rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h3]
    have hb := oddAt_congr par h1
    have hc := oddAt_congr par h2
    by_cases ho : oddAt par ν a
    · rw [ite_eq_left ho, ite_eq_left (hb.mp ho), ite_eq_left (hc.mp (hb.mp ho))]
      exact fO_cycle hab hbc hca
    · rw [ite_eq_right ho, ite_eq_right (mt hb.mpr ho), ite_eq_right (mt hc.mpr (mt hb.mpr ho)),
        add_zero, add_zero, add_zero, ← scalar_mul, ← scalar_mul, ← scalar_mul, ← scalar_add,
        ← scalar_add, hS_cycle hab hbc hca, scalar_zero]
  · have t1 : fP (k := k) par a b ν * fP par b c ν = 0 := by
      by_cases h1 : ν a = ν b
      · rw [fP_eq_zero par (fun h2 => h ⟨h1, h2⟩), mul_zero]
      · rw [fP_eq_zero par h1, zero_mul]
    have t2 : fP (k := k) par b c ν * fP par c a ν = 0 := by
      by_cases h2 : ν b = ν c
      · rw [fP_eq_zero par (fun h3 => h ⟨h3.symm.trans h2.symm, h2⟩), mul_zero]
      · rw [fP_eq_zero par h2, zero_mul]
    have t3 : fP (k := k) par c a ν * fP par a b ν = 0 := by
      by_cases h3 : ν c = ν a
      · rw [fP_eq_zero par (fun h1 => h ⟨h1, (h3.trans h1).symm⟩), mul_zero]
      · rw [fP_eq_zero par h3, zero_mul]
    rw [t1, t2, t3, add_zero, add_zero]

theorem fpq_cycle {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    fpq (k := k) (I := I) par a b * fpq par b c + fpq par b c * fpq par c a +
      fpq par c a * fpq par a b = 0 := by
  simp only [fpq_eq_diag, ← diag_mul]
  rw [← diag_add, ← diag_add, ← diag_zero]
  exact congrArg diag (funext (fP_cycle par hab hbc hca))

set_option linter.unusedSimpArgs false in
theorem fO_sq {p q : ℕ} (h : p ≠ q) :
    fO (k := k) p q * fO p q = scalar (hS p q * hS p q + hA p q * hA p q) := by
  have h' := h.symm
  simp only [fO, mul_add, add_mul, mul_assoc, cliff_scalar_assoc, cliff_scalar,
    scalar_scalar_assoc, map_mul, reflect_hS_left, reflect_hS_right, reflect_hA_left,
    reflect_hA_right, map_neg, h, h', ne_eq, not_false_eq_true]
  have hw : cliff (k := k) q * (cliff p * (cliff q * cliff p)) = -1 := by
    rw [cliff_anticomm_assoc h, cliff_mul_self, mul_one, endMul_neg, cliff_mul_self]
  have e1 : scalar (hA p q * -hS (k := k) p q) = -scalar (hS p q * hA p q) := by
    rw [← scalar_neg]; congr 1; ring
  have e2 : scalar (hA p q * -hA (k := k) p q) = -scalar (hA p q * hA p q) := by
    rw [← scalar_neg]; congr 1; ring
  rw [hw, endMul_neg, mul_one, ← scalar_mul, scalar_add, e1, e2, endNeg_mul]
  abel

/-- `f_{p,q}²`, a scalar: `(y_p - y_q)⁻² e_{p,q} + (y_p + y_q)⁻² ec_{p,q}`. -/
def sqv (p q : ℕ) (ν : Seq I) : K k :=
  if ν p = ν q then hS p q * hS p q + (if oddAt par ν p then hA p q * hA p q else 0) else 0

theorem fP_sq {p q : ℕ} (h : p ≠ q) (ν : Seq I) :
    fP (k := k) par p q ν * fP par p q ν = scalar (sqv par p q ν) := by
  unfold fP sqv
  by_cases hν : ν p = ν q
  · rw [ite_eq_left hν, ite_eq_left hν]
    by_cases ho : oddAt par ν p
    · rw [ite_eq_left ho, ite_eq_left ho]
      exact fO_sq h
    · rw [ite_eq_right ho, ite_eq_right ho, add_zero, add_zero, scalar_mul]
  · rw [ite_eq_right hν, ite_eq_right hν, zero_mul, scalar_zero]

theorem fpq_sq {p q : ℕ} (h : p ≠ q) :
    fpq (k := k) (I := I) par p q * fpq par p q = mulK (sqv par p q) := by
  rw [fpq_eq_diag, ← diag_mul, mulK]
  exact congrArg diag (funext (fP_sq par h))

theorem permK_sqv (σ : Equiv.Perm ℕ) (p q : ℕ) (ν : Seq I) :
    permK σ (sqv (k := k) par p q (ν ∘ σ)) = sqv par (σ p) (σ q) ν := by
  unfold sqv
  simp only [Function.comp_apply, oddAt_comp]
  split_ifs <;> simp

theorem sqv_swap (p q : ℕ) (ν : Seq I) : sqv (k := k) par q p ν = sqv par p q ν := by
  unfold sqv
  by_cases hν : ν p = ν q
  · rw [ite_eq_left hν.symm, ite_eq_left hν, hS_swap, hA_swap]
    simp only [(oddAt_congr par hν).symm]
    ring
  · rw [ite_eq_right (Ne.symm hν), ite_eq_right hν]

theorem reflect_sqv {p q : ℕ} (h : p ≠ q) {s : ℕ} {ν : Seq I} (hs : oddAt par ν s) :
    reflect s (sqv (k := k) par p q ν) = sqv par p q ν := by
  unfold sqv
  by_cases hν : ν p = ν q
  · rw [ite_eq_left hν]
    by_cases hp : p = s
    · subst hp
      rw [ite_eq_left hs]
      simp only [map_add, map_mul, reflect_hS_left (Ne.symm h), reflect_hA_left (Ne.symm h)]
      ring
    · by_cases hq : q = s
      · subst hq
        rw [ite_eq_left ((oddAt_congr par hν).mpr hs)]
        simp only [map_add, map_mul, reflect_hS_right h, reflect_hA_right h]
        ring
      · split_ifs <;> simp [reflect_hS_of_ne hp hq, reflect_hA_of_ne hp hq]
  · rw [ite_eq_right hν, map_zero]

theorem mulK_fpq_comm (g : Seq I → K k) {p q : ℕ}
    (hp : ∀ ν, oddAt par ν p → reflect p (g ν) = g ν)
    (hq : ∀ ν, oddAt par ν q → reflect q (g ν) = g ν) :
    mulK g * fpq par p q = fpq par p q * mulK g := by
  have e1 := (clif_mulK_comm par q g hq).symm
  have e2 := clif_mulK_comm par p g hp
  rw [fpq, mul_add, add_mul, mulK_comm]
  congr 1
  calc mulK g * (clif par q * mulK (hh p q) * clif par p)
      = (mulK g * clif par q) * mulK (hh p q) * clif par p := by simp only [mul_assoc]
    _ = clif par q * (mulK g * mulK (hh p q)) * clif par p := by rw [e1]; simp only [mul_assoc]
    _ = clif par q * mulK (hh p q) * (mulK g * clif par p) := by
        rw [mulK_comm]; simp only [mul_assoc]
    _ = _ := by rw [← e2]; simp only [mul_assoc]

/-! ## An identity in rings (proof of Theorem 3.8, relation (x)) -/

set_option linter.unusedSimpArgs false in
/-- The computation in the proof of KKT Theorem 3.8 for the braid relation, in any ring. -/
theorem braid_expand {E : Type*} [Ring E] (s₁ s₂ f₁ f₂ f₃ Q₁ Q₂ : E)
    (h12 : s₁ * f₂ = f₃ * s₁) (h13 : s₁ * f₃ = f₂ * s₁) (h11 : s₁ * f₁ = -(f₁ * s₁))
    (h21 : s₂ * f₁ = f₃ * s₂) (h23 : s₂ * f₃ = f₁ * s₂) (h22 : s₂ * f₂ = -(f₂ * s₂))
    (hs₁ : s₁ * s₁ = Q₁ - f₁ * f₁) (hs₂ : s₂ * s₂ = Q₂ - f₂ * f₂)
    (hA : f₃ * f₁ = f₁ * f₂ - f₂ * f₃) (hB : f₁ * f₃ = f₂ * f₁ - f₃ * f₂)
    (hc₂ : f₂ * f₂ * f₃ = f₃ * (f₂ * f₂)) :
    (s₂ + f₂) * (s₁ + f₁) * (s₂ + f₂) - (s₁ + f₁) * (s₂ + f₂) * (s₁ + f₁) =
      (s₂ * s₁ * s₂ - s₁ * s₂ * s₁) + f₃ * (Q₂ - Q₁) := by
  have h13' : ∀ X, s₁ * (f₃ * X) = f₂ * (s₁ * X) := fun X => by rw [← mul_assoc, h13, mul_assoc]
  have h23' : ∀ X, s₂ * (f₃ * X) = f₁ * (s₂ * X) := fun X => by rw [← mul_assoc, h23, mul_assoc]
  have hA' : ∀ X, f₃ * (f₁ * X) = f₁ * (f₂ * X) - f₂ * (f₃ * X) := fun X => by
    rw [← mul_assoc, hA, sub_mul, mul_assoc, mul_assoc]
  have hB' : ∀ X, f₁ * (f₃ * X) = f₂ * (f₁ * X) - f₃ * (f₂ * X) := fun X => by
    rw [← mul_assoc, hB, sub_mul, mul_assoc, mul_assoc]
  have hc₂' : f₂ * (f₂ * f₃) = f₃ * (f₂ * f₂) := by rw [← mul_assoc, hc₂]
  have h12' : ∀ X, s₁ * (f₂ * X) = f₃ * (s₁ * X) := fun X => by rw [← mul_assoc, h12, mul_assoc]
  have h21' : ∀ X, s₂ * (f₁ * X) = f₃ * (s₂ * X) := fun X => by rw [← mul_assoc, h21, mul_assoc]
  have h11' : ∀ X, s₁ * (f₁ * X) = -(f₁ * (s₁ * X)) := fun X => by
    rw [← mul_assoc, h11, neg_mul, mul_assoc]
  have h22' : ∀ X, s₂ * (f₂ * X) = -(f₂ * (s₂ * X)) := fun X => by
    rw [← mul_assoc, h22, neg_mul, mul_assoc]
  have hs₁' : ∀ X, s₁ * (s₁ * X) = Q₁ * X - f₁ * (f₁ * X) := fun X => by
    rw [← mul_assoc, hs₁, sub_mul, mul_assoc]
  have hs₂' : ∀ X, s₂ * (s₂ * X) = Q₂ * X - f₂ * (f₂ * X) := fun X => by
    rw [← mul_assoc, hs₂, sub_mul, mul_assoc]
  simp only [add_mul, mul_add, mul_sub, mul_neg, mul_assoc, h13', h23', hA', hB', h12', h21',
    h11', h22', hs₁', hs₂', h12, h11, h21, h22, hs₁, hs₂, hA, hc₂']
  noncomm_ring

/-! ## The operators `σ_a` (KKT Theorem 3.8) -/

variable (Qt : PairFn I k)

/-- The central coefficient `R_{p,q} = Q̃_{p,q} - f_{p,q}²` of the proof of KKT Theorem 3.8. -/
def cen (p q : ℕ) (ν : Seq I) : K k := Qt.val p q ν - sqv par p q ν

theorem permK_cen (σ : Equiv.Perm ℕ) (p q : ℕ) (ν : Seq I) :
    permK σ (cen par Qt p q (ν ∘ σ)) = cen par Qt (σ p) (σ q) ν := by
  rw [cen, map_sub, Qt.permK_val, permK_sqv, cen]

theorem cen_swap (p q : ℕ) (ν : Seq I) : cen par Qt q p ν = cen par Qt p q ν := by
  rw [cen, cen, Qt.val_symm, sqv_swap]

theorem reflect_cen (hQ : Qt.IsEven par) {p q : ℕ} (h : p ≠ q) {s : ℕ} {ν : Seq I}
    (hs : oddAt par ν s) : reflect s (cen par Qt p q ν) = cen par Qt p q ν := by
  rw [cen, map_sub, Qt.reflect_val hQ h s ν hs, reflect_sqv par h hs]

/-- KKT's `σ_a = s̃_a R_{a,a+1} + f_{a,a+1}` (Theorem 3.8), as an operator on the
twisted module. -/
def sig (a : ℕ) : Module.End k (V k I) := tw a (cen par Qt a (a + 1)) + fpq par a (a + 1)

theorem cen_cov (a : ℕ) (ν : Seq I) :
    permK (sw a) (cen par Qt a (a + 1) (ν ∘ sw a)) = cen par Qt a (a + 1) ν := by
  rw [permK_cen, sw_apply_left, sw_apply_right, cen_swap]

variable {par Qt} in
theorem tw_fpq_cen (hQ : Qt.IsEven par) (a p q : ℕ) :
    tw a (cen par Qt a (a + 1)) * fpq par p q =
      fpq par (sw a p) (sw a q) * tw a (cen par Qt a (a + 1)) :=
  tw_fpq par a _ (fun _ _ hs => reflect_cen par Qt hQ (by omega) hs) p q

/-- `σ_a² = Q̃_{a,a+1}(y_a, y_{a+1})` (KKT Theorem 3.8). -/
theorem sig_mul_self (hQ : Qt.IsEven par) (a : ℕ) :
    sig par Qt a * sig par Qt a = mulK (Qt.val a (a + 1)) := by
  have h1 := tw_fpq_cen hQ a a (a + 1)
  rw [sw_apply_left, sw_apply_right, fpq_swap par (p := a) (q := a + 1) (by omega),
    endNeg_mul] at h1
  rw [sig, add_mul, mul_add, mul_add, h1, tw_mul_self a _ (cen_cov par Qt a),
    fpq_sq par (by omega)]
  have : cen par Qt a (a + 1) + sqv par a (a + 1) = Qt.val a (a + 1) := by
    funext ν; simp [cen]
  rw [← this, mulK_add]
  abel

set_option linter.unusedSimpArgs false in
/-- The braid relation of KKT Theorem 3.8:
`σ_{a+1} σ_a σ_{a+1} - σ_a σ_{a+1} σ_a = f_{a,a+2} (Q̃_{a+1,a+2} - Q̃_{a,a+1})`. -/
theorem sig_braid (hQ : Qt.IsEven par) (a : ℕ) :
    sig par Qt (a + 1) * sig par Qt a * sig par Qt (a + 1) -
        sig par Qt a * sig par Qt (a + 1) * sig par Qt a =
      fpq par a (a + 2) * mulK (Qt.val (a + 1) (a + 2) - Qt.val a (a + 1)) := by
  have hs1 : sw a (a + 2) = a + 2 := sw_apply_of_ne (by omega) (by omega)
  have hs2 : sw (a + 1) a = a := sw_apply_of_ne (by omega) (by omega)
  have h12 := tw_fpq_cen hQ a (a + 1) (a + 2)
  have h13 := tw_fpq_cen hQ a a (a + 2)
  have h11 := tw_fpq_cen hQ a a (a + 1)
  have h21 := tw_fpq_cen hQ (a + 1) a (a + 1)
  have h23 := tw_fpq_cen hQ (a + 1) a (a + 2)
  have h22 := tw_fpq_cen hQ (a + 1) (a + 1) (a + 2)
  have e2 : a + 1 + 1 = a + 2 := rfl
  simp only [sw_apply_left, sw_apply_right, hs1, hs2, e2] at h12 h13 h11 h21 h23 h22
  rw [fpq_swap par (p := a) (q := a + 1) (by omega), endNeg_mul] at h11
  rw [fpq_swap par (p := a + 1) (q := a + 2) (by omega), endNeg_mul] at h22
  have hc1 := fpq_cycle (k := k) (I := I) par (a := a) (b := a + 1) (c := a + 2)
    (by omega) (by omega) (by omega)
  have hc2 := fpq_cycle (k := k) (I := I) par (a := a + 1) (b := a) (c := a + 2)
    (by omega) (by omega) (by omega)
  rw [fpq_swap par (p := a) (q := a + 2) (by omega)] at hc1
  rw [fpq_swap par (p := a) (q := a + 1) (by omega),
    fpq_swap par (p := a + 1) (q := a + 2) (by omega)] at hc2
  have hA : fpq (k := k) (I := I) par a (a + 2) * fpq par a (a + 1) =
      fpq par a (a + 1) * fpq par (a + 1) (a + 2) -
        fpq par (a + 1) (a + 2) * fpq par a (a + 2) := by
    rw [endMul_neg, endNeg_mul] at hc1
    rw [← sub_eq_zero, ← neg_eq_zero, ← hc1]; abel
  have hB : fpq (k := k) (I := I) par a (a + 1) * fpq par a (a + 2) =
      fpq par (a + 1) (a + 2) * fpq par a (a + 1) -
        fpq par a (a + 2) * fpq par (a + 1) (a + 2) := by
    rw [endMul_neg, endNeg_mul, endNeg_mul, endMul_neg, neg_neg] at hc2
    rw [← sub_eq_zero, ← neg_eq_zero, ← hc2]; abel
  have hc₂ : fpq (k := k) (I := I) par (a + 1) (a + 2) * fpq par (a + 1) (a + 2) *
      fpq par a (a + 2) = fpq par a (a + 2) *
        (fpq par (a + 1) (a + 2) * fpq par (a + 1) (a + 2)) := by
    rw [fpq_sq par (by omega)]
    exact mulK_fpq_comm par _ (fun _ hs => reflect_sqv par (by omega) hs)
      (fun _ hs => reflect_sqv par (by omega) hs)
  have hsq : ∀ b, tw b (cen par Qt b (b + 1)) * tw b (cen par Qt b (b + 1)) =
      mulK (Qt.val b (b + 1)) - fpq par b (b + 1) * fpq par b (b + 1) := fun b => by
    rw [tw_mul_self b _ (cen_cov par Qt b), fpq_sq par (by omega), ← mulK_sub]
    rfl
  have key := braid_expand (tw a (cen par Qt a (a + 1)))
    (tw (a + 1) (cen par Qt (a + 1) (a + 2))) (fpq par a (a + 1))
    (fpq par (a + 1) (a + 2)) (fpq par a (a + 2)) (mulK (Qt.val a (a + 1)))
    (mulK (Qt.val (a + 1) (a + 2))) h12 h13 h11 h21 h23 h22 (hsq a) (hsq (a + 1)) hA hB hc₂
  have hbr := tw_braid a (cen par Qt a (a + 1)) (cen par Qt (a + 1) (a + 2))
    (fun ν => by
      rw [permK_cen]; simp only [Equiv.Perm.coe_mul, Function.comp_apply, sw_apply_right,
        sw_apply_left, hs1, hs2])
    (fun ν => by
      rw [permK_cen, permK_cen]; simp only [sw_apply_right, sw_apply_left, hs1, hs2])
    (fun ν => by
      rw [permK_cen]; simp only [Equiv.Perm.coe_mul, Function.comp_apply, sw_apply_right,
        sw_apply_left, hs1, hs2])
  simp only [sig, e2]
  rw [key, hbr, sub_self, zero_add, mulK_sub]

end OddMath.QuiverHecke.Realization
