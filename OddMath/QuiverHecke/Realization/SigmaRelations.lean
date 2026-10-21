/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Realization.Sigma

/-!
# The remaining relations of KKT Theorem 3.8

Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, Theorem 3.8: besides `σ_a² = Q̃_{a,a+1}` and the
braid relation (`sig_mul_self`, `sig_braid`), the operators `σ_a` commute with each other at
distance at least two, move the Clifford generators along the transposition `s_a`, commute
with symmetric scalars, and satisfy the dot relations

  `σ_a y_a - y_{a+1} σ_a = e_{a,a+1} + c_a c_{a+1} e_{a,a+1}`,
  `σ_a y_{a+1} - y_a σ_a = -e_{a,a+1} + c_a c_{a+1} e_{a,a+1}`,

where `e_{a,a+1}` is the sum of the idempotents with equal colours at `a` and `a + 1` and the
Clifford generators vanish at even positions. As in `Realization/Sigma`, positions are read from
left to right.
-/

noncomputable section
open scoped TensorProduct
namespace OddMath.QuiverHecke.Realization

variable {I : Type*} {k : Type*} [CommRing k]

/-! ## Identities in rings -/

/-- An element `c₂ h c₁` commutes with `d` when `h` does and both `cᵢ` anticommute with `d`. -/
theorem commute_sandwich {E : Type*} [Ring E] {h c₁ c₂ d : E} (e₁ : c₁ * d = -(d * c₁))
    (e₂ : c₂ * d = -(d * c₂)) (e₃ : Commute h d) : Commute (c₂ * h * c₁) d := by
  show c₂ * h * c₁ * d = d * (c₂ * h * c₁)
  calc c₂ * h * c₁ * d = c₂ * h * (c₁ * d) := by rw [mul_assoc]
    _ = -(c₂ * (h * d) * c₁) := by rw [e₁]; noncomm_ring
    _ = -((c₂ * d) * h * c₁) := by rw [e₃.eq]; noncomm_ring
    _ = d * (c₂ * h * c₁) := by rw [e₂]; noncomm_ring

/-- Two operators of the shape of `f_{p,q}` on disjoint pairs of positions commute. -/
theorem commute_fpq_shape {E : Type*} [Ring E] {h g c₁ c₂ d₁ d₂ : E} (hg : Commute h g)
    (hd₁ : Commute h d₁) (hd₂ : Commute h d₂) (gc₁ : Commute g c₁) (gc₂ : Commute g c₂)
    (a₁₁ : c₁ * d₁ = -(d₁ * c₁)) (a₁₂ : c₁ * d₂ = -(d₂ * c₁)) (a₂₁ : c₂ * d₁ = -(d₁ * c₂))
    (a₂₂ : c₂ * d₂ = -(d₂ * c₂)) : Commute (h + c₂ * h * c₁) (g + d₂ * g * d₁) := by
  have X₁ := commute_sandwich a₁₁ a₂₁ hd₁
  have X₂ := commute_sandwich a₁₂ a₂₂ hd₂
  have Xg : Commute (c₂ * h * c₁) g := (gc₂.symm.mul_left hg).mul_left gc₁.symm
  refine (hg.add_right ((hd₂.mul_right hg).mul_right hd₁)).add_left
    (Xg.add_right ((X₂.mul_right Xg).mul_right X₁))

/-- An operator of the shape of `f_{p,q}` commutes with `d` when `h` does and `d`
anticommutes with both Clifford factors. -/
theorem commute_fpq_shape_one {E : Type*} [Ring E] {h c₁ c₂ d : E} (e₁ : c₁ * d = -(d * c₁))
    (e₂ : c₂ * d = -(d * c₂)) (e₃ : Commute h d) : Commute (h + c₂ * h * c₁) d :=
  e₃.add_left (commute_sandwich e₁ e₂ e₃)

theorem fpq_shape_mul_left {E : Type*} [Ring E] {s c₁ c₂ : E} (h₁ : c₁ * c₁ = 1)
    (h₂ : c₂ * c₂ = 1) : (s + c₂ * s * c₁) * c₁ = c₂ * (s + c₂ * s * c₁) := by
  rw [add_mul, mul_add, mul_assoc (c₂ * s), h₁, mul_one, ← mul_assoc c₂ (c₂ * s),
    ← mul_assoc c₂ c₂, h₂, one_mul, add_comm]

theorem fpq_shape_mul_right {E : Type*} [Ring E] {s A c₁ c₂ : E} (h₁ : c₁ * c₁ = 1)
    (h₂ : c₂ * c₂ = 1) (h₁₂ : c₁ * c₂ = -(c₂ * c₁)) (e₂ : c₂ * s = A * c₂)
    (e₁ : c₁ * s = -(A * c₁)) (e₁' : c₁ * A = -(s * c₁)) :
    (s + c₂ * s * c₁) * c₂ = c₁ * (s + c₂ * s * c₁) := by
  have l : c₂ * s * c₁ * c₂ = -(A * c₁) := by
    calc c₂ * s * c₁ * c₂ = c₂ * s * (c₁ * c₂) := by rw [mul_assoc]
      _ = -((c₂ * s) * c₂ * c₁) := by rw [h₁₂]; noncomm_ring
      _ = -(A * (c₂ * c₂) * c₁) := by rw [e₂]; noncomm_ring
      _ = -(A * c₁) := by rw [h₂, mul_one]
  have r : c₁ * (c₂ * s * c₁) = s * c₂ := by
    calc c₁ * (c₂ * s * c₁) = c₁ * (c₂ * s) * c₁ := by noncomm_ring
      _ = (c₁ * A) * c₂ * c₁ := by rw [e₂]; noncomm_ring
      _ = -(s * (c₁ * c₂) * c₁) := by rw [e₁']; noncomm_ring
      _ = s * c₂ * (c₁ * c₁) := by rw [h₁₂]; noncomm_ring
      _ = s * c₂ := by rw [h₁, mul_one]
  rw [add_mul, mul_add, l, r, e₁]
  abel

theorem fpq_shape_dot {E : Type*} [Ring E] {s yp yq cp cq : E} {u : E}
    (hs : s * yp - yq * s = u) (hp : cp * yp = -(yp * cp)) (hq : yq * cq = -(cq * yq))
    (hu₁ : u * cp = cp * u) (hqp : cq * cp = -(cp * cq)) :
    (s + cq * s * cp) * yp - yq * (s + cq * s * cp) = u + cp * cq * u := by
  have l : cq * s * cp * yp = -(cq * (s * yp) * cp) := by
    rw [mul_assoc (cq * s), hp]; noncomm_ring
  have r : yq * (cq * s * cp) = -(cq * (yq * s) * cp) := by
    rw [← mul_assoc, ← mul_assoc, hq]; noncomm_ring
  have m : cq * (s * yp) * cp - cq * (yq * s) * cp = -(cp * cq * u) := by
    rw [← sub_mul, ← mul_sub, hs, mul_assoc, hu₁, ← mul_assoc, hqp, neg_mul]
  have key : s * yp + -(cq * (s * yp) * cp) - (yq * s + -(cq * (yq * s) * cp)) =
      (s * yp - yq * s) - (cq * (s * yp) * cp - cq * (yq * s) * cp) := by abel
  rw [add_mul, mul_add, l, r, key, hs, m, sub_neg_eq_add]

theorem fpq_shape_dot' {E : Type*} [Ring E] {s yp yq cp cq : E} {u : E}
    (hs : s * yq - yp * s = u) (hp : cp * yq = yq * cp) (hq : yp * cq = cq * yp)
    (hu₁ : u * cp = cp * u) (hqp : cq * cp = -(cp * cq)) :
    (s + cq * s * cp) * yq - yp * (s + cq * s * cp) = u - cp * cq * u := by
  have l : cq * s * cp * yq = cq * (s * yq) * cp := by
    rw [mul_assoc (cq * s), hp]; noncomm_ring
  have r : yp * (cq * s * cp) = cq * (yp * s) * cp := by
    rw [← mul_assoc, ← mul_assoc, hq]; noncomm_ring
  have m : cq * (s * yq) * cp - cq * (yp * s) * cp = -(cp * cq * u) := by
    rw [← sub_mul, ← mul_sub, hs, mul_assoc, hu₁, ← mul_assoc, hqp, neg_mul]
  have key : s * yq + cq * (s * yq) * cp - (yp * s + cq * (yp * s) * cp) =
      (s * yq - yp * s) + (cq * (s * yq) * cp - cq * (yp * s) * cp) := by abel
  rw [add_mul, mul_add, l, r, key, hs, m, ← sub_eq_add_neg]

/-! ## Operators -/

variable [DecidableEq I] (par : I → ZMod 2)

/-- The Clifford coefficient operator at `p` on the component `ν`. -/
def cl (ν : Seq I) (p : ℕ) : Module.End k (Coeff k) := if oddAt par ν p then cliff p else 0

omit [DecidableEq I] in
theorem clif_eq_diag (p : ℕ) : clif (k := k) (I := I) par p = diag fun ν => cl par ν p := rfl

theorem reflect_hh {s p q : ℕ} (hp : p ≠ s) (hq : q ≠ s) (ν : Seq I) :
    reflect s (hh (k := k) p q ν) = hh p q ν := by
  unfold hh
  split_ifs
  · exact reflect_hS_of_ne hp hq
  · exact map_zero _

theorem commute_mulK_hh_clif {s p q : ℕ} (hp : p ≠ s) (hq : q ≠ s) :
    Commute (mulK (k := k) (hh p q)) (clif par s) :=
  (clif_mulK_comm par s _ fun ν _ => reflect_hh hp hq ν).symm

/-- `f_{p,q}` and `f_{r,s}` commute for disjoint pairs. -/
theorem commute_fpq {p q r s : ℕ} (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) :
    Commute (fpq (k := k) (I := I) par p q) (fpq par r s) :=
  commute_fpq_shape (mulK_comm _ _) (commute_mulK_hh_clif par hpr hqr)
    (commute_mulK_hh_clif par hps hqs) (commute_mulK_hh_clif par hpr.symm hps.symm)
    (commute_mulK_hh_clif par hqr.symm hqs.symm) (clif_anticomm par hpr)
    (clif_anticomm par hps) (clif_anticomm par hqr) (clif_anticomm par hqs)

/-- `f_{p,q}` commutes with `c_s` for `s ∉ {p, q}`. -/
theorem commute_fpq_clif {p q s : ℕ} (hp : p ≠ s) (hq : q ≠ s) :
    Commute (fpq (k := k) (I := I) par p q) (clif par s) :=
  commute_fpq_shape_one (clif_anticomm par hp) (clif_anticomm par hq)
    (commute_mulK_hh_clif par hp hq)

theorem fP_cl_left (p q : ℕ) (ν : Seq I) :
    fP (k := k) par p q ν * cl par ν p = cl par ν q * fP par p q ν := by
  unfold fP cl
  by_cases hν : ν p = ν q
  · have hpq := oddAt_congr par hν
    rw [ite_eq_left hν]
    by_cases ho : oddAt par ν p
    · rw [ite_eq_left ho, ite_eq_left ho, ite_eq_left (hpq.mp ho)]
      exact fpq_shape_mul_left (E := Module.End k (Coeff k)) (cliff_mul_self p) (cliff_mul_self q)
    · rw [ite_eq_right ho, ite_eq_right ho, ite_eq_right (mt hpq.mpr ho), mul_zero, zero_mul]
  · rw [ite_eq_right hν, zero_mul, mul_zero]

theorem fP_cl_right {p q : ℕ} (h : p ≠ q) (ν : Seq I) :
    fP (k := k) par p q ν * cl par ν q = cl par ν p * fP par p q ν := by
  unfold fP cl
  by_cases hν : ν p = ν q
  · have hpq := oddAt_congr par hν
    rw [ite_eq_left hν]
    by_cases ho : oddAt par ν p
    · rw [ite_eq_left ho, ite_eq_left ho, ite_eq_left (hpq.mp ho)]
      refine fpq_shape_mul_right (E := Module.End k (Coeff k)) (A := scalar (hA p q))
        (cliff_mul_self p) (cliff_mul_self q)
        (cliff_anticomm h) ?_ ?_ ?_
      · rw [cliff_scalar, reflect_hS_right h]
      · rw [cliff_scalar, reflect_hS_left (Ne.symm h), scalar_neg, endNeg_mul]
      · rw [cliff_scalar, reflect_hA_left (Ne.symm h), scalar_neg, endNeg_mul]
    · rw [ite_eq_right ho, ite_eq_right ho, ite_eq_right (mt hpq.mpr ho), mul_zero, zero_mul]
  · rw [ite_eq_right hν, zero_mul, mul_zero]

theorem fpq_clif_left (p q : ℕ) :
    fpq (k := k) (I := I) par p q * clif par p = clif par q * fpq par p q := by
  rw [fpq_eq_diag, clif_eq_diag, clif_eq_diag, ← diag_mul', ← diag_mul']
  exact congrArg diag (funext (fP_cl_left par p q))

theorem fpq_clif_right {p q : ℕ} (h : p ≠ q) :
    fpq (k := k) (I := I) par p q * clif par q = clif par p * fpq par p q := by
  rw [fpq_eq_diag, clif_eq_diag, clif_eq_diag, ← diag_mul', ← diag_mul']
  exact congrArg diag (funext (fP_cl_right par h))

/-! ## The relations of `σ_a` -/

variable (Qt : PairFn I k)

theorem permK_cen_far {a b : ℕ} (hab : a + 1 < b ∨ b + 1 < a) (ν : Seq I) :
    permK (sw b) (cen par Qt a (a + 1) (ν ∘ sw b)) = cen par Qt a (a + 1) ν := by
  rw [permK_cen, sw_apply_of_ne (by omega) (by omega), sw_apply_of_ne (by omega) (by omega)]

/-- Far commutation `σ_a σ_b = σ_b σ_a` for `|a - b| > 1` (KKT Theorem 3.8). -/
theorem sig_comm (hQ : Qt.IsEven par) {a b : ℕ} (hab : a + 1 < b ∨ b + 1 < a) :
    sig par Qt a * sig par Qt b = sig par Qt b * sig par Qt a := by
  have htt := tw_comm hab (cen par Qt a (a + 1)) (cen par Qt b (b + 1))
    (permK_cen_far par Qt hab) (permK_cen_far par Qt (Or.symm hab))
  have htf := tw_fpq_cen hQ a b (b + 1)
  have hft := tw_fpq_cen hQ b a (a + 1)
  rw [sw_apply_of_ne (by omega) (by omega), sw_apply_of_ne (by omega) (by omega)] at htf hft
  have hff := (commute_fpq (k := k) par (p := a) (q := a + 1) (r := b) (s := b + 1)
    (by omega) (by omega) (by omega) (by omega)).eq
  simp only [sig, add_mul, mul_add, htt, htf, hft, hff]
  abel

/-- `σ_a c_p = c_{s_a(p)} σ_a` (KKT Theorem 3.8). -/
theorem sig_clif (hQ : Qt.IsEven par) (a p : ℕ) :
    sig par Qt a * clif par p = clif par (sw a p) * sig par Qt a := by
  have ht := tw_clif par a (cen par Qt a (a + 1)) p
    (fun _ hs => reflect_cen par Qt hQ (by omega) hs)
  have hf : fpq (k := k) (I := I) par a (a + 1) * clif par p =
      clif par (sw a p) * fpq par a (a + 1) := by
    by_cases h₀ : p = a
    · subst h₀; rw [sw_apply_left]; exact fpq_clif_left par _ _
    · by_cases h₁ : p = a + 1
      · subst h₁; rw [sw_apply_right]; exact fpq_clif_right par (by omega)
      · rw [sw_apply_of_ne h₀ h₁]
        exact (commute_fpq_clif par (Ne.symm h₀) (Ne.symm h₁)).eq
  rw [sig, add_mul, mul_add, ht, hf]

/-- Scalars invariant under `s_a` and even in the odd variables at `a`, `a + 1` commute
with `σ_a`. -/
theorem sig_mulK (a : ℕ) (g : Seq I → K k)
    (hg : ∀ ν, permK (sw a) (g (ν ∘ sw a)) = g ν)
    (h₀ : ∀ ν, oddAt par ν a → reflect a (g ν) = g ν)
    (h₁ : ∀ ν, oddAt par ν (a + 1) → reflect (a + 1) (g ν) = g ν) :
    sig par Qt a * mulK g = mulK g * sig par Qt a := by
  rw [sig, add_mul, mul_add, tw_mulK, funext hg, mulK_fpq_comm par g h₀ h₁]

/-- The indicator of equal colours at `a` and `a + 1`. -/
def eqv (a : ℕ) (ν : Seq I) : K k := if ν a = ν (a + 1) then 1 else 0

theorem sig_dot_aux (a : ℕ) (Y Y' : K k) (hY : permK (sw a) Y = Y') :
    sig par Qt a * mulK (fun _ => Y) - mulK (fun _ => Y') * sig par Qt a =
      fpq par a (a + 1) * mulK (fun _ => Y) - mulK (fun _ => Y') * fpq par a (a + 1) := by
  rw [sig, add_mul, mul_add, tw_mulK]
  simp only [hY]
  abel

theorem scalar_y_cliff (q : ℕ) :
    scalar (y (k := k) q) * cliff q = -(cliff q * scalar (y q)) := by
  have := cliff_scalar (k := k) q (-y q)
  rw [map_neg, reflect_y_self, neg_neg] at this
  rw [← this, scalar_neg, endMul_neg]

/-- The first dot relation of KKT Theorem 3.8:
`σ_a y_a - y_{a+1} σ_a = e + c_a c_{a+1} e` with `e` the equal-colour indicator. -/
theorem sig_dot_left (a : ℕ) :
    sig par Qt a * mulK (fun _ => y a) - mulK (fun _ => y (a + 1)) * sig par Qt a =
      mulK (eqv a) + clif par a * clif par (a + 1) * mulK (eqv a) := by
  rw [sig_dot_aux par Qt a _ _ (by rw [permK_y, sw_apply_left]), fpq_eq_diag]
  simp only [mulK, clif_eq_diag, ← diag_mul', ← diag_sub, ← diag_add]
  congr 1
  funext ν
  unfold fP cl eqv
  by_cases hν : ν a = ν (a + 1)
  · have hpq := oddAt_congr par hν
    rw [ite_eq_left hν, ite_eq_left hν, scalar_one, mul_one]
    have hs : scalar (hS (k := k) a (a + 1)) * scalar (y a) - scalar (y (a + 1)) *
        scalar (hS a (a + 1)) = 1 := by
      rw [← scalar_mul, ← scalar_mul, ← scalar_sub, mul_comm (y _), ← mul_sub,
        hS_mul (by omega), scalar_one]
    by_cases ho : oddAt par ν a
    · rw [ite_eq_left ho, ite_eq_left ho, ite_eq_left (hpq.mp ho)]
      have := fpq_shape_dot (E := Module.End k (Coeff k)) (u := 1) hs
        (by rw [cliff_scalar, reflect_y_self, scalar_neg, endNeg_mul])
        (scalar_y_cliff (a + 1)) (by rw [one_mul, mul_one]) (cliff_anticomm (by omega))
      rw [this, mul_one]
    · rw [ite_eq_right ho, ite_eq_right ho]
      simp only [add_zero, zero_mul, hs]
  · rw [ite_eq_right hν, ite_eq_right hν]
    simp only [zero_mul, mul_zero, scalar_zero, add_zero]
    exact sub_self (0 : Module.End k (Coeff k))

/-- The second dot relation of KKT Theorem 3.8:
`σ_a y_{a+1} - y_a σ_a = -e + c_a c_{a+1} e`. -/
theorem sig_dot_right (a : ℕ) :
    sig par Qt a * mulK (fun _ => y (a + 1)) - mulK (fun _ => y a) * sig par Qt a =
      -mulK (eqv a) + clif par a * clif par (a + 1) * mulK (eqv a) := by
  rw [sig_dot_aux par Qt a _ _ (by rw [permK_y, sw_apply_right]), fpq_eq_diag]
  simp only [mulK, clif_eq_diag, ← diag_mul', ← diag_sub, ← diag_add, ← diag_neg]
  congr 1
  funext ν
  unfold fP cl eqv
  by_cases hν : ν a = ν (a + 1)
  · have hpq := oddAt_congr par hν
    rw [ite_eq_left hν, ite_eq_left hν, scalar_one, mul_one]
    have hs : scalar (hS (k := k) a (a + 1)) * scalar (y (a + 1)) - scalar (y a) *
        scalar (hS a (a + 1)) = -1 := by
      rw [← scalar_mul, ← scalar_mul, ← scalar_sub, mul_comm (y _), ← mul_sub,
        ← neg_sub, mul_neg, hS_mul (by omega), scalar_neg, scalar_one]
    by_cases ho : oddAt par ν a
    · rw [ite_eq_left ho, ite_eq_left ho, ite_eq_left (hpq.mp ho)]
      have := fpq_shape_dot' (E := Module.End k (Coeff k)) (u := -1) (cp := cliff a)
        (cq := cliff (a + 1)) hs
        (by rw [cliff_scalar, reflect_y_of_ne (show a + 1 ≠ a by omega)])
        (by rw [cliff_scalar, reflect_y_of_ne (show a ≠ a + 1 by omega)])
        (by rw [endNeg_mul, one_mul, endMul_neg, mul_one])
        (cliff_anticomm (by omega))
      rw [this, endMul_neg, mul_one]
      exact sub_neg_eq_add (-1 : Module.End k (Coeff k)) _
    · rw [ite_eq_right ho, ite_eq_right ho]
      simp only [add_zero, zero_mul, hs]
  · rw [ite_eq_right hν, ite_eq_right hν]
    simp only [zero_mul, mul_zero, scalar_zero, add_zero]
    exact (sub_self (0 : Module.End k (Coeff k))).trans
      (neg_zero (G := Module.End k (Coeff k))).symm

end OddMath.QuiverHecke.Realization
