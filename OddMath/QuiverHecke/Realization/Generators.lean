/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Realization.SigmaRelations
import OddMath.QuiverHecke.Presentation

/-!
# The BE2 dots and crossings on the twisted module

Brundan–Ellis, arXiv:1701.04133v2, §11, the quiver Hecke supercategory `H` with the
relations (1.7)–(1.9), realized through Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2,
Theorems 3.8 and 3.13. A dot on a strand of colour `i` at position `p` acts by

  `x_p = c_p y_p` if `|i| = 1`, and `x_p = y_p` if `|i| = 0`,

and a crossing of colours `i`, `j` at positions `a`, `a + 1` acts by

  `τ_a = γ_{ij} (c_a - c_{a+1})^{|i||j|} σ_a`,

with `γ_{ii} = -1/2` for odd `i` and `γ_{ij} = 1` otherwise. The operators `σ_a` of
`Realization/Sigma` are built from `Q̃ = κ_{ij} Q_{ij}(x_a, x_{a+1})`, where `Q_{ij}` is the
right-hand side of BE2's quadratic relation rewritten through `x_p² = -y_p²` at odd colours,
and `κ_{ij} = -1/2` for distinct odd colours (`1` otherwise).

The two halves needed for odd colours exist by `SKM.Scalars.two_isUnit`.
-/

noncomputable section
open scoped TensorProduct
namespace OddMath.QuiverHecke.Realization

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] {k : Type*} [CommRing k]

/-! ## The coefficient `Q̃` -/

/-- `x^n` in terms of `u`, for a dot of parity `e` with `x = c u` when `e = 1`: `u^n` for
`e = 0`; `(-1)^{n/2} u^n` for `e = 1` and `n` even. Odd powers of odd dots never occur with a
nonzero coefficient in the quadratic relation, and are sent to `0`. -/
def xpow (e : ZMod 2) (n : ℕ) (u : K k) : K k :=
  if e = 1 then (if Even n then (-1) ^ (n / 2) * u ^ n else 0) else u ^ n

theorem map_xpow (e' : K k ≃ₐ[k] K k) (e : ZMod 2) (n : ℕ) (u : K k) :
    e' (xpow e n u) = xpow e n (e' u) := by
  unfold xpow; split_ifs <;> simp

theorem xpow_neg_of_odd (n : ℕ) (u : K k) : xpow (1 : ZMod 2) n (-u) = xpow 1 n u := by
  unfold xpow
  by_cases h : Even n
  · simp [h, h.neg_pow]
  · simp [h]

variable (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [DecidableEq I]

/-- The right-hand side of BE2's quadratic relation (1.7) for `i ≠ j`, as a function of
`u = y_a` and `v = y_{a+1}` (with `x_p² = -y_p²` at odd colours), and `0` for `i = j`. -/
def qL (i j : I) (u v : K k) : K k :=
  if i = j then 0
  else if D.d i j = 0 then algebraMap k (K k) (Sc.t i j)
  else algebraMap k (K k) (Sc.t i j) * xpow (D.parity i) (D.dn i j) u +
    algebraMap k (K k) (Sc.t j i) * xpow (D.parity j) (D.dn j i) v +
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      algebraMap k (K k) (Sc.s i j p q) * (xpow (D.parity i) p u * xpow (D.parity j) q v)

theorem qL_symm (i j : I) (u v : K k) : qL D Sc j i v u = qL D Sc i j u v := by
  unfold qL
  by_cases hij : i = j
  · subst hij; simp
  · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]
    by_cases hd : D.d i j = 0
    · rw [ite_eq_left ((D.d_eq_zero_iff i j).mp hd), ite_eq_left hd, Sc.t_symm_of_d_eq_zero i j hd]
    · rw [ite_eq_right (fun h => hd ((D.d_eq_zero_iff i j).mpr h)), ite_eq_right hd, Finset.sum_comm]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
        rw [Sc.s_symm i j q p]; ring

theorem map_qL (e : K k ≃ₐ[k] K k) (i j : I) (u v : K k) :
    e (qL D Sc i j u v) = qL D Sc i j (e u) (e v) := by
  unfold qL
  split_ifs <;> simp [map_sum, map_xpow]

/-- `-1/2`'s half, `2⁻¹ ∈ k` (meaningful when `2` is a unit). -/
def half : k := Ring.inverse 2

/-- The normalization `κ_{ij}`: `-1/2` for distinct odd colours, else `1`. -/
def kap (i j : I) : k := if i ≠ j ∧ D.parity i = 1 ∧ D.parity j = 1 then -half else 1

theorem kap_symm (i j : I) : kap (k := k) D j i = kap D i j := by
  unfold kap
  by_cases h : i ≠ j ∧ D.parity i = 1 ∧ D.parity j = 1
  · rw [ite_eq_left h, ite_eq_left ⟨Ne.symm h.1, h.2.2, h.2.1⟩]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨Ne.symm h'.1, h'.2.2, h'.2.1⟩]

/-- KKT's `Q̃` for the BE2 parameters. -/
def qt : PairFn I k where
  toFun
    | some i, some j, u, v => algebraMap k (K k) (kap D i j) * qL D Sc i j u v
    | _, _, _, _ => 0
  map' e i j u v := by
    rcases i with _ | i <;> rcases j with _ | j <;> simp [map_qL]
  symm' i j u v := by
    rcases i with _ | i <;> rcases j with _ | j <;> simp [qL_symm, kap_symm]

theorem qt_isEven : (qt D Sc).IsEven D.parity := by
  intro i j u v hi
  rcases j with _ | j
  · rfl
  · show _ * qL D Sc i j (-u) v = _ * qL D Sc i j u v
    unfold qL
    split_ifs <;> simp [hi, xpow_neg_of_odd]

/-! ## Ring identities for the dot–crossing relations -/

/-- The odd–odd case of the first dot–crossing relation. -/
theorem slide_odd_left {E : Type*} [Ring E] {s Ya Yb Ca Cb O U : E} (hsa : s * Ca = Cb * s)
    (hYa : Yb * Ca = Ca * Yb) (hYb : Yb * Cb = -(Cb * Yb)) (hO : Cb * Cb = O)
    (hba : Cb * Ca = -(Ca * Cb)) (hU : s * Ya - Yb * s = U) :
    (Ca - Cb) * s * (Ca * Ya) + Cb * Yb * ((Ca - Cb) * s) = (Ca * Cb - O) * U := by
  have l : (Ca - Cb) * s * (Ca * Ya) = (Ca * Cb - O) * (s * Ya) := by
    rw [← hO, mul_assoc (Ca - Cb), ← mul_assoc s, hsa]; noncomm_ring
  have r : Cb * Yb * ((Ca - Cb) * s) = -((Ca * Cb - O) * (Yb * s)) := by
    rw [← hO]
    calc Cb * Yb * ((Ca - Cb) * s) = Cb * (Yb * Ca) * s - Cb * (Yb * Cb) * s := by noncomm_ring
      _ = (Cb * Ca) * Yb * s + Cb * Cb * Yb * s := by rw [hYa, hYb]; noncomm_ring
      _ = _ := by rw [hba]; noncomm_ring
  rw [l, r, ← hU]; noncomm_ring

/-- The odd–odd case of the second dot–crossing relation. -/
theorem slide_odd_right {E : Type*} [Ring E] {s Ya Yb Ca Cb O U : E} (hsb : s * Cb = Ca * s)
    (hYa : Ya * Ca = -(Ca * Ya)) (hYb : Ya * Cb = Cb * Ya) (hO : Ca * Ca = O)
    (hba : Cb * Ca = -(Ca * Cb)) (hU : s * Yb - Ya * s = U) :
    Ca * Ya * ((Ca - Cb) * s) + (Ca - Cb) * s * (Cb * Yb) = (O + Ca * Cb) * U := by
  have l : Ca * Ya * ((Ca - Cb) * s) = -((O + Ca * Cb) * (Ya * s)) := by
    rw [← hO]
    calc Ca * Ya * ((Ca - Cb) * s) = Ca * (Ya * Ca) * s - Ca * (Ya * Cb) * s := by noncomm_ring
      _ = _ := by rw [hYa, hYb]; noncomm_ring
  have r : (Ca - Cb) * s * (Cb * Yb) = (O + Ca * Cb) * (s * Yb) := by
    rw [← hO, mul_assoc (Ca - Cb), ← mul_assoc s, hsb]
    calc (Ca - Cb) * (Ca * s * Yb) = (Ca * Ca - Cb * Ca) * (s * Yb) := by noncomm_ring
      _ = _ := by rw [hba]; noncomm_ring
  rw [l, r, ← hU]; noncomm_ring

/-! ## The operators -/

/-- A dot of colour `i` at position `p`: `c_p y_p` for odd `i`, `y_p` for even `i`. -/
def dotOp (i : I) (p : ℕ) : Module.End k (V k I) :=
  if D.parity i = 1 then clif D.parity p * mulK (fun _ => y p) else mulK (fun _ => y p)

/-- `γ_{ij}`: `-1/2` for `i = j` odd, else `1`. -/
def gam (i j : I) : k := if i = j ∧ D.parity i = 1 then -(half : k) else 1

/-- The Clifford factor `(c_a - c_{a+1})^{|i||j|}`. -/
def dres (i j : I) (a : ℕ) : Module.End k (V k I) :=
  if D.parity i = 1 ∧ D.parity j = 1 then clif D.parity a - clif D.parity (a + 1) else 1

/-- A crossing of colours `i`, `j` at positions `a`, `a + 1`. -/
def crossOp (i j : I) (a : ℕ) : Module.End k (V k I) :=
  gam (k := k) D i j • (dres D i j a * sig D.parity (qt D Sc) a)

/-! ## Commutation of Clifford generators and variables -/

section Comm

variable {J : Type*} (par : J → ZMod 2)

theorem clif_y_self (p : ℕ) :
    clif par p * mulK (fun _ => y (k := k) p) = -(mulK (fun _ => y p) * clif par p) := by
  rw [clif_mulK]
  simp only [reflect_y_self]
  have : (fun _ : Seq J => -y (k := k) p) = -(fun _ => y p) := rfl
  rw [this, mulK_neg, endNeg_mul]

theorem clif_y_comm {p q : ℕ} (h : q ≠ p) :
    clif par p * mulK (fun _ => y (k := k) q) = mulK (fun _ => y q) * clif par p :=
  clif_mulK_comm par p _ fun _ _ => reflect_y_of_ne h

theorem y_clif_self (p : ℕ) :
    mulK (fun _ => y (k := k) p) * clif par p = -(clif par p * mulK (fun _ => y p)) :=
  by rw [clif_y_self, endNeg_neg]

end Comm

/-! ## The dot–crossing relations as operator identities -/

section Slide

variable (a : ℕ)

/-- Shorthand: multiplication by `y_p`. -/
abbrev Y (p : ℕ) : Module.End k (V k I) := mulK fun _ => y p

/-- Shorthand: `e + c_a c_{a+1} e`, the right-hand side of `sig_dot_left`. -/
abbrev eL (par : I → ZMod 2) (a : ℕ) : Module.End k (V k I) :=
  mulK (eqv a) + clif par a * clif par (a + 1) * mulK (eqv a)

/-- Shorthand: `-e + c_a c_{a+1} e`, the right-hand side of `sig_dot_right`. -/
abbrev eR (par : I → ZMod 2) (a : ℕ) : Module.End k (V k I) :=
  -mulK (eqv a) + clif par a * clif par (a + 1) * mulK (eqv a)

theorem parity_cases (e : ZMod 2) : e = 0 ∨ e = 1 := by
  generalize e = x; revert x; decide

theorem zsign_zero : SKM.zsign k 0 = 1 := by simp [SKM.zsign]

theorem zsign_one : SKM.zsign k 1 = -1 := by simp [SKM.zsign]

/-- BE2 (1.8), left dot: `τ x_a - (-1)^{|i||j|} x_{a+1} τ` as an operator, for `|i| = 0`. -/
theorem slideL_even {i j : I} (hi : D.parity i = 0) :
    crossOp D Sc i j a * dotOp D i a -
        SKM.zsign k (D.parity i * D.parity j) • (dotOp D i (a + 1) * crossOp D Sc i j a) =
      gam (k := k) D i j • eL D.parity a := by
  have hd : dres (k := k) D i j a = 1 := by simp [dres, hi]
  rw [crossOp, hd, one_mul, dotOp, dotOp, ite_eq_right (by rw [hi]; decide),
    ite_eq_right (by rw [hi]; decide), hi, zero_mul, zsign_zero, one_smul, smul_mul_assoc,
    mul_smul_comm, endSmul_sub, sig_dot_left]

/-- BE2 (1.8), left dot, `|i| = 1`, `|j| = 0`. -/
theorem slideL_odd_even {i j : I} (hi : D.parity i = 1) (hj : D.parity j = 0) :
    crossOp D Sc i j a * dotOp D i a -
        SKM.zsign k (D.parity i * D.parity j) • (dotOp D i (a + 1) * crossOp D Sc i j a) =
      gam (k := k) D i j • (clif D.parity (a + 1) * eL D.parity a) := by
  have hd : dres (k := k) D i j a = 1 := by simp [dres, hj]
  rw [crossOp, hd, one_mul, dotOp, dotOp, ite_eq_left hi, ite_eq_left hi, hj, mul_zero, zsign_zero,
    one_smul, smul_mul_assoc, mul_smul_comm, endSmul_sub]
  congr 1
  have h1 := sig_clif D.parity (qt D Sc) (qt_isEven D Sc) a a
  rw [sw_apply_left] at h1
  rw [← mul_assoc, h1, mul_assoc, mul_assoc, ← mul_sub, sig_dot_left]

/-- BE2 (1.8), left dot, `|i| = |j| = 1`. -/
theorem slideL_odd_odd {i j : I} (hi : D.parity i = 1) (hj : D.parity j = 1) :
    crossOp D Sc i j a * dotOp D i a -
        SKM.zsign k (D.parity i * D.parity j) • (dotOp D i (a + 1) * crossOp D Sc i j a) =
      gam (k := k) D i j • ((clif D.parity a * clif D.parity (a + 1) -
        mulK (fun ν => if oddAt D.parity ν (a + 1) then 1 else 0)) * eL D.parity a) := by
  have hd : dres (k := k) D i j a = clif D.parity a - clif D.parity (a + 1) := by
    simp [dres, hi, hj]
  have h1 := sig_clif D.parity (qt D Sc) (qt_isEven D Sc) a a
  rw [sw_apply_left] at h1
  rw [crossOp, hd, dotOp, dotOp, ite_eq_left hi, ite_eq_left hi, hi, hj, mul_one, zsign_one,
    endNeg_one_smul, endSub_neg_eq_add, smul_mul_assoc, mul_smul_comm, endSmul_add]
  congr 1
  exact slide_odd_left (E := Module.End k (V k I)) (s := sig D.parity (qt D Sc) a)
    (Ya := Y a) (Yb := Y (a + 1)) (Ca := clif D.parity a) (Cb := clif D.parity (a + 1)) h1
    (clif_y_comm D.parity (show a + 1 ≠ a by omega)).symm (y_clif_self D.parity (a + 1))
    (clif_mul_self D.parity (a + 1)) (clif_anticomm D.parity (by omega))
    (sig_dot_left D.parity (qt D Sc) a)

/-- BE2 (1.8), right dot: `x_a τ - (-1)^{|i||j|} τ x_{a+1}` as an operator, for `|j| = 0`. -/
theorem slideR_even {i j : I} (hj : D.parity j = 0) :
    dotOp D j a * crossOp D Sc i j a -
        SKM.zsign k (D.parity i * D.parity j) • (crossOp D Sc i j a * dotOp D j (a + 1)) =
      gam (k := k) D i j • -eR D.parity a := by
  have hd : dres (k := k) D i j a = 1 := by simp [dres, hj]
  rw [crossOp, hd, one_mul, dotOp, dotOp, ite_eq_right (by rw [hj]; decide),
    ite_eq_right (by rw [hj]; decide), hj, mul_zero, zsign_zero, one_smul, smul_mul_assoc,
    mul_smul_comm, endSmul_sub]
  exact congrArg _ ((neg_sub _ _).symm.trans (congrArg _ (sig_dot_right D.parity (qt D Sc) a)))

/-- BE2 (1.8), right dot, `|i| = 0`, `|j| = 1`. -/
theorem slideR_even_odd {i j : I} (hi : D.parity i = 0) (hj : D.parity j = 1) :
    dotOp D j a * crossOp D Sc i j a -
        SKM.zsign k (D.parity i * D.parity j) • (crossOp D Sc i j a * dotOp D j (a + 1)) =
      gam (k := k) D i j • (clif D.parity a * -eR D.parity a) := by
  have hd : dres (k := k) D i j a = 1 := by simp [dres, hi]
  have h1 := sig_clif D.parity (qt D Sc) (qt_isEven D Sc) a (a + 1)
  rw [sw_apply_right] at h1
  rw [crossOp, hd, one_mul, dotOp, dotOp, ite_eq_left hj, ite_eq_left hj, hi, zero_mul,
    zsign_zero, one_smul, smul_mul_assoc, mul_smul_comm, endSmul_sub]
  congr 1
  rw [← mul_assoc (sig _ _ a), h1, mul_assoc, mul_assoc (clif _ a), ← mul_sub]
  exact congrArg _ ((neg_sub _ _).symm.trans (congrArg _ (sig_dot_right D.parity (qt D Sc) a)))

/-- BE2 (1.8), right dot, `|i| = |j| = 1`. -/
theorem slideR_odd_odd {i j : I} (hi : D.parity i = 1) (hj : D.parity j = 1) :
    dotOp D j a * crossOp D Sc i j a -
        SKM.zsign k (D.parity i * D.parity j) • (crossOp D Sc i j a * dotOp D j (a + 1)) =
      gam (k := k) D i j • ((mulK (fun ν => if oddAt D.parity ν a then 1 else 0) +
        clif D.parity a * clif D.parity (a + 1)) * eR D.parity a) := by
  have hd : dres (k := k) D i j a = clif D.parity a - clif D.parity (a + 1) := by
    simp [dres, hi, hj]
  have h1 := sig_clif D.parity (qt D Sc) (qt_isEven D Sc) a (a + 1)
  rw [sw_apply_right] at h1
  rw [crossOp, hd, dotOp, dotOp, ite_eq_left hj, ite_eq_left hj, hi, hj, mul_one, zsign_one,
    endNeg_one_smul, endSub_neg_eq_add, smul_mul_assoc, mul_smul_comm, endSmul_add]
  congr 1
  exact slide_odd_right (E := Module.End k (V k I)) (s := sig D.parity (qt D Sc) a)
    (Ya := Y a) (Yb := Y (a + 1)) (Ca := clif D.parity a) (Cb := clif D.parity (a + 1)) h1
    (y_clif_self D.parity a) (clif_y_comm D.parity (show a ≠ a + 1 by omega)).symm
    (clif_mul_self D.parity a) (clif_anticomm D.parity (by omega))
    (sig_dot_right D.parity (qt D Sc) a)

end Slide

/-! ## The quadratic relation as an operator identity -/

/-- `-(c_a - c_{a+1})²` for two odd colours, else `1`. -/
def dsq (i j : I) (a : ℕ) : Module.End k (V k I) :=
  if D.parity i = 1 ∧ D.parity j = 1 then
    -((clif D.parity a - clif D.parity (a + 1)) * (clif D.parity a - clif D.parity (a + 1)))
  else 1

section Quad

variable (a : ℕ)

theorem anti_sq {E : Type*} [Ring E] {s d : E} (h : s * d = -(d * s)) :
    d * s * (d * s) = -(d * d) * (s * s) := by
  calc d * s * (d * s) = d * (s * d) * s := by noncomm_ring
    _ = _ := by rw [h]; noncomm_ring

omit [DecidableEq I] in
theorem dres_symm (i j : I) : dres (k := k) D j i a = dres D i j a := by
  unfold dres
  by_cases h : D.parity i = 1 ∧ D.parity j = 1
  · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.2, h'.1⟩]

/-- `σ_a` anticommutes with `c_a - c_{a+1}`. -/
theorem sig_clifDiff :
    sig D.parity (qt D Sc) a * (clif D.parity a - clif D.parity (a + 1)) =
      -((clif D.parity a - clif D.parity (a + 1)) * sig D.parity (qt D Sc) a) := by
  have h₀ := sig_clif D.parity (qt D Sc) (qt_isEven D Sc) a a
  have h₁ := sig_clif D.parity (qt D Sc) (qt_isEven D Sc) a (a + 1)
  rw [sw_apply_left] at h₀
  rw [sw_apply_right] at h₁
  rw [mul_sub, h₀, h₁, ← sub_mul]
  exact (congrArg (· * _) (neg_sub _ _).symm).trans (endNeg_mul _ _)


/-- `τ_{ji} τ_{ij}`: the square of a crossing as an operator. -/
theorem crossOp_mul_crossOp (i j : I) :
    crossOp D Sc j i a * crossOp D Sc i j a =
      (gam (k := k) D j i * gam D i j) •
        (dsq D i j a * mulK ((qt D Sc).val a (a + 1))) := by
  rw [crossOp, crossOp, dres_symm, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [← sig_mul_self D.parity (qt D Sc) (qt_isEven D Sc) a]
  unfold dres dsq
  by_cases h : D.parity i = 1 ∧ D.parity j = 1
  · rw [ite_eq_left h, ite_eq_left h]
    exact anti_sq (sig_clifDiff D Sc a)
  · rw [ite_eq_right h, ite_eq_right h, one_mul, one_mul]

end Quad

end OddMath.QuiverHecke.Realization
