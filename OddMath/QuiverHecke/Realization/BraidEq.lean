/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Realization.Braid

/-!
# The braid relation (1.9) with equal end colours

Brundan–Ellis, arXiv:1701.04133v2, (1.9) for colours `(i, j, i)` with `i ≠ j`, for the quiver
Hecke supercategory of §11 acting on the twisted module. By `cross3_sub` the difference of
the two triple crossings is `f_{a,a+2}` times the difference of the two values of `Q̃`; this
file identifies it with BE2's correction term.

For odd `i` the correction term is `(-1)^{|j|} (x_a - x_{a+2}) E` with `E` a divided difference
in `y_a²`, `y_{a+2}²`, by an odd geometric sum (`odd_geom`); for even `i` it is the ordinary
divided difference of `Q_{ij}` in its first variable.
-/

noncomputable section
open scoped TensorProduct
open Finset
namespace OddMath.QuiverHecke.Realization

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] {k : Type*} [CommRing k]

/-! ## Ring identities -/

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (r : ℕ) :
    ∑ s ∈ range (2 * r), f s = ∑ t ∈ range r, (f (2 * t) + f (2 * t + 1)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 2 * (r + 1) = 2 * r + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

theorem zsign_add_one (e : ZMod 2) : SKM.zsign k (e + 1) = -SKM.zsign k e := by
  rcases parity_cases e with rfl | rfl
  · simp [SKM.zsign]
  · rw [show (1 : ZMod 2) + 1 = 0 by decide]; simp [SKM.zsign]

/-- The odd geometric sum: for `A` with `A²` commuting with `C`,
`Σ_{s<2r} (-1)^s A^{2r-1-s} Z C^s = (A - C) Σ_{t<r} (A²)^{r-1-t} Z (C²)^t`. -/
theorem odd_geom {E : Type*} [Ring E] [Algebra k E] {A C Z : E} (hAC : Commute (A * A) C)
    (hZC : Commute Z C) (c : k) (e : ZMod 2) (r : ℕ) :
    ∑ s ∈ range (2 * r), (SKM.zsign k (e + s) * c) • (A ^ (2 * r - 1 - s) * Z * C ^ s) =
      (SKM.zsign k e * c) •
        ((A - C) * ∑ t ∈ range r, (A * A) ^ (r - 1 - t) * Z * (C * C) ^ t) := by
  rw [sum_range_two_mul, mul_sum, smul_sum]
  refine sum_congr rfl fun t ht => ?_
  rw [mem_range] at ht
  have e1 : 2 * r - 1 - 2 * t = 2 * (r - 1 - t) + 1 := by omega
  have e2 : 2 * r - 1 - (2 * t + 1) = 2 * (r - 1 - t) := by omega
  have z1 : SKM.zsign k (e + ((2 * t : ℕ) : ZMod 2)) = SKM.zsign k e := by
    rw [Nat.cast_mul, Nat.cast_two, (by decide : (2 : ZMod 2) = 0), zero_mul, add_zero]
  have z2 : SKM.zsign k (e + ((2 * t + 1 : ℕ) : ZMod 2)) = -SKM.zsign k e := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_two, (by decide : (2 : ZMod 2) = 0), zero_mul,
      zero_add, Nat.cast_one, zsign_add_one]
  have hA1 : A ^ (2 * (r - 1 - t) + 1) = A * (A * A) ^ (r - 1 - t) := by
    rw [pow_succ', pow_mul, sq]
  have hA0 : A ^ (2 * (r - 1 - t)) = (A * A) ^ (r - 1 - t) := by rw [pow_mul, sq]
  have hC0 : C ^ (2 * t) = (C * C) ^ t := by rw [pow_mul, sq]
  have hC1 : C ^ (2 * t + 1) = C * (C * C) ^ t := by rw [pow_succ', pow_mul, sq]
  have hcomm : Commute ((A * A) ^ (r - 1 - t) * Z) C := (hAC.pow_left _).mul_left hZC
  have hsw : (A * A) ^ (r - 1 - t) * Z * (C * (C * C) ^ t) =
      C * ((A * A) ^ (r - 1 - t) * Z * (C * C) ^ t) := by
    rw [← mul_assoc, hcomm.eq, mul_assoc C]
  rw [e1, e2, z1, z2, hA1, hA0, hC0, hC1, hsw, neg_mul, neg_smul, ← sub_eq_add_neg, ← smul_sub,
    sub_mul]
  simp only [mul_assoc]

/-- Three anticommuting Clifford generators `x, y, z`:
`(y - z)(x - z)(x - y) = 2 (x - z)`. -/
theorem clif_triple {E : Type*} [Ring E] {x y z : E} (hx : x * x = 1) (hy : y * y = 1)
    (hz : z * z = 1) (hxy : x * y = -(y * x)) (hyz : y * z = -(z * y)) :
    (y - z) * ((x - z) * (x - y)) = (x - z) + (x - z) := by
  calc (y - z) * ((x - z) * (x - y)) =
        (y - z) * (y - z) * (x - y) + (y - z) * ((x - y) * (x - y)) := by noncomm_ring
    _ = (1 + 1) * (x - y) + (y - z) * (1 + 1) := by
        rw [diff_mul_self hyz, diff_mul_self hxy, hx, hy, hz]
    _ = (x - z) + (x - z) := by noncomm_ring

/-- `(c_a - c_c)(V + c_c V c_a) = 2 (c_a U - c_c W)` for `V = U + W`, `U` odd in `c_a` and
even in `c_c`, `W` the reverse. -/
theorem clif_fO_shape {E : Type*} [Ring E] {C0 C2 U W : E} (h00 : C0 * C0 = 1)
    (h22 : C2 * C2 = 1) (h02 : C0 * C2 = -(C2 * C0)) (hU0 : C0 * U = -(U * C0))
    (hW0 : C0 * W = W * C0) (hU2 : C2 * U = U * C2) (hW2 : C2 * W = -(W * C2)) (Z : E) :
    (C0 - C2) * (((U + W) + C2 * (U + W) * C0) * Z) =
      ((C0 * U - C2 * W) + (C0 * U - C2 * W)) * Z := by
  have h1 : C0 * (C2 * (U + W) * C0) = C2 * U - C2 * W := by
    calc C0 * (C2 * (U + W) * C0) = C0 * (C2 * U) * C0 + C0 * (C2 * W) * C0 := by noncomm_ring
      _ = C0 * U * C2 * C0 - C0 * W * C2 * C0 := by rw [hU2, hW2]; noncomm_ring
      _ = -(U * (C0 * C2) * C0) - W * (C0 * C2) * C0 := by rw [hU0, hW0]; noncomm_ring
      _ = U * C2 * (C0 * C0) + W * C2 * (C0 * C0) := by rw [h02]; noncomm_ring
      _ = C2 * U - C2 * W := by
        rw [h00, mul_one, mul_one, ← hU2, (neg_neg (W * C2)).symm, ← hW2]; noncomm_ring
  have h2 : C2 * (C2 * (U + W) * C0) = U * C0 + W * C0 := by
    calc C2 * (C2 * (U + W) * C0) = (C2 * C2) * (U + W) * C0 := by noncomm_ring
      _ = U * C0 + W * C0 := by rw [h22]; noncomm_ring
  have hU0' : U * C0 = -(C0 * U) := by rw [hU0, neg_neg]
  calc (C0 - C2) * (((U + W) + C2 * (U + W) * C0) * Z) =
        (C0 * U + C0 * W + C0 * (C2 * (U + W) * C0) - C2 * U - C2 * W -
          C2 * (C2 * (U + W) * C0)) * Z := by noncomm_ring
    _ = (C0 * U + C0 * W + (C2 * U - C2 * W) - C2 * U - C2 * W - (-(C0 * U) + C0 * W)) * Z := by
        rw [h1, h2, hU0', hW0]
    _ = ((C0 * U - C2 * W) + (C0 * U - C2 * W)) * Z := by noncomm_ring

/-! ## Divided differences -/

/-- `Σ_{t<r} (-u²)^{r-1-t} (-w²)^t`, the divided difference of `x ↦ (-x²)^r`. -/
def ddo (r : ℕ) (u w : K k) : K k :=
  ∑ t ∈ range r, (-(u ^ 2)) ^ (r - 1 - t) * (-(w ^ 2)) ^ t

/-- `Σ_{s<n} u^{n-1-s} w^s`, the divided difference of `x ↦ x^n`. -/
def dde (n : ℕ) (u w : K k) : K k := ∑ s ∈ range n, u ^ (n - 1 - s) * w ^ s

theorem xpow_odd_sub (r : ℕ) (u w : K k) :
    xpow (1 : ZMod 2) (2 * r) w - xpow 1 (2 * r) u = (u ^ 2 - w ^ 2) * ddo r u w := by
  have h : ddo r u w = ∑ t ∈ range r, (-(w ^ 2)) ^ t * (-(u ^ 2)) ^ (r - 1 - t) :=
    sum_congr rfl fun _ _ => mul_comm _ _
  rw [xpow_two_mul_odd, xpow_two_mul_odd, h, ← geom_sum₂_mul]
  ring

theorem pow_sub_dde (n : ℕ) (u w : K k) : u ^ n - w ^ n = (u - w) * dde n u w := by
  have h : dde n u w = ∑ s ∈ range n, w ^ s * u ^ (n - 1 - s) :=
    sum_congr rfl fun _ _ => mul_comm _ _
  rw [← neg_sub (w ^ n), ← geom_sum₂_mul, h]
  ring

theorem xpow_zero (n : ℕ) (u : K k) : xpow (0 : ZMod 2) n u = u ^ n := by
  simp [xpow]

/-! ## Operators acting on one component -/

section OnComp

variable {J : Type*}

/-- `T` acts on the component `ν` through the coefficient operator `F`. -/
def OnComp (ν : Seq J) (T : Module.End k (V k J)) (F : Module.End k (Coeff k)) : Prop :=
  ∀ m, T (sgl ν m) = sgl ν (Finsupp.mapRange.linearMap F m)

variable {ν : Seq J}

theorem onComp_diag (F : Seq J → Module.End k (Coeff k)) : OnComp ν (diag F) (F ν) :=
  diag_single F ν

theorem onComp_mul {T T' : Module.End k (V k J)} {F F' : Module.End k (Coeff k)}
    (h : OnComp ν T F) (h' : OnComp ν T' F') : OnComp ν (T * T') (F * F') := by
  intro m
  rw [Module.End.mul_apply, h', h]
  congr 1
  ext w
  simp

theorem onComp_add {T T' : Module.End k (V k J)} {F F' : Module.End k (Coeff k)}
    (h : OnComp ν T F) (h' : OnComp ν T' F') : OnComp ν (T + T') (F + F') := by
  intro m
  rw [LinearMap.add_apply, h, h', ← Pi.single_add]
  congr 1
  ext w
  simp

theorem onComp_neg {T : Module.End k (V k J)} {F : Module.End k (Coeff k)}
    (h : OnComp ν T F) : OnComp ν (-T) (-F) := by
  intro m
  rw [LinearMap.neg_apply, h, ← Pi.single_neg]
  congr 1
  ext w
  simp

theorem onComp_sub {T T' : Module.End k (V k J)} {F F' : Module.End k (Coeff k)}
    (h : OnComp ν T F) (h' : OnComp ν T' F') : OnComp ν (T - T') (F - F') := by
  intro m
  rw [LinearMap.sub_apply, h, h', ← Pi.single_sub]
  congr 1
  ext w
  simp

theorem onComp_smul {T : Module.End k (V k J)} {F : Module.End k (Coeff k)} (c : k)
    (h : OnComp ν T F) : OnComp ν (c • T) (c • F) := by
  intro m
  rw [LinearMap.smul_apply, h, ← Pi.single_smul]
  congr 1
  ext w
  simp

theorem onComp_one : OnComp ν (1 : Module.End k (V k J)) 1 := by
  intro m
  simp

theorem onComp_zero : OnComp ν (0 : Module.End k (V k J)) 0 := by
  intro m
  simp

theorem onComp_pow {T : Module.End k (V k J)} {F : Module.End k (Coeff k)}
    (h : OnComp ν T F) (n : ℕ) : OnComp ν (T ^ n) (F ^ n) := by
  induction n with
  | zero => simpa using onComp_one
  | succ n ih => rw [pow_succ, pow_succ]; exact onComp_mul ih h

theorem onComp_sum {ι : Type*} (S : Finset ι) {T : ι → Module.End k (V k J)}
    {F : ι → Module.End k (Coeff k)} (h : ∀ x ∈ S, OnComp ν (T x) (F x)) :
    OnComp ν (∑ x ∈ S, T x) (∑ x ∈ S, F x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using onComp_zero
  | insert x S hx ih =>
    rw [sum_insert hx, sum_insert hx]
    exact onComp_add (h x (mem_insert_self x S)) (ih fun y hy => h y (mem_insert_of_mem hy))

theorem onComp_eq_zero {T : Module.End k (V k J)} {F : Module.End k (Coeff k)}
    (h : OnComp ν T F) (hF : F = 0) (m : M k) : T (sgl ν m) = 0 := by
  rw [h, hF]
  simp

theorem onComp_mulK [DecidableEq J] (g : Seq J → K k) : OnComp ν (mulK g) (scalar (g ν)) :=
  onComp_diag _

theorem onComp_clif [DecidableEq J] {par : J → ZMod 2} {p : ℕ} (h : oddAt par ν p) :
    OnComp ν (clif (k := k) par p) (cliff p) := by
  have := onComp_diag (k := k) (ν := ν) fun ν => if oddAt par ν p then cliff p else 0
  rwa [ite_eq_left h] at this

theorem onComp_fpq [DecidableEq J] (par : J → ZMod 2) (p q : ℕ) :
    OnComp ν (fpq (k := k) par p q) (fP par p q ν) := by
  rw [fpq_eq_diag]
  exact onComp_diag _

end OnComp

/-! ## Coefficient operators of dots and Clifford factors -/

/-- The coefficient operator of a dot of parity `e` at position `p`. -/
def dc (e : ZMod 2) (p : ℕ) : Module.End k (Coeff k) :=
  (if e = 1 then cliff p else 1) * scalar (y p)

theorem dc_zero (p : ℕ) : dc (k := k) 0 p = scalar (y p) := by
  simp [dc]

theorem dc_one (p : ℕ) : dc (k := k) 1 p = cliff p * scalar (y p) := by
  simp [dc]

theorem dc_pow {e : ZMod 2} {n : ℕ} (h : e = 0 ∨ Even n) (p : ℕ) :
    dc (k := k) e p ^ n = scalar (xpow e n (y p)) := by
  rcases parity_cases e with rfl | rfl
  · rw [dc_zero, xpow_zero, scalar_pow]
  · obtain ⟨r, rfl⟩ := h.resolve_left (by decide)
    rw [dc_one, ← two_mul, xpow_two_mul_odd, pow_mul, cliff_scalar_y_sq, scalar_pow]

/-- The coefficient operator of `dd i j p q`. -/
def ddc (D : SKM.Datum I X) (i j : I) (p q : ℕ) : Module.End k (Coeff k) :=
  if D.parity i = 1 ∧ D.parity j = 1 then cliff p - cliff q else 1

theorem scalar_sum {ι : Type*} (S : Finset ι) (f : ι → K k) :
    scalar (∑ x ∈ S, f x) = ∑ x ∈ S, scalar (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih => rw [sum_insert hx, sum_insert hx, scalar_add, ih]

theorem scalar_algebraMap_mul (c : k) (f : K k) :
    scalar (algebraMap k (K k) c * f) = c • scalar f := by
  rw [scalar_mul, scalar_algebraMap, smul_mul_assoc, one_mul]

theorem cliff_scalar_y_self (p : ℕ) :
    cliff p * scalar (y (k := k) p) = -(scalar (y p) * cliff p) := by
  rw [scalar_y_cliff, endNeg_neg]

theorem cliff_scalar_y_ne {p q : ℕ} (h : q ≠ p) :
    cliff p * scalar (y (k := k) q) = scalar (y q) * cliff p := by
  rw [cliff_scalar, reflect_y_of_ne h]

theorem cliff_scalar_of {p : ℕ} {f : K k} (h : reflect p f = f) :
    cliff p * scalar f = scalar f * cliff p := by
  rw [cliff_scalar, h]

section OnCompOps

variable (D : SKM.Datum I X) [DecidableEq I] {ν : Seq I}

theorem onComp_dotOp {i : I} {p : ℕ} (hp : ν p = some i) :
    OnComp ν (dotOp (k := k) D i p) (dc (D.parity i) p) := by
  unfold dotOp dc
  split_ifs with h
  · exact onComp_mul (onComp_clif ((oddAt_iff hp).mpr h)) (onComp_mulK _)
  · rw [one_mul]; exact onComp_mulK _

theorem onComp_dd {i j : I} {p q : ℕ}
    (h : D.parity i = 1 ∧ D.parity j = 1 → oddAt D.parity ν p ∧ oddAt D.parity ν q) :
    OnComp ν (dd (k := k) D i j p q) (ddc D i j p q) := by
  unfold dd ddc
  split_ifs with h'
  · exact onComp_sub (onComp_clif (h h').1) (onComp_clif (h h').2)
  · exact onComp_one

end OnCompOps

/-! ## The value of `Q̃` at the two ends -/

variable (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [DecidableEq I]

/-- The correction coefficient for odd `i`. -/
def eOdd (i j : I) (u v w : K k) : K k :=
  algebraMap k (K k) (Sc.t i j) * ddo (D.dn i j / 2) u w +
    ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      algebraMap k (K k) (Sc.s i j p q) * (xpow (D.parity j) q v * ddo (p / 2) u w)

/-- The correction coefficient for even `i`. -/
def eEv (i j : I) (u v w : K k) : K k :=
  algebraMap k (K k) (Sc.t i j) * dde (D.dn i j) u w +
    ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      algebraMap k (K k) (Sc.s i j p q) * (xpow (D.parity j) q v * dde p u w)

omit [DecidableEq I] in
theorem dn_eq_zero {i j : I} (hd : D.d i j = 0) : D.dn i j = 0 := by
  simp [SKM.Datum.dn, hd]

theorem qL_sub_odd {i j : I} (hi : D.parity i = 1) (hij : i ≠ j) (u v w : K k) :
    qL D Sc i j w v - qL D Sc i j u v = (u ^ 2 - w ^ 2) * eOdd D Sc i j u v w := by
  unfold qL
  rw [ite_eq_right hij, ite_eq_right hij]
  by_cases hd : D.d i j = 0
  · rw [ite_eq_left hd, ite_eq_left hd, eOdd, dn_eq_zero D hd]
    simp [ddo]
  rw [ite_eq_right hd, ite_eq_right hd]
  obtain ⟨r, hr⟩ := even_dn D hi hij
  have h1 : xpow (D.parity i) (D.dn i j) w - xpow (D.parity i) (D.dn i j) u =
      (u ^ 2 - w ^ 2) * ddo (D.dn i j / 2) u w := by
    rw [hi, hr, ← two_mul, Nat.mul_div_cancel_left _ two_pos]
    exact xpow_odd_sub r u w
  have h2 : ∀ p q, algebraMap k (K k) (Sc.s i j p q) *
      (xpow (D.parity i) p w * xpow (D.parity j) q v) -
      algebraMap k (K k) (Sc.s i j p q) * (xpow (D.parity i) p u * xpow (D.parity j) q v) =
      (u ^ 2 - w ^ 2) * (algebraMap k (K k) (Sc.s i j p q) *
        (xpow (D.parity j) q v * ddo (p / 2) u w)) := by
    intro p q
    by_cases hs : Sc.s i j p q = 0
    · simp [hs]
    · obtain ⟨hp, -⟩ := Sc.parity_of_ne_zero hs
      rw [hi, mul_one] at hp
      obtain ⟨r', rfl⟩ := ZMod.natCast_eq_zero_iff_even.mp hp
      rw [← two_mul, Nat.mul_div_cancel_left _ two_pos, hi]
      linear_combination (algebraMap k (K k) (Sc.s i j (2 * r') q) *
        xpow (D.parity j) q v) * xpow_odd_sub r' u w
  have hsum : (∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      algebraMap k (K k) (Sc.s i j p q) * (xpow (D.parity i) p w * xpow (D.parity j) q v)) -
      ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
        algebraMap k (K k) (Sc.s i j p q) * (xpow (D.parity i) p u * xpow (D.parity j) q v) =
      (u ^ 2 - w ^ 2) * ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
        algebraMap k (K k) (Sc.s i j p q) * (xpow (D.parity j) q v * ddo (p / 2) u w) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun q _ => h2 p q
  rw [eOdd]
  linear_combination algebraMap k (K k) (Sc.t i j) * h1 + hsum

theorem qL_sub_even {i j : I} (hi : D.parity i = 0) (hij : i ≠ j) (u v w : K k) :
    qL D Sc i j u v - qL D Sc i j w v = (u - w) * eEv D Sc i j u v w := by
  unfold qL
  rw [ite_eq_right hij, ite_eq_right hij]
  by_cases hd : D.d i j = 0
  · rw [ite_eq_left hd, ite_eq_left hd, eEv, dn_eq_zero D hd]
    simp [dde]
  rw [ite_eq_right hd, ite_eq_right hd]
  have h1 : xpow (D.parity i) (D.dn i j) u - xpow (D.parity i) (D.dn i j) w =
      (u - w) * dde (D.dn i j) u w := by
    rw [hi, xpow_zero, xpow_zero]
    exact pow_sub_dde _ u w
  have h2 : ∀ p q, algebraMap k (K k) (Sc.s i j p q) *
      (xpow (D.parity i) p u * xpow (D.parity j) q v) -
      algebraMap k (K k) (Sc.s i j p q) * (xpow (D.parity i) p w * xpow (D.parity j) q v) =
      (u - w) * (algebraMap k (K k) (Sc.s i j p q) *
        (xpow (D.parity j) q v * dde p u w)) := by
    intro p q
    rw [hi, xpow_zero, xpow_zero]
    linear_combination (algebraMap k (K k) (Sc.s i j p q) * xpow (D.parity j) q v) *
      pow_sub_dde p u w
  have hsum : (∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      algebraMap k (K k) (Sc.s i j p q) * (xpow (D.parity i) p u * xpow (D.parity j) q v)) -
      ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
        algebraMap k (K k) (Sc.s i j p q) * (xpow (D.parity i) p w * xpow (D.parity j) q v) =
      (u - w) * ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
        algebraMap k (K k) (Sc.s i j p q) * (xpow (D.parity j) q v * dde p u w) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun q _ => h2 p q
  rw [eEv]
  linear_combination algebraMap k (K k) (Sc.t i j) * h1 + hsum

omit [DecidableEq I] in
theorem map_eOdd (e : K k ≃ₐ[k] K k) (i j : I) (u v w : K k) :
    e (eOdd D Sc i j u v w) = eOdd D Sc i j (e u) (e v) (e w) := by
  simp [eOdd, ddo, map_sum, map_xpow]

omit [DecidableEq I] in
theorem eOdd_neg_left (i j : I) (u v w : K k) : eOdd D Sc i j (-u) v w = eOdd D Sc i j u v w := by
  simp [eOdd, ddo]

omit [DecidableEq I] in
theorem reflect_eOdd (i j : I) (a : ℕ) :
    reflect a (eOdd D Sc i j (y a) (y (a + 1)) (y (a + 2))) =
      eOdd D Sc i j (y a) (y (a + 1)) (y (a + 2)) := by
  rw [map_eOdd, reflect_y_self, reflect_y_of_ne (by omega), reflect_y_of_ne (by omega),
    eOdd_neg_left]

/-! ## The coefficient of the triple-crossing difference -/

theorem fO_mul_scalar {a c : ℕ} (hac : a ≠ c) {E : K k} (hE : reflect a E = E) :
    fO a c * scalar ((y a ^ 2 - y c ^ 2) * E) =
      (scalar (y a) + scalar (y c) + cliff c * (scalar (y a) + scalar (y c)) * cliff a) *
        scalar E := by
  have hr : reflect a ((y a ^ 2 - y c ^ 2) * E) = (y a ^ 2 - y c ^ 2) * E := by
    simp [hE, reflect_y_of_ne (Ne.symm hac)]
  have hk : hS a c * ((y a ^ 2 - y c ^ 2) * E) = (y (k := k) a + y c) * E := by
    linear_combination ((y a + y c) * E) * hS_mul (k := k) hac
  have hV : scalar ((y (k := k) a + y c) * E) = (scalar (y a) + scalar (y c)) * scalar E := by
    rw [scalar_mul, scalar_add]
  calc fO a c * scalar ((y a ^ 2 - y c ^ 2) * E) =
        scalar (hS a c) * scalar ((y a ^ 2 - y c ^ 2) * E) +
          cliff c * scalar (hS a c) * (cliff a * scalar ((y a ^ 2 - y c ^ 2) * E)) := by
        rw [fO, add_mul, mul_assoc (cliff c * scalar (hS a c))]
    _ = scalar ((y (k := k) a + y c) * E) + cliff c * scalar ((y a + y c) * E) * cliff a := by
        rw [← scalar_mul, hk, cliff_scalar_of hr, ← mul_assoc, mul_assoc (cliff c),
          ← scalar_mul, hk]
    _ = _ := by
        rw [hV]
        simp only [mul_assoc]
        rw [← cliff_scalar_of hE]
        simp only [add_mul, mul_assoc]

theorem clifDiff_fO {a c : ℕ} (hac : a ≠ c) {E : K k} (hE : reflect a E = E) :
    (cliff a - cliff c) * (fO a c * scalar ((y a ^ 2 - y c ^ 2) * E)) =
      (dc 1 a - dc 1 c) * scalar E + (dc 1 a - dc 1 c) * scalar E := by
  rw [fO_mul_scalar hac hE, dc_one, dc_one, ← add_mul]
  exact clif_fO_shape (E := Module.End k (Coeff k)) (cliff_mul_self a) (cliff_mul_self c)
    (cliff_anticomm hac) (cliff_scalar_y_self a) (cliff_scalar_y_ne (Ne.symm hac))
    (cliff_scalar_y_ne hac) (cliff_scalar_y_self c) (scalar E)

theorem combo_odd_even {E : Type*} [Ring E] [Algebra k E] {B F Y : E} (hBF : B * F = Y + Y)
    (h2 : IsUnit (2 : k)) : (-(half : k)) • (B * -((1 : k) • F)) = (1 : k) • Y := by
  have hh : (half : k) * 2 = 1 := Ring.inverse_mul_cancel _ h2
  rw [one_smul, one_smul, mul_neg, hBF, smul_neg, neg_smul, neg_neg, ← two_smul k Y, smul_smul,
    hh, one_smul]

theorem combo_odd_odd {E : Type*} [Ring E] [Algebra k E] {B F Y : E} (hBF : B * F = Y + Y)
    (h2 : IsUnit (2 : k)) :
    (-(half : k)) • ((B + B) * -((-(half : k)) • F)) = (-1 : k) • Y := by
  have hh : (half : k) * 2 = 1 := Ring.inverse_mul_cancel _ h2
  rw [mul_neg, mul_smul_comm, add_mul, hBF, smul_neg, smul_smul, ← two_smul k Y,
    ← two_smul k (2 • Y), smul_smul, smul_smul, ← neg_smul]
  congr 1
  linear_combination (-half * 2 - 1 : k) * hh

/-! ## The coefficients of the correction terms -/

theorem rhs_odd (pj : ZMod 2) (c : k) (a r : ℕ) {z : K k} (hz : reflect (a + 2) z = z) :
    ∑ s ∈ range (2 * r), (SKM.zsign k (1 * (pj + s)) * c) •
        (dc 1 a ^ (2 * r - 1 - s) * scalar z * dc 1 (a + 2) ^ s) =
      (SKM.zsign k pj * c) •
        ((dc 1 a - dc 1 (a + 2)) * scalar (z * ddo r (y a) (y (a + 2)))) := by
  have hsq : ∀ p, dc (k := k) 1 p * dc 1 p = scalar (-(y p ^ 2)) := fun p => by
    rw [← sq, dc_one, cliff_scalar_y_sq]
  have hc : ∀ f : K k, reflect (a + 2) f = f → Commute (scalar f) (dc 1 (a + 2)) := by
    intro f hf
    rw [dc_one]
    exact (show Commute (scalar f) (cliff (a + 2)) from (cliff_scalar_of hf).symm).mul_right
      (scalar_commute _ _)
  have hu : reflect (a + 2) (-(y (k := k) a ^ 2)) = -(y a ^ 2) := by
    simp [reflect_y_of_ne (show a ≠ a + 2 by omega)]
  simp only [one_mul]
  refine (odd_geom (E := Module.End k (Coeff k)) (by rw [hsq]; exact hc _ hu) (hc z hz) c pj
    r).trans ?_
  rw [hsq, hsq]
  congr 2
  rw [ddo, mul_sum, scalar_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [← scalar_pow, ← scalar_pow, ← scalar_mul, ← scalar_mul]
  congr 1
  ring

theorem rhs_even (pj : ZMod 2) (c : k) (a n : ℕ) (z : K k) :
    ∑ s ∈ range n, (SKM.zsign k (0 * (pj + s)) * c) •
        (dc 0 a ^ (n - 1 - s) * scalar z * dc 0 (a + 2) ^ s) =
      c • scalar (z * dde n (y a) (y (a + 2))) := by
  simp only [zero_mul, zsign_zero, one_mul, dc_zero, dde, mul_sum, scalar_sum, smul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [← scalar_pow, ← scalar_pow, ← scalar_mul, ← scalar_mul]
  congr 2
  ring

theorem rhs_odd1 (pj : ZMod 2) (c : k) (a r : ℕ) :
    ∑ s ∈ range (2 * r), (SKM.zsign k (1 * (pj + s)) * c) •
        (dc 1 a ^ (2 * r - 1 - s) * dc 1 (a + 2) ^ s) =
      (SKM.zsign k pj * c) •
        ((dc 1 a - dc 1 (a + 2)) * scalar (ddo (k := k) r (y a) (y (a + 2)))) := by
  have := rhs_odd (k := k) pj c a r (z := 1) (map_one _)
  simp only [scalar_one, mul_one, one_mul] at this ⊢
  exact this

theorem rhs_even1 (pj : ZMod 2) (c : k) (a n : ℕ) :
    ∑ s ∈ range n, (SKM.zsign k (0 * (pj + s)) * c) • (dc 0 a ^ (n - 1 - s) * dc 0 (a + 2) ^ s) =
      c • scalar (dde (k := k) n (y a) (y (a + 2))) := by
  have := rhs_even (k := k) pj c a n 1
  simp only [scalar_one, mul_one, one_mul] at this
  exact this

theorem smul_mul_scalar (z c : k) (Y : Module.End k (Coeff k)) (f : K k) :
    (z * c) • (Y * scalar f) = z • (Y * scalar (algebraMap k (K k) c * f)) := by
  rw [scalar_algebraMap_mul, mul_smul_comm, smul_smul]

theorem sum_smul_mul_scalar {ι : Type*} (S : Finset ι) (z : k) (Y : Module.End k (Coeff k))
    (g : ι → K k) : ∑ x ∈ S, z • (Y * scalar (g x)) = z • (Y * scalar (∑ x ∈ S, g x)) := by
  rw [scalar_sum, mul_sum, smul_sum]

theorem sub_sub_eq_zero_of {E : Type*} [AddCommGroup E] {L L' A B : E} (h : L = L')
    (h' : L' - A - B = 0) : L - A - B = 0 := h ▸ h'

theorem final_comb {E : Type*} [Ring E] [Module k E] (z : k) (Y S SA SB : E) (h : S = SA + SB) :
    z • (Y * S) - z • (Y * SA) - z • (Y * SB) = 0 := by
  rw [h, mul_add, smul_add]
  abel

theorem final_comb' {E : Type*} [AddCommGroup E] (S SA SB : E) (h : S = SA + SB) :
    S - SA - SB = 0 := by
  rw [h]
  abel

/-! ## The braid relation with equal end colours -/

theorem val_diff {i j : I} {ν : Seq I} {a : ℕ} (hi : ν a = some i) (hj : ν (a + 1) = some j)
    (hl : ν (a + 2) = some i) :
    (qt D Sc).val (a + 1) (a + 2) ν - (qt D Sc).val a (a + 1) ν =
      algebraMap k (K k) (kap D i j) *
        (qL D Sc i j (y (a + 2)) (y (a + 1)) - qL D Sc i j (y a) (y (a + 1))) := by
  have e1 : (qt D Sc).val (a + 1) (a + 2) ν =
      algebraMap k (K k) (kap D j i) * qL D Sc j i (y (a + 1)) (y (a + 2)) := by
    simp only [PairFn.val, hj, hl]; rfl
  have e2 : (qt D Sc).val a (a + 1) ν =
      algebraMap k (K k) (kap D i j) * qL D Sc i j (y a) (y (a + 1)) := by
    simp only [PairFn.val, hi, hj]; rfl
  rw [e1, e2, kap_symm, qL_symm]
  ring

theorem fP_eq_of {i : I} {ν : Seq I} {a c : ℕ} (ha : ν a = some i) (hc : ν c = some i) :
    fP (k := k) D.parity a c ν =
      scalar (hS a c) + if D.parity i = 1 then cliff c * scalar (hS a c) * cliff a else 0 := by
  unfold fP
  rw [ite_eq_left (ha.trans hc.symm)]
  by_cases h : D.parity i = 1
  · rw [ite_eq_left ((oddAt_iff ha).mpr h), ite_eq_left h]
  · rw [ite_eq_right (mt (oddAt_iff ha).mp h), ite_eq_right h]

/-- BE2 (1.9), the braid relation for colours `(i, j, i)` with `i ≠ j`, on the component of
`(i, j, i)`. -/
theorem braidEq_single {i j : I} (hij : i ≠ j) {ν : Seq I} {a : ℕ} (hi : ν a = some i)
    (hj : ν (a + 1) = some j) (hl : ν (a + 2) = some i) (m : M k) :
    (crossOp D Sc j i a * crossOp D Sc i i (a + 1) * crossOp D Sc i j a -
        crossOp D Sc i j (a + 1) * crossOp D Sc i i a * crossOp D Sc j i (a + 1) -
        ∑ s ∈ range (D.dn i j), (SKM.zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
          (dotOp D i a ^ (D.dn i j - 1 - s) * dotOp D i (a + 2) ^ s) -
        ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i), ∑ s ∈ range p,
          (SKM.zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
            (dotOp D i a ^ (p - 1 - s) * dotOp D j (a + 1) ^ q * dotOp D i (a + 2) ^ s) :
          Module.End k (V k I)) (sgl ν m) = 0 := by
  rw [cross3_sub]
  refine onComp_eq_zero (onComp_sub (onComp_sub (onComp_smul _ (onComp_mul (onComp_mul
    (onComp_dd D ?_) (onComp_mul (onComp_dd D ?_) (onComp_dd D ?_)))
    (onComp_neg (onComp_mul (onComp_fpq _ _ _) (onComp_mulK _)))))
    (onComp_sum _ fun s _ => onComp_smul _ (onComp_mul (onComp_pow (onComp_dotOp D hi) _)
      (onComp_pow (onComp_dotOp D hl) _))))
    (onComp_sum _ fun p _ => onComp_sum _ fun q _ => onComp_sum _ fun s _ => onComp_smul _
      (onComp_mul (onComp_mul (onComp_pow (onComp_dotOp D hi) _)
        (onComp_pow (onComp_dotOp D hj) _)) (onComp_pow (onComp_dotOp D hl) _)))) ?_ m
  · exact fun h => ⟨(oddAt_iff hj).mpr h.2, (oddAt_iff hl).mpr h.1⟩
  · exact fun h => ⟨(oddAt_iff hi).mpr h.1, (oddAt_iff hl).mpr h.1⟩
  · exact fun h => ⟨(oddAt_iff hi).mpr h.2, (oddAt_iff hj).mpr h.1⟩
  rw [Pi.sub_apply, val_diff D Sc hi hj hl, fP_eq_of D hi hl,
    show gam (k := k) D j i * gam D i i * gam D i j = gam D i i by simp [gam, hij, Ne.symm hij]]
  rcases parity_cases (D.parity i) with hpi | hpi
  · -- even `i`: everything is a scalar
    have hpq : ∀ p q, Sc.s i j p q ≠ 0 → D.parity j = 0 ∨ Even q := by
      intro p q hs
      rcases parity_cases (D.parity j) with h | h
      · exact Or.inl h
      · have := (Sc.parity_of_ne_zero hs).2
        rw [h, mul_one] at this
        exact Or.inr (ZMod.natCast_eq_zero_iff_even.mp this)
    have hK : hS (k := k) a (a + 2) * (algebraMap k (K k) 1 *
        (qL D Sc i j (y (a + 2)) (y (a + 1)) - qL D Sc i j (y a) (y (a + 1)))) =
        -eEv D Sc i j (y a) (y (a + 1)) (y (a + 2)) := by
      rw [map_one, one_mul]
      linear_combination (-hS (k := k) a (a + 2)) * qL_sub_even D Sc hpi hij (y a) (y (a + 1))
        (y (a + 2)) - eEv D Sc i j (y a) (y (a + 1)) (y (a + 2)) *
          hS_mul (k := k) (show a ≠ a + 2 by omega)
    have hR2 : ∀ p q, ∑ s ∈ range p, (SKM.zsign k (0 * (D.parity j + s)) * Sc.s i j p q) •
        (dc 0 a ^ (p - 1 - s) * dc (D.parity j) (a + 1) ^ q * dc 0 (a + 2) ^ s) =
        Sc.s i j p q • scalar (xpow (D.parity j) q (y (a + 1)) * dde (k := k) p (y a) (y (a + 2))) := by
      intro p q
      by_cases hs : Sc.s i j p q = 0
      · simp [hs]
      · rw [dc_pow (hpq p q hs)]
        exact rhs_even _ _ a p _
    have hd : ∀ j' i' p q, D.parity i' = 0 → ddc (k := k) D j' i' p q = 1 := by
      intro j' i' p q h
      simp [ddc, h]
    have hd' : ddc (k := k) D i j (a + 1) (a + 2) = 1 := by simp [ddc, hpi]
    rw [hd', hd _ _ _ _ hpi, hd _ _ _ _ hpi, show kap (k := k) D i j = 1 by simp [kap, hpi],
      show gam (k := k) D i i = 1 by simp [gam, hpi], ite_eq_right (by rw [hpi]; decide),
      add_zero, ← scalar_mul, hK, scalar_neg, endNeg_neg, one_mul, one_mul, one_smul, hpi,
      rhs_even1, sum_congr rfl fun p _ => sum_congr rfl fun q _ => hR2 p q]
    simp only [← scalar_algebraMap_mul, ← scalar_sum]
    exact final_comb' (E := Module.End k (Coeff k)) _ _ _ (by rw [← scalar_add]; rfl)
  · -- odd `i`
    have h2 : IsUnit (2 : k) := Sc.two_isUnit ⟨i, hpi⟩
    have hBF := clifDiff_fO (k := k) (show a ≠ a + 2 by omega) (reflect_eOdd D Sc i j a)
    obtain ⟨r, hr⟩ := even_dn D hpi hij
    have hR1 : ∑ s ∈ range (D.dn i j), (SKM.zsign k (1 * (D.parity j + s)) * (Sc.t i j : k)) •
        (dc 1 a ^ (D.dn i j - 1 - s) * dc 1 (a + 2) ^ s) =
        (SKM.zsign k (D.parity j) * (Sc.t i j : k)) •
          ((dc 1 a - dc 1 (a + 2)) * scalar (ddo (k := k) (D.dn i j / 2) (y a) (y (a + 2)))) := by
      rw [hr, ← two_mul, Nat.mul_div_cancel_left _ two_pos]
      exact rhs_odd1 _ _ a r
    have hR2 : ∀ p q, ∑ s ∈ range p, (SKM.zsign k (1 * (D.parity j + s)) * Sc.s i j p q) •
        (dc 1 a ^ (p - 1 - s) * dc (D.parity j) (a + 1) ^ q * dc 1 (a + 2) ^ s) =
        (SKM.zsign k (D.parity j) * Sc.s i j p q) • ((dc 1 a - dc 1 (a + 2)) *
          scalar (xpow (D.parity j) q (y (a + 1)) * ddo (k := k) (p / 2) (y a) (y (a + 2)))) := by
      intro p q
      by_cases hs : Sc.s i j p q = 0
      · simp [hs]
      · obtain ⟨hp, hq⟩ := Sc.parity_of_ne_zero hs
        rw [hpi, mul_one] at hp
        obtain ⟨r', rfl⟩ := ZMod.natCast_eq_zero_iff_even.mp hp
        have hq' : D.parity j = 0 ∨ Even q := by
          rcases parity_cases (D.parity j) with h | h
          · exact Or.inl h
          · rw [h, mul_one] at hq
            exact Or.inr (ZMod.natCast_eq_zero_iff_even.mp hq)
        rw [dc_pow hq', ← two_mul, Nat.mul_div_cancel_left _ two_pos]
        exact rhs_odd _ _ a r' (by rw [map_xpow, reflect_y_of_ne (by omega)])
    rw [show gam (k := k) D i i = -half by simp [gam, hpi], ite_eq_left hpi,
      qL_sub_odd D Sc hpi hij, scalar_algebraMap_mul, mul_smul_comm,
      show scalar (hS (k := k) a (a + 2)) + cliff (a + 2) * scalar (hS a (a + 2)) * cliff a =
        fO a (a + 2) from rfl, hpi, hR1, sum_congr rfl fun p _ => sum_congr rfl fun q _ => hR2 p q]
    simp only [smul_mul_scalar, sum_smul_mul_scalar]
    rcases parity_cases (D.parity j) with hpj | hpj
    · have hd1 : ddc (k := k) D i j (a + 1) (a + 2) = 1 := by simp [ddc, hpj]
      have hd2 : ddc (k := k) D i i a (a + 2) = cliff a - cliff (a + 2) := by simp [ddc, hpi]
      have hd3 : ddc (k := k) D j i a (a + 1) = 1 := by simp [ddc, hpj]
      rw [hd1, hd2, hd3, show kap (k := k) D i j = 1 by simp [kap, hpj], one_mul, mul_one, hpj,
        zsign_zero]
      refine sub_sub_eq_zero_of (combo_odd_even (E := Module.End k (Coeff k)) hBF h2) ?_
      exact final_comb (E := Module.End k (Coeff k)) _ _ _ _ _ (by rw [← scalar_add, eOdd, hpj])
    · have hd1 : ddc (k := k) D i j (a + 1) (a + 2) = cliff (a + 1) - cliff (a + 2) := by
        simp [ddc, hpi, hpj]
      have hd2 : ddc (k := k) D i i a (a + 2) = cliff a - cliff (a + 2) := by simp [ddc, hpi]
      have hd3 : ddc (k := k) D j i a (a + 1) = cliff a - cliff (a + 1) := by simp [ddc, hpi, hpj]
      have hP := clif_triple (E := Module.End k (Coeff k)) (cliff_mul_self a)
        (cliff_mul_self (a + 1)) (cliff_mul_self (a + 2)) (cliff_anticomm (show a ≠ a + 1 by omega))
        (cliff_anticomm (show a + 1 ≠ a + 2 by omega))
      rw [hd1, hd2, hd3, hP, show kap (k := k) D i j = -half by simp [kap, hij, hpi, hpj], hpj,
        zsign_one]
      refine sub_sub_eq_zero_of (combo_odd_odd (E := Module.End k (Coeff k)) hBF h2) ?_
      exact final_comb (E := Module.End k (Coeff k)) _ _ _ _ _ (by rw [← scalar_add, eOdd, hpj])

end OddMath.QuiverHecke.Realization
