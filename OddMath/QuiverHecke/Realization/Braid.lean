/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Realization.Relations

/-!
# The braid relations (1.9) on the twisted module

Brundan–Ellis, arXiv:1701.04133v2, (1.9) for the quiver Hecke supercategory of §11. The
Clifford factors of the three crossings move to the left of the operators `σ`, where they
agree for both sides of the braid relation; the remaining difference is KKT's
`f_{a,a+2}(Q̃_{a+1,a+2} - Q̃_{a,a+1})` (`sig_braid`).
-/

noncomputable section
open scoped TensorProduct
namespace OddMath.QuiverHecke.Realization

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] {k : Type*} [CommRing k]
variable (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-! ## Clifford factors at arbitrary positions -/

/-- `c_p - c_q` if both colours are odd, else `1`. -/
def dd (i j : I) (p q : ℕ) : Module.End k (V k I) :=
  if D.parity i = 1 ∧ D.parity j = 1 then clif D.parity p - clif D.parity q else 1

theorem dres_eq_dd (i j : I) (a : ℕ) : dres (k := k) D i j a = dd D i j a (a + 1) := rfl

theorem sw_add_two (a : ℕ) : sw a (a + 2) = a + 2 := sw_apply_of_ne (by omega) (by omega)

theorem sw_succ_left (a : ℕ) : sw (a + 1) a = a := sw_apply_of_ne (by omega) (by omega)

theorem sw_succ_self (a : ℕ) : sw (a + 1) (a + 1) = a + 2 := sw_apply_left (a + 1)

theorem sw_succ_two (a : ℕ) : sw (a + 1) (a + 2) = a + 1 := sw_apply_right (a + 1)

variable [DecidableEq I]

theorem sig_dd (a : ℕ) (i j : I) (p q : ℕ) :
    sig D.parity (qt D Sc) a * dd (k := k) D i j p q =
      dd D i j (sw a p) (sw a q) * sig D.parity (qt D Sc) a := by
  unfold dd
  split_ifs
  · rw [mul_sub, sig_clif D.parity (qt D Sc) (qt_isEven D Sc),
      sig_clif D.parity (qt D Sc) (qt_isEven D Sc), sub_mul]
  · rw [mul_one, one_mul]

theorem sig_dd_assoc (a : ℕ) (i j : I) (p q : ℕ) (Z : Module.End k (V k I)) :
    sig D.parity (qt D Sc) a * (dd D i j p q * Z) =
      dd D i j (sw a p) (sw a q) * (sig D.parity (qt D Sc) a * Z) := by
  rw [← mul_assoc, sig_dd, mul_assoc]

set_option linter.unusedSimpArgs false in
/-- The first side of the braid relation: crossings `(i,j)` at `a`, `(i,l)` at `a+1`, `(j,l)`
at `a`, applied in this order. -/
theorem cross3_left (i j l : I) (a : ℕ) :
    crossOp D Sc j l a * crossOp D Sc i l (a + 1) * crossOp D Sc i j a =
      (gam (k := k) D j l * gam D i l * gam D i j) •
        (dd D j l a (a + 1) * (dd D i l a (a + 2) * (dd D i j (a + 1) (a + 2) *
          (sig D.parity (qt D Sc) a * (sig D.parity (qt D Sc) (a + 1) *
            sig D.parity (qt D Sc) a))))) := by
  simp only [crossOp, dres_eq_dd, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc,
    sig_dd_assoc, sw_apply_left, sw_apply_right, sw_add_two, sw_succ_left, sw_succ_self,
    sw_succ_two]
  congr 1; ring

set_option linter.unusedSimpArgs false in
/-- The second side of the braid relation: crossings `(j,l)` at `a+1`, `(i,l)` at `a`, `(i,j)`
at `a+1`, applied in this order. -/
theorem cross3_right (i j l : I) (a : ℕ) :
    crossOp D Sc i j (a + 1) * crossOp D Sc i l a * crossOp D Sc j l (a + 1) =
      (gam (k := k) D j l * gam D i l * gam D i j) •
        (dd D i j (a + 1) (a + 2) * (dd D i l a (a + 2) * (dd D j l a (a + 1) *
          (sig D.parity (qt D Sc) (a + 1) * (sig D.parity (qt D Sc) a *
            sig D.parity (qt D Sc) (a + 1)))))) := by
  simp only [crossOp, dres_eq_dd, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc,
    sig_dd_assoc, sw_apply_left, sw_apply_right, sw_add_two, sw_succ_left, sw_succ_self,
    sw_succ_two]

/-! ## The Clifford prefactors agree -/

theorem commute_sq_of_anticomm {E : Type*} [Ring E] {c d : E} (h : c * d = -(d * c)) :
    Commute (c * c) d := by
  show c * c * d = d * (c * c)
  calc c * c * d = c * (c * d) := by noncomm_ring
    _ = -(c * (d * c)) := by rw [h]; noncomm_ring
    _ = d * (c * c) := by rw [← mul_assoc, h]; noncomm_ring

theorem diff_mul_self {E : Type*} [Ring E] {x y : E} (h : x * y = -(y * x)) :
    (x - y) * (x - y) = x * x + y * y := by
  have : (x - y) * (x - y) = x * x + y * y - (x * y + y * x) := by noncomm_ring
  rw [this, h, neg_add_cancel, sub_zero]

/-- `A (A + C) C = C (A + C) A` when the squares of `A` and `C` commute with `C` and `A`. -/
theorem braid_prefactor {E : Type*} [Ring E] {A C : E} (hA : Commute (A * A) C)
    (hC : Commute (C * C) A) : A * ((A + C) * C) = C * ((A + C) * A) := by
  calc A * ((A + C) * C) = A * A * C + A * (C * C) := by noncomm_ring
    _ = C * (A * A) + C * C * A := by rw [hA.eq, ← hC.eq]
    _ = C * ((A + C) * A) := by noncomm_ring

omit [DecidableEq I] in
/-- For three odd colours: `(c_a - c_{a+1})(c_a - c_{a+2})(c_{a+1} - c_{a+2})` is unchanged
by reversing the order of the factors. -/
theorem clif_prefactor (a : ℕ) :
    (clif D.parity a - clif D.parity (a + 1)) * ((clif D.parity a - clif D.parity (a + 2)) *
        (clif D.parity (a + 1) - clif D.parity (a + 2))) =
      (clif D.parity (a + 1) - clif D.parity (a + 2)) *
        ((clif D.parity a - clif D.parity (a + 2)) *
          (clif (k := k) D.parity a - clif D.parity (a + 1))) := by
  have e : clif (k := k) (I := I) D.parity a - clif D.parity (a + 2) =
      (clif D.parity a - clif D.parity (a + 1)) +
        (clif D.parity (a + 1) - clif D.parity (a + 2)) := (sub_add_sub_cancel _ _ _).symm
  have h01 := clif_anticomm (k := k) (I := I) D.parity (show a ≠ a + 1 by omega)
  have h02 := clif_anticomm (k := k) (I := I) D.parity (show a ≠ a + 2 by omega)
  have h12 := clif_anticomm (k := k) (I := I) D.parity (show a + 1 ≠ a + 2 by omega)
  have h10 := clif_anticomm (k := k) (I := I) D.parity (show a + 1 ≠ a by omega)
  have h20 := clif_anticomm (k := k) (I := I) D.parity (show a + 2 ≠ a by omega)
  have h21 := clif_anticomm (k := k) (I := I) D.parity (show a + 2 ≠ a + 1 by omega)
  rw [e]
  refine braid_prefactor ?_ ?_
  · rw [diff_mul_self h01]
    refine Commute.add_left ((commute_sq_of_anticomm h01).sub_right
      (commute_sq_of_anticomm h02)) ((Commute.mul_left (Commute.refl _) (Commute.refl _)).sub_right
      (commute_sq_of_anticomm h12))
  · rw [diff_mul_self h12]
    refine Commute.add_left ((commute_sq_of_anticomm h10).sub_right
      (Commute.mul_left (Commute.refl _) (Commute.refl _)))
      ((commute_sq_of_anticomm h20).sub_right (commute_sq_of_anticomm h21))

omit [DecidableEq I] in
variable {D} in
theorem prefactor_eq (i j l : I) (a : ℕ) :
    dd (k := k) D j l a (a + 1) * (dd D i l a (a + 2) * dd D i j (a + 1) (a + 2)) =
      dd D i j (a + 1) (a + 2) * (dd D i l a (a + 2) * dd D j l a (a + 1)) := by
  unfold dd
  split_ifs with h1 h2 h3 <;> first
    | exact clif_prefactor D a
    | (exfalso; tauto)
    | simp only [one_mul, mul_one]

/-! ## The braid relation -/

/-- The difference of the two sides of the braid relation, with the Clifford factors on the
left. -/
theorem cross3_sub (i j l : I) (a : ℕ) :
    crossOp D Sc j l a * crossOp D Sc i l (a + 1) * crossOp D Sc i j a -
        crossOp D Sc i j (a + 1) * crossOp D Sc i l a * crossOp D Sc j l (a + 1) =
      (gam (k := k) D j l * gam D i l * gam D i j) •
        (dd D i j (a + 1) (a + 2) * (dd D i l a (a + 2) * dd D j l a (a + 1)) *
          -(fpq D.parity a (a + 2) * mulK ((qt D Sc).val (a + 1) (a + 2) -
            (qt D Sc).val a (a + 1)))) := by
  rw [cross3_left, cross3_right, endSmul_sub]
  congr 1
  have hP := prefactor_eq (k := k) (D := D) i j l a
  have hb := sig_braid D.parity (qt D Sc) (qt_isEven D Sc) a
  rw [show a + 1 + 1 = a + 2 from rfl] at hb
  rw [← hb, neg_sub]
  simp only [← mul_assoc] at hP ⊢
  rw [hP, mul_sub]
  simp only [← mul_assoc]

theorem eval_fpq_mulK {a b : ℕ} (g : Seq I → K k) {ν : Seq I} (m : M k)
    (h : ν a ≠ ν b ∨ g ν = 0) :
    (fpq D.parity a b * mulK g : Module.End k (V k I)) (sgl ν m) = 0 := by
  rw [Module.End.mul_apply, mulK_eq_diag, diag_single, fpq_eq_diag, diag_single]
  rcases h with h | h
  · simp [fP_eq_zero D.parity h]
  · simp [h]

/-- BE2 (1.9), the braid relation for `¬(i = l ∧ i ≠ j)`, on the component of `(i, j, l)`. -/
theorem braid_single {i j l : I} (h : ¬(i = l ∧ i ≠ j)) {ν : Seq I} {a : ℕ}
    (hi : ν a = some i) (hj : ν (a + 1) = some j) (hl : ν (a + 2) = some l) (m : M k) :
    (crossOp D Sc j l a * crossOp D Sc i l (a + 1) * crossOp D Sc i j a -
        crossOp D Sc i j (a + 1) * crossOp D Sc i l a * crossOp D Sc j l (a + 1) :
          Module.End k (V k I)) (sgl ν m) = 0 := by
  rw [cross3_sub, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.neg_apply]
  rw [eval_fpq_mulK D _ m, neg_zero, map_zero, smul_zero]
  by_cases hil : i = l
  · subst hil
    have hij : i = j := by tauto
    subst hij
    right
    simp [PairFn.val, qt, hi, hj, hl, qL]
  · left
    rw [hi, hl]
    simpa using hil

end OddMath.QuiverHecke.Realization
