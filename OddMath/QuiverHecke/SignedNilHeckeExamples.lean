/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SignedNilHecke
import Categorification.Algebra.NilHeckeDemazure

/-!
# The nilHecke ring as a signed nilHecke family

Multiplication by the variables and the divided differences on `k[x_0, …, x_{m-1}]` form a
signed nilHecke family with `ε = 1` on the block `[0, m)`. Its Demazure elements are the
Demazure operators `π_j = -∂_j x_{j+1}` of `Categorification.Algebra.NilHeckeDemazure`, and its
longest Demazure product is their `demIdem`, the even divided-power idempotent of
Brundan–Ellis, arXiv:1701.04133v2, §11.
-/

namespace OddMath.QuiverHecke.SignedNilHecke

open Categorification.NilHecke Categorification.KLR.KL2.NH

variable (k : Type*) [CommRing k] (m : ℕ)

/-- The polynomial representation of the nilHecke ring is a signed nilHecke family, `ε = 1`. -/
theorem isSignedNilHeckeFamily_nilHecke :
    IsSignedNilHeckeFamily (B := Module.End k (MvPolynomial (Fin m) k)) 1 0 m (xv k m)
      (dd k m) where
  x_comm a b _ ha _ hb _ := by
    rw [xv_of_lt (by omega), xv_of_lt (by omega), Units.val_one, one_smul]
    exact mulX_mul_mulX _ _
  x_t_comm a j _ ha _ _ h₃ h₄ := by
    rw [xv_of_lt (by omega), Units.val_one, one_smul]
    exact (dd_mul_mulX j ⟨a, by omega⟩ h₃ h₄).symm
  t_comm j l _ h _ := by rw [Units.val_one, one_smul]; exact dd_mul_dd h
  t_sq j _ _ := dd_mul_self j
  braid j _ _ := dd_braid j
  t_x j _ h := by
    rw [xv_of_lt (by omega), xv_of_lt (by omega), Units.val_one, one_smul]
    exact dd_mulX_sub_mulX_dd (by omega)
  x_t j _ h := by
    rw [xv_of_lt (by omega), xv_of_lt (by omega), Units.val_one, one_smul]
    exact mulX_dd_sub_dd_mulX (by omega)

/-- Its Demazure elements are the Demazure operators. -/
theorem dem_nilHecke : dem 1 0 m (xv k m) (dd k m) = demOp k m := by
  funext j
  by_cases h : j + 1 < m
  · rw [dem_of (Nat.zero_le j) (by omega), demOp, Units.val_one, one_smul, neg_one_zsmul]
  · rw [dem_of_not (by omega), demOp, dd, dite_eq_right h, zero_mul, smul_zero]

/-- Its longest Demazure product is the even divided-power idempotent `demIdem`. -/
theorem idem_nilHecke : idem 1 0 m (xv k m) (dd k m) 0 m = demIdem k m := by
  rw [idem, dem_nilHecke, Wb, demIdem, demw, wp]
  simp only [zero_add, List.map_id']

end OddMath.QuiverHecke.SignedNilHecke
