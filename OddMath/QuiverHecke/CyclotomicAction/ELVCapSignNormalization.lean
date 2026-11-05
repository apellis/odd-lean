import StringDiagrams.Super.SVec
import Mathlib.Data.Nat.Choose.Basic

/-! # The sign in the prescribed dotted cap row

The scalar in DeformedMatrixComparison (5) is
(-1)^(n(n+1)/2). For an odd operator T on a superspace, composing T with
source parity changes its iterates by exactly this scalar and output parity.
This linear-algebra identity is the sign step used by the concrete shifted
counit comparison; it does not assert an action or a matrix inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {k : Type u} [CommRing k]

def capRowSign (n : ℕ) : k := (-1 : k) ^ (n + 1).choose 2

theorem capRowSign_eq (n : ℕ) :
    capRowSign (k := k) n = (-1 : k) ^ (n * (n + 1) / 2) := by
  unfold capRowSign
  rw [Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm (n + 1) n]

private theorem sign_natCast (n : ℕ) :
    sign k (n : ZMod 2) = (-1 : k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, sign_add, ih, sign_one, pow_succ]

theorem capRowSign_succ (n : ℕ) :
    capRowSign (k := k) (n + 1) =
      sign k ((n + 1 : ℕ) : ZMod 2) * capRowSign (k := k) n := by
  have h : (n + 1 + 1).choose 2 = (n + 1) + (n + 1).choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ (n + 1) 1
  unfold capRowSign
  rw [h, pow_add, sign_natCast]

/-- The prescribed cap scalar cancels the sign introduced by composing an
odd dot with source parity. The odd-operator premise is discharged by the
concrete module dot in the shifted-counit comparison. -/
theorem capRowSign_sgn_iterate (V : SVec k) (T : V →ₗ[k] V)
    (hT : T ∈ SVec.parityHom V V 1) (n : ℕ) (z : V) :
    capRowSign (k := k) n • V.sgn (n : ZMod 2)
      ((T.comp (V.sgn 1))^[n] z) = T^[n] z := by
  induction n with
  | zero => simp [capRowSign]
  | succ n ih =>
    let w := (T.comp (V.sgn 1))^[n] z
    have hp : ((n + 1 : ℕ) : ZMod 2) + 1 = (n : ZMod 2) := by
      rw [Nat.cast_add, Nat.cast_one, add_assoc, SVec.zmod2_one_add_one, add_zero]
    have hphi : V.sgn ((n + 1 : ℕ) : ZMod 2) (V.sgn 1 w) =
        V.sgn (n : ZMod 2) w := by
      have h := congrArg (fun f : V →ₗ[k] V => f w)
        (SVec.sgn_comp_sgn V ((n + 1 : ℕ) : ZMod 2) 1)
      simpa only [LinearMap.comp_apply, hp] using h
    have hc := congrArg (fun f : V →ₗ[k] V => f (V.sgn 1 w))
      (SVec.sgn_comp_of_mem hT ((n + 1 : ℕ) : ZMod 2))
    simp only [LinearMap.comp_apply, SVec.coe_toLinearMap, LinearMap.smul_apply,
      one_mul, hphi] at hc
    have hs : V.sgn ((n + 1 : ℕ) : ZMod 2)
        ((T.comp (V.sgn 1))^[n + 1] z) =
        sign k ((n + 1 : ℕ) : ZMod 2) • T (V.sgn (n : ZMod 2) w) := by
      rw [Function.iterate_succ_apply']
      exact hc
    have he : capRowSign (k := k) (n + 1) *
        sign k ((n + 1 : ℕ) : ZMod 2) = capRowSign (k := k) n := by
      rw [capRowSign_succ, mul_right_comm, sign_mul_self, one_mul]
    calc
      capRowSign (k := k) (n + 1) • V.sgn ((n + 1 : ℕ) : ZMod 2)
          ((T.comp (V.sgn 1))^[n + 1] z) =
          capRowSign (k := k) n • T (V.sgn (n : ZMod 2) w) := by
        rw [hs, smul_smul, he]
      _ = T (capRowSign (k := k) n • V.sgn (n : ZMod 2) w) := (map_smul T _ _).symm
      _ = T (T^[n] z) := congrArg T ih
      _ = T^[n + 1] z := (Function.iterate_succ_apply' _ _ _).symm

end OddMath.QuiverHecke.ELVOld
