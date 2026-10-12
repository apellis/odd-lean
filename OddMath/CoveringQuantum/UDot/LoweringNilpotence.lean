/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.IntegrableWeightOperators

/-!
# Local nilpotence of the original quotient lowering operators

The monic end of the actual Serre relation propagates nilpotence through
creation words. No division by a Serre coefficient or dominance is needed.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot.GenericVerma

section Serre
variable {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]

private theorem pow_apply_zero_of_le (A : Module.End k M) {v : M} {n N : ℕ}
    (h : (A ^ n) v = 0) (hn : n ≤ N) : (A ^ N) v = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm n d, pow_add, Module.End.mul_apply, h, map_zero]

/-- A monic Serre relation preserves locally nilpotent vectors, over any
commutative ring. The deliberately loose bound avoids dividing coefficients. -/
theorem serre_nilpotence_bound (A B : Module.End k M) (m : ℕ) (c : ℕ → k)
    (hc : c 0 = 1)
    (hs : ∑ r ∈ Finset.range (m + 1), c r • (A ^ (m - r) * B * A ^ r) = 0)
    (n : ℕ) (v : M) (hv : (A ^ n) v = 0) : (A ^ (n * m)) (B v) = 0 := by
  induction n generalizing v with
  | zero =>
    have hz : v = 0 := by simpa using hv
    simp [hz]
  | succ n ih =>
    have he := congrArg (fun f : Module.End k M ↦ (A ^ (n * m)) (f v)) hs
    rw [Finset.sum_range_succ'] at he
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      map_add, map_sum, map_smul, LinearMap.zero_apply, map_zero,
      hc, Nat.sub_zero, pow_zero, mul_one, one_smul, Module.End.mul_apply] at he
    have hz : ∑ r ∈ Finset.range m,
        c (r + 1) • (A ^ (n * m)) ((A ^ (m - (r + 1))) (B ((A ^ (r + 1)) v))) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      have hv' : (A ^ n) ((A ^ (r + 1)) v) = 0 := by
        rw [← Module.End.mul_apply, ← pow_add]
        exact pow_apply_zero_of_le A hv (by omega)
      have hi := ih ((A ^ (r + 1)) v) hv'
      have hi' := pow_apply_zero_of_le A hi (Nat.le_add_right (n * m) (m - (r + 1)))
      rw [← Module.End.mul_apply, ← pow_add, hi', smul_zero]
    rw [hz, zero_add] at he
    simpa only [Nat.succ_mul, pow_add, Module.End.mul_apply] using he

end Serre

open PreF Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ : X)

/-- Powers of the original lowering operator are left creation before projection. -/
theorem integrableChevalley_false_pow_mk (i : I) (n : ℕ)
    (x : D.serreF Coefficients.q pi) :
    (integrableChevalley D hD Λ false i ^ n) (toIntegrable D hD Λ x) =
      toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i ^ n) * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, ih, integrableChevalley_mk,
      chevalley_false_apply, map_mul, mul_assoc]

/-- The defining integrability relation kills the vacuum for every highest weight. -/
theorem integrableChevalley_false_vacuum (i : I) :
    (integrableChevalley D hD Λ false i ^ ((D.h i Λ).toNat + 1))
      (toIntegrable D hD Λ 1) = 0 := by
  rw [integrableChevalley_false_pow_mk, mul_one]
  exact toIntegrable_generator D hD Λ i

/-- Nilpotence under a fixed lowering generator survives every lowering generator,
using the actual quotient Serre relation for unequal indices. -/
theorem integrableChevalley_false_preserves_nilpotence (i j : I)
    (x : IntegrableQuotient D hD Λ)
    (hx : ∃ n : ℕ, (integrableChevalley D hD Λ false i ^ n) x = 0) :
    ∃ n : ℕ, (integrableChevalley D hD Λ false i ^ n)
      (integrableChevalley D hD Λ false j x) = 0 := by
  obtain ⟨n, hn⟩ := hx
  by_cases hij : i = j
  · subst j
    refine ⟨n, ?_⟩
    rw [← Module.End.mul_apply, ← pow_succ]
    exact pow_apply_zero_of_le _ hn (Nat.le_succ n)
  · refine ⟨n * D.serreDeg i j, ?_⟩
    exact serre_nilpotence_bound _ _ _ (D.serreCoeff Coefficients.q pi i j)
      (by simp [SuperCartanDatum.serreCoeff])
      (integrableChevalley_serre D hD Λ false hij) n x hn

/-- Every vector of the original action-generated quotient is locally nilpotent
under each original lowering Chevalley operator. No dominance, independent roots,
positive direction, field, finite dimension or nondegeneracy is assumed. -/
theorem integrableChevalley_false_locally_nilpotent
    (x : IntegrableQuotient D hD Λ) (i : I) :
    ∃ n : ℕ, (integrableChevalley D hD Λ false i ^ n) x = 0 := by
  induction x using integrable_induction D hD Λ with
  | word w =>
    induction w with
    | nil =>
      refine ⟨(D.h i Λ).toNat + 1, ?_⟩
      simpa only [monomial_nil, map_one] using integrableChevalley_false_vacuum D hD Λ i
    | cons j w ih =>
      have h := integrableChevalley_false_preserves_nilpotence D hD Λ i j _ ih
      simpa only [integrableChevalley_mk, chevalley_false_apply, monomial_cons, map_mul] using h
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨max n m, ?_⟩
    rw [map_add, pow_apply_zero_of_le _ hn (Nat.le_max_left n m),
      pow_apply_zero_of_le _ hm (Nat.le_max_right n m), add_zero]
  | smul c x hx =>
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, by rw [map_smul, hn, smul_zero]⟩

end OddMath.CoveringQuantum.UDot.GenericVerma
