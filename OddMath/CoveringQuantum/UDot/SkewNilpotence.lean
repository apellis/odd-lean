/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorNegative

/-! Scalar-commuting sums and tensor maps, without division or dimension assumptions. -/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.TensorNilpotence
open TensorProduct

variable {k V W : Type*} [CommRing k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- A killing power continues to kill at every larger exponent. -/
theorem pow_kills_of_le (A : Module.End k V) {x : V} {m n : ℕ}
    (h : (A ^ m) x = 0) (hmn : m ≤ n) : (A ^ n) x = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_comm m r, pow_add, Module.End.mul_apply, h, map_zero]

/-- Moving a power past the other operator retains the full scalar. -/
theorem skew_pow_apply (A B : Module.End k V) (c : k)
    (h : A * B = c • (B * A)) (n : ℕ) (x : V) :
    (A ^ n) (B x) = c ^ n • B ((A ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx (y : V) : A (B y) = c • B (A y) :=
      congrArg (fun f : Module.End k V ↦ f y) h
    simp only [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, mul_comm]

/-- Rectangular induction on the two killing powers. Both scalar commutations
are explicit; no ordinary commuting binomial formula is used. -/
theorem skew_sum_bound (A B : Module.End k V) (c d : k)
    (hab : A * B = c • (B * A)) (hba : B * A = d • (A * B))
    (m n : ℕ) (x : V) (ha : (A ^ m) x = 0) (hb : (B ^ n) x = 0) :
    ((A + B) ^ (m + n)) x = 0 := by
  induction m generalizing n x with
  | zero =>
    have hx : x = 0 := by simpa using ha
    simp [hx]
  | succ m ihm =>
    induction n generalizing x with
    | zero =>
      have hx : x = 0 := by simpa using hb
      simp [hx]
    | succ n ihn =>
      have ha' : (A ^ m) (A x) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using ha
      have hb' : (B ^ (n + 1)) (A x) = 0 := by
        rw [skew_pow_apply B A d hba, hb, map_zero, smul_zero]
      have ha'' : (A ^ (m + 1)) (B x) = 0 := by
        rw [skew_pow_apply A B c hab, ha, map_zero, smul_zero]
      have hb'' : (B ^ n) (B x) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hb
      have hleft := ihm (n + 1) (A x) ha' hb'
      have hright := ihn (B x) ha'' hb''
      rw [show m + 1 + (n + 1) = (m + (n + 1)) + 1 by omega,
        pow_succ, Module.End.mul_apply, LinearMap.add_apply, map_add, hleft]
      simpa only [Nat.add_assoc, Nat.add_comm 1 n, zero_add] using hright

/-- Local nilpotence of a scalar-commuting sum on arbitrary vectors. -/
theorem skew_sum_locally_nilpotent (A B : Module.End k V) (c d : k)
    (hab : A * B = c • (B * A)) (hba : B * A = d • (A * B))
    (ha : ∀ x, ∃ m : ℕ, (A ^ m) x = 0)
    (hb : ∀ x, ∃ n : ℕ, (B ^ n) x = 0) (x : V) :
    ∃ n : ℕ, ((A + B) ^ n) x = 0 := by
  obtain ⟨m, hm⟩ := ha x
  obtain ⟨n, hn⟩ := hb x
  exact ⟨m + n, skew_sum_bound A B c d hab hba m n x hm hn⟩

/-- Extend killing powers from elementary tensors to finite tensor sums. -/
theorem tensor_locally_nilpotent_of_tmul
    (A : Module.End k (V ⊗[k] W))
    (h : ∀ x y, ∃ n : ℕ, (A ^ n) (x ⊗ₜ[k] y) = 0)
    (z : V ⊗[k] W) : ∃ n : ℕ, (A ^ n) z = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    rw [map_add, pow_kills_of_le A hm (by omega), pow_kills_of_le A hn (by omega),
      add_zero]

/-- Only the left tensor factor needs to be locally nilpotent. -/
theorem map_left_locally_nilpotent (A : Module.End k V) (B : Module.End k W)
    (h : ∀ x, ∃ n : ℕ, (A ^ n) x = 0) (z : V ⊗[k] W) :
    ∃ n : ℕ, (TensorProduct.map A B ^ n) z = 0 := by
  apply tensor_locally_nilpotent_of_tmul
  intro x y
  obtain ⟨n, hn⟩ := h x
  exact ⟨n, by simp only [TensorProduct.map_pow, TensorProduct.map_tmul, hn,
    TensorProduct.zero_tmul]⟩

/-- Only the right tensor factor needs to be locally nilpotent. -/
theorem map_right_locally_nilpotent (A : Module.End k V) (B : Module.End k W)
    (h : ∀ y, ∃ n : ℕ, (B ^ n) y = 0) (z : V ⊗[k] W) :
    ∃ n : ℕ, (TensorProduct.map A B ^ n) z = 0 := by
  apply tensor_locally_nilpotent_of_tmul
  intro x y
  obtain ⟨n, hn⟩ := h y
  exact ⟨n, by simp only [TensorProduct.map_pow, TensorProduct.map_tmul, hn,
    TensorProduct.tmul_zero]⟩

end OddMath.CoveringQuantum.UDot.GenericVerma.TensorNilpotence
