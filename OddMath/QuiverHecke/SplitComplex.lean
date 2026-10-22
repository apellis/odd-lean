/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.Frontier.Categorification

/-!
# Split complexes of principal modules

The algebraic step from the local identities of a categorical Serre complex to its splitting,
as used for Brundan–Ellis, arXiv:1701.04133v2, Proposition 11.2 (Hill–Wang, arXiv:1202.2769v2,
Theorem 5.9). In a ring `R`, let `e₀, …, e_M` be elements with maps `f a ∈ e_{a+1} R e_a` and
`g a ∈ e_a R e_{a+1}` between neighbours (on principal left modules `R e`, right multiplication
by `f a` maps `R e_{a+1}` to `R e_a`, and `g a` maps back). If consecutive `f`'s and consecutive
`g`'s compose to zero and

`e_a = c⁺_a g_a f_a + c⁻_a f_{a-1} g_{a-1}`

for scalars `c⁺`, `c⁻` (the second term absent for `a = 0`, and `f_M = g_M = 0`), then the sum
of the modules `R e_a` with `a` even is isomorphic to the sum of those with `a` odd
(`evenOddEquiv`). No scalar needs to be invertible: the identities force
`c⁺_{a-1} f_{a-1} g_{a-1} = c⁻_a f_{a-1} g_{a-1}` (`smul_fg_eq`), so the map with entries
`g_a` and `c⁺_{a-1} f_{a-1}` is its own inverse.

`matrixEquiv` is the general statement: square matrices of elements between two families of
principal left modules that are inverse to each other give an isomorphism of the sums.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.QuiverHecke.SplitComplex
open OddMath.Frontier.Categorification

variable {R : Type*} [Ring R]

/-! ## Matrices of right multiplications -/

section Matrix

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  {e : A → R} {e' : B → R} {φ : A → B → R} {ψ : B → A → R}

/-- Mutually inverse matrices `φ`, `ψ` between the families `R e_a` and `R e'_b`. -/
structure IsInverse (e : A → R) (e' : B → R) (φ : A → B → R) (ψ : B → A → R) : Prop where
  φ_mul : ∀ a b, φ a b * e' b = φ a b
  ψ_mul : ∀ b a, ψ b a * e a = ψ b a
  φψ : ∀ a a', ∑ b, φ a b * ψ b a' = if a = a' then e a else 0
  ψφ : ∀ b b', ∑ a, ψ b a * φ a b' = if b = b' then e' b else 0

/-- `⊕_a R e_a ≃ ⊕_b R e'_b`, `(x_a) ↦ (∑_a x_a φ_{ab})_b`. -/
def matrixEquiv (h : IsInverse e e' φ ψ) :
    (∀ a, leftIdeal (e a)) ≃ₗ[R] (∀ b, leftIdeal (e' b)) where
  toFun x b := ⟨∑ a, (x a : R) * φ a b, by
    rw [mem_leftIdeal, Finset.sum_mul]
    simp_rw [mul_assoc, h.φ_mul]⟩
  map_add' x y := funext fun b => Subtype.ext <| by
    simp only [Pi.add_apply, Submodule.coe_add, add_mul, Finset.sum_add_distrib]
  map_smul' r x := funext fun b => Subtype.ext <| by
    simp only [Pi.smul_apply, SetLike.val_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
      mul_assoc]
  invFun y a := ⟨∑ b, (y b : R) * ψ b a, by
    rw [mem_leftIdeal, Finset.sum_mul]
    simp_rw [mul_assoc, h.ψ_mul]⟩
  left_inv x := funext fun a' => Subtype.ext <| by
    change ∑ b, (∑ a, (x a : R) * φ a b) * ψ b a' = x a'
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, h.φψ, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    exact (x a').2
  right_inv y := funext fun b' => Subtype.ext <| by
    change ∑ a, (∑ b, (y b : R) * ψ b a) * φ a b' = y b'
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, h.ψφ, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    exact (y b').2

theorem matrixEquiv_apply (h : IsInverse e e' φ ψ) (x : ∀ a, leftIdeal (e a)) (b : B) :
    (matrixEquiv h x b : R) = ∑ a, (x a : R) * φ a b := rfl

theorem matrixEquiv_symm_apply (h : IsInverse e e' φ ψ) (y : ∀ b, leftIdeal (e' b)) (a : A) :
    ((matrixEquiv h).symm y a : R) = ∑ b, (y b : R) * ψ b a := rfl

end Matrix

/-! ## Split complexes -/

section Complex

variable {k : Type*} [CommRing k] [Algebra k R]

/-- The data of a split complex `R e₀ ⇄ R e₁ ⇄ ⋯ ⇄ R e_M`. -/
structure IsSplit (M : ℕ) (e : ℕ → R) (f g : ℕ → R) (cp cm : ℕ → k) : Prop where
  f_mul : ∀ a, f a * e a = f a
  mul_f : ∀ a, e (a + 1) * f a = f a
  g_mul : ∀ a, g a * e (a + 1) = g a
  mul_g : ∀ a, e a * g a = g a
  ff : ∀ a, f (a + 1) * f a = 0
  gg : ∀ a, g a * g (a + 1) = 0
  f_top : ∀ a, M ≤ a → f a = 0
  g_top : ∀ a, M ≤ a → g a = 0
  split : ∀ a, a ≤ M →
    e a = cp a • (g a * f a) + if 0 < a then cm a • (f (a - 1) * g (a - 1)) else 0

namespace IsSplit

variable {M : ℕ} {e f g : ℕ → R} {cp cm : ℕ → k} (h : IsSplit M e f g cp cm)
include h

theorem split_zero : e 0 = cp 0 • (g 0 * f 0) := by
  simpa using h.split 0 (Nat.zero_le _)

theorem split_succ {a : ℕ} (ha : a + 1 ≤ M) :
    e (a + 1) = cp (a + 1) • (g (a + 1) * f (a + 1)) + cm (a + 1) • (f a * g a) := by
  simpa using h.split (a + 1) ha

/-- `f_a g_a` is fixed by `c⁺_a` and by `c⁻_{a+1}` times itself. -/
theorem fg_eq_cp {a : ℕ} (ha : a + 1 ≤ M) :
    f a * g a = cp a • (f a * g a * (f a * g a)) := by
  have key : f a * e a * g a = cp a • (f a * g a * (f a * g a)) := by
    rcases a with _ | a
    · rw [h.split_zero, mul_smul_comm, smul_mul_assoc]
      simp only [mul_assoc]
    · rw [h.split_succ (by omega), mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
        mul_smul_comm, smul_mul_assoc]
      have h0 : f (a + 1) * (f a * g a) * g (a + 1) = 0 := by
        rw [← mul_assoc, h.ff, zero_mul, zero_mul]
      rw [h0, smul_zero, add_zero]
      simp only [mul_assoc]
  rw [← key, h.f_mul]

theorem fg_eq_cm {a : ℕ} (ha : a + 1 ≤ M) :
    f a * g a = cm (a + 1) • (f a * g a * (f a * g a)) := by
  have key : f a * g a * e (a + 1) = cm (a + 1) • (f a * g a * (f a * g a)) := by
    rw [h.split_succ ha, mul_add, mul_smul_comm, mul_smul_comm]
    have h0 : f a * g a * (g (a + 1) * f (a + 1)) = 0 := by
      rw [mul_assoc, ← mul_assoc (g a), h.gg, zero_mul, mul_zero]
    rw [h0, smul_zero, zero_add]
  rw [← key, mul_assoc, h.g_mul]

/-- The two scalars agree on `f_a g_a`. -/
theorem smul_fg_eq {a : ℕ} (ha : a + 1 ≤ M) :
    cp a • (f a * g a) = cm (a + 1) • (f a * g a) := by
  conv_lhs => rw [h.fg_eq_cm ha]
  conv_rhs => rw [h.fg_eq_cp ha]
  rw [smul_smul, smul_smul, mul_comm]

/-- The splitting identity with the scalars `c⁺` only. -/
theorem split' (a : ℕ) (ha : a ≤ M) :
    e a = cp a • (g a * f a) + if 0 < a then cp (a - 1) • (f (a - 1) * g (a - 1)) else 0 := by
  rw [h.split a ha]
  split_ifs with h0
  · obtain ⟨a, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [h.smul_fg_eq ha]
  · rfl

end IsSplit

/-- The entries of the map `d + h` between neighbouring terms: `g_a` from `a` to `a + 1` and
`c⁺_{a-1} f_{a-1}` from `a` to `a - 1`. -/
def ent (g f : ℕ → R) (cp : ℕ → k) (a b : ℕ) : R :=
  (if b = a + 1 then g a else 0) + if b + 1 = a then cp b • f b else 0

/-- The terms `0 ≤ a ≤ M` of parity `p` (`true`: even). -/
def terms (M : ℕ) (p : Bool) : Finset ℕ :=
  (Finset.range (M + 1)).filter fun a => decide (Even a) = p

theorem mem_terms {M a : ℕ} {p : Bool} : a ∈ terms M p ↔ a ≤ M ∧ decide (Even a) = p := by
  simp [terms]

namespace IsSplit

variable {M : ℕ} {e f g : ℕ → R} {cp cm : ℕ → k} (h : IsSplit M e f g cp cm)
include h

theorem ent_mul (a b : ℕ) : ent g f cp a b * e b = ent g f cp a b := by
  unfold ent
  split_ifs <;> (try (exfalso; omega)) <;> subst_vars <;>
    simp only [smul_mul_assoc, zero_mul, add_zero, zero_add, h.g_mul, h.f_mul]

theorem ent_mul_ent (a b a' : ℕ) :
    ent g f cp a b * ent g f cp b a' =
      if a' = a then
        (if b = a + 1 then cp a • (g a * f a) else 0) +
          if b + 1 = a then cp b • (f b * g b) else 0
      else 0 := by
  unfold ent
  split_ifs <;> (try (exfalso; omega)) <;> subst_vars <;>
    simp only [smul_mul_assoc, mul_smul_comm, zero_mul, mul_zero, add_zero, zero_add, h.gg,
      h.ff, smul_zero]

theorem sum_ent {p q : Bool} (hq : q = !p) {a a' : ℕ} (ha : a ∈ terms M p)
    (ha' : a' ∈ terms M p) :
    ∑ b ∈ terms M q, ent g f cp a b * ent g f cp b a' = if a = a' then e a else 0 := by
  subst hq
  rw [mem_terms] at ha ha'
  simp_rw [h.ent_mul_ent]
  by_cases haa : a = a'
  · subst haa
    simp only [ite_true, Finset.sum_add_distrib]
    rw [h.split' a ha.1]
    congr 1
    · rw [Finset.sum_ite_eq']
      split_ifs with hm
      · rfl
      · rw [h.g_top a (by
          by_contra hM
          apply hm
          rw [mem_terms]
          refine ⟨by omega, ?_⟩
          rw [← ha.2]
          by_cases he : Even a <;> simp [Nat.even_add_one, he]), zero_mul, smul_zero]
    · rcases a with _ | a
      · simp
      · simp only [Nat.add_right_cancel_iff, Finset.sum_ite_eq', Nat.add_sub_cancel,
          Nat.zero_lt_succ, ite_true]
        split_ifs with hm
        · rfl
        · exfalso
          apply hm
          rw [mem_terms]
          refine ⟨by omega, ?_⟩
          rw [← ha.2]
          by_cases he : Even a <;> simp [Nat.even_add_one, he]
  · simp [haa, Ne.symm haa]

/-- The matrices of `d + h` from the even to the odd terms and back are inverse. -/
theorem isInverse :
    IsInverse (A := terms M true) (B := terms M false) (fun a => e a) (fun b => e b)
      (fun a b => ent g f cp a b) (fun b a => ent g f cp b a) where
  φ_mul a b := h.ent_mul a b
  ψ_mul b a := h.ent_mul b a
  φψ a a' := by
    rw [Finset.sum_coe_sort (terms M false) (fun b => ent g f cp a b * ent g f cp b a')]
    rw [h.sum_ent (p := true) (q := false) rfl a.2 a'.2]
    by_cases haa : a = a'
    · subst haa; simp
    · rw [ite_eq_right (fun e => absurd (Subtype.ext e) haa), ite_eq_right (absurd · haa)]
  ψφ b b' := by
    rw [Finset.sum_coe_sort (terms M true) (fun a => ent g f cp b a * ent g f cp a b')]
    rw [h.sum_ent (p := false) (q := true) rfl b.2 b'.2]
    by_cases hbb : b = b'
    · subst hbb; simp
    · rw [ite_eq_right (fun e => absurd (Subtype.ext e) hbb), ite_eq_right (absurd · hbb)]

/-- **The splitting**: `⊕_{a even} R e_a ≅ ⊕_{a odd} R e_a`. -/
def evenOddEquiv :
    (∀ a : terms M true, leftIdeal (e a)) ≃ₗ[R] (∀ b : terms M false, leftIdeal (e b)) :=
  matrixEquiv h.isInverse

end IsSplit

end Complex

end OddMath.QuiverHecke.SplitComplex
