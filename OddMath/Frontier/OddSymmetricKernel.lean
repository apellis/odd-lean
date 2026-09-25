import OddMath.Frontier.AllRankDivided
import OddMath.Frontier.FiniteCompleteElementary

/-! The joint odd-divided-difference kernel and the literal finite e/h sums.
Ellis 1111.3932v1 §2.1, (2.3) and the following finite-sum displays. -/
namespace OddMath.Frontier.OddSymmetricKernel
open OddMath.SkewPolynomial
open AllRankDivided PlacticEvaluation FiniteCompleteElementary
open FiniteCompleteElementary.FiniteWords
open scoped BigOperators
noncomputable section

/-- One actual twisted-derivation kernel is a subring, not an invariant ring. -/
def singleKernel {n : ℕ} (i : Fin (n+1)) : Subring (SkewPolynomial (n+2)) where
  carrier := {f | divided i f = 0}
  zero_mem' := map_zero _
  one_mem' := divided_one i
  add_mem' := by intro f g hf hg; simp only [Set.mem_setOf_eq] at *; rw [map_add, hf, hg, add_zero]
  neg_mem' := by intro f hf; simp only [Set.mem_setOf_eq] at *; rw [map_neg, hf, neg_zero]
  mul_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at *
    rw [divided_mul, hf, hg]
    simp

/-- The joint kernel in Ellis §2.1 (2.3). -/
def kernelSubring (n : ℕ) : Subring (SkewPolynomial (n+2)) where
  carrier := {f | ∀ i : Fin (n+1), divided i f = 0}
  zero_mem' := fun _ => map_zero _
  one_mem' := divided_one
  add_mem' := by intro f g hf hg i; rw [map_add, hf i, hg i, add_zero]
  neg_mem' := by intro f hf i; rw [map_neg, hf i, neg_zero]
  mul_mem' := by
    intro f g hf hg i
    rw [divided_mul, hf i, hg i]
    simp

@[simp] theorem mem_kernelSubring {n : ℕ} (f : SkewPolynomial (n+2)) :
    f ∈ kernelSubring n ↔ ∀ i : Fin (n+1), divided i f = 0 := Iff.rfl

section SubringWords
variable {R : Type*} [Ring R] (S : Subring R)

/-- Every strict word in elements of a subring stays in it. -/
theorem strictSum_mem {m : ℕ} (x : Fin m → R) (hx : ∀ j, x j ∈ S) (k : ℕ) :
    strictSum x k ∈ S := by
  classical
  apply S.sum_mem
  intro f _
  apply S.list_prod_mem
  intro a ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  exact hx (f.val j)

/-- Split off the first two letters, without commuting any factors. -/
theorem strictSum_pair_front {m : ℕ} (x : Fin (m+2) → R) (k : ℕ) :
    strictSum x (k+2) = (x 0 * x 1) * strictSum (fun j => x j.succ.succ) k +
      (x 0 + x 1) * strictSum (fun j => x j.succ.succ) (k+1) +
      strictSum (fun j => x j.succ.succ) (k+2) := by
  rw [strictSum_succ, strictSum_succ, strictSum_succ (fun j => x j.succ)]
  simp only [Fin.succ_zero_eq_one]
  noncomm_ring

/-- A paired head need only have its sum and ordered product in the subring. -/
theorem strictSum_mem_front {m : ℕ} (x : Fin (m+2) → R)
    (ht : ∀ j : Fin m, x j.succ.succ ∈ S)
    (ha : x 0 + x 1 ∈ S) (hm : x 0 * x 1 ∈ S) (k : ℕ) :
    strictSum x k ∈ S := by
  cases k with
  | zero => simpa using S.one_mem
  | succ k =>
    cases k with
    | zero =>
      have he : strictSum x 1 = (x 0 + x 1) + strictSum (fun j => x j.succ.succ) 1 := by
        rw [strictSum_succ, strictSum_succ]
        simp only [strictSum_zero, _root_.mul_one, Fin.succ_zero_eq_one, add_assoc]
      rw [he]
      exact S.add_mem ha (strictSum_mem S _ ht 1)
    | succ k =>
      rw [strictSum_pair_front]
      exact S.add_mem (S.add_mem (S.mul_mem hm (strictSum_mem S _ ht k))
        (S.mul_mem ha (strictSum_mem S _ ht (k+1)))) (strictSum_mem S _ ht (k+2))

/-- Isolate any consecutive pair by peeling off earlier spectator letters. -/
theorem strictSum_mem_pair {m : ℕ} (x : Fin (m+2) → R) (i : Fin (m+1))
    (ht : ∀ j, j ≠ i.castSucc → j ≠ i.succ → x j ∈ S)
    (ha : x i.castSucc + x i.succ ∈ S) (hm : x i.castSucc * x i.succ ∈ S)
    (k : ℕ) : strictSum x k ∈ S := by
  induction m generalizing k with
  | zero =>
    have hi : i = 0 := by apply Fin.ext; have := i.isLt; simp only [Fin.val_zero]; omega
    subst i
    exact strictSum_mem_front S x (fun j => Fin.elim0 j) ha hm k
  | succ m ih =>
    cases i using Fin.cases with
    | zero =>
      apply strictSum_mem_front S x _ ha hm k
      intro j
      apply ht
      · exact Fin.succ_ne_zero _
      · intro h
        have h' := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_zero] at h'
        omega
    | succ i =>
      have ht' : ∀ j : Fin (m+2), j ≠ i.castSucc → j ≠ i.succ → x j.succ ∈ S := by
        intro j hl hr
        apply ht
        · intro h; exact hl (Fin.succ_injective _ h)
        · intro h; exact hr (Fin.succ_injective _ h)
      have h0 : x 0 ∈ S := ht 0
        (by intro h; have := congrArg Fin.val h; simp at this)
        (Fin.succ_ne_zero _).symm
      cases k with
      | zero => simpa using S.one_mem
      | succ k =>
        rw [strictSum_succ]
        exact S.add_mem (S.mul_mem h0 (ih (fun j => x j.succ) i ht' ha hm k))
          (ih (fun j => x j.succ) i ht' ha hm (k+1))
end SubringWords

/-- Spectators have zero derivative; their twist signs are already in the parent law. -/
theorem divided_tilde_spectator {n : ℕ} (i : Fin (n+1)) (j : Fin (n+2))
    (hl : j ≠ i.castSucc) (hr : j ≠ i.succ) : divided i (tildeGenerator j) = 0 := by
  rw [tildeGenerator, map_smul, divided_generator]
  simp [hl, hr]

theorem divided_tilde_pair_add {n : ℕ} (i : Fin (n+1)) :
    divided i (tildeGenerator i.castSucc + tildeGenerator i.succ) = 0 := by
  simp only [map_add, tildeGenerator, map_smul, divided_generator]
  simp [pow_succ]

theorem divided_tilde_pair_mul {n : ℕ} (i : Fin (n+1)) :
    divided i (tildeGenerator i.castSucc * tildeGenerator i.succ) = 0 := by
  have hp : divided i (generator i.castSucc * generator i.succ) = 0 := by
    rw [divided_left_mul, divided_generator]
    simp
  simp only [tildeGenerator, smul_mul_assoc, mul_smul_comm, map_smul, hp, smul_zero]

/-- Every literal elementary sum lies in every adjacent divided-difference kernel. -/
theorem divided_elementary (n k : ℕ) (i : Fin (n+1)) :
    divided i (elementaryPoly (n+2) k) = 0 := by
  rw [elementaryPoly_eq_strictSum]
  exact strictSum_mem_pair (singleKernel i) tildeGenerator i
    (fun j hl hr => divided_tilde_spectator i j hl hr)
    (divided_tilde_pair_add i) (divided_tilde_pair_mul i) k

theorem elementary_mem (n k : ℕ) : elementaryPoly (n+2) k ∈ kernelSubring n :=
  divided_elementary n k

/-- Ordered convolution isolates h_k; every other h has strictly smaller degree. -/
theorem complete_mem (n k : ℕ) : completePoly (n+2) k ∈ kernelSubring n := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa using (kernelSubring n).one_mem
    | succ k =>
      have he := elementary_complete_inverse (n+2) (k+1) (by omega)
      rw [Finset.sum_range_succ'] at he
      norm_num only [Nat.sub_zero, elementaryPoly_zero, one_smul, one_mul,
        Nat.add_sub_add_right] at he
      simp only [show Nat.choose 1 2 = 0 from rfl, pow_zero, one_smul, _root_.one_mul] at he
      have hs : (∑ j ∈ Finset.range (k+1), (-1 : ℤ) ^ ((j+2).choose 2) •
          (elementaryPoly (n+2) (j+1) * completePoly (n+2) (k-j))) ∈ kernelSubring n := by
        apply (kernelSubring n).sum_mem
        intro j _
        apply (kernelSubring n).zsmul_mem
        exact (kernelSubring n).mul_mem (elementary_mem n (j+1)) (ih (k-j) (by omega))
      have hh : completePoly (n+2) (k+1) =
          -(∑ j ∈ Finset.range (k+1), (-1 : ℤ) ^ ((j+2).choose 2) •
            (elementaryPoly (n+2) (j+1) * completePoly (n+2) (k-j))) :=
        eq_neg_of_add_eq_zero_right he
      rw [hh]
      exact (kernelSubring n).neg_mem hs

/-- The independently enumerated weak sums are annihilated in every degree. -/
theorem divided_complete (n k : ℕ) (i : Fin (n+1)) :
    divided i (completePoly (n+2) k) = 0 := complete_mem n k i

/-- Genuine free lift into the joint kernel on positive h generators. -/
def completeKernelEvaluation (n : ℕ) : CompleteElementary.A →+* kernelSubring n :=
  (FreeAlgebra.lift ℤ (fun j => (⟨completePoly (n+2) (j+1), complete_mem n (j+1)⟩ :
    kernelSubring n))).toRingHom

@[simp] theorem completeKernelEvaluation_generator (n j : ℕ) :
    completeKernelEvaluation n (FreeAlgebra.ι ℤ j) =
      ⟨completePoly (n+2) (j+1), complete_mem n (j+1)⟩ :=
  FreeAlgebra.lift_ι_apply _ j

/-- The subtype composition is exactly the parent's existing evaluation map. -/
theorem subtype_comp_completeKernelEvaluation (n : ℕ) :
    (kernelSubring n).subtype.comp (completeKernelEvaluation n) = completeEvaluation (n+2) := by
  apply RingHom.ext
  intro a
  induction a using FreeAlgebra.induction with
  | grade0 r => simp
  | grade1 j => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, ha, hb]

/-- An arbitrary noncommutative free expression lands in the actual joint kernel. -/
theorem completeEvaluation_mem (n : ℕ) (a : CompleteElementary.A) :
    completeEvaluation (n+2) a ∈ kernelSubring n := by
  rw [← subtype_comp_completeKernelEvaluation]
  exact (completeKernelEvaluation n a).property

end
end OddMath.Frontier.OddSymmetricKernel
