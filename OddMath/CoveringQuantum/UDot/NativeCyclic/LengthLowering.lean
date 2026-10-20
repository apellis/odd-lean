/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.NativeCyclic.NativeLeading

/-! Formal word-length lowering, before and after the actual quotient maps. -/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.NativeLeading
open PreF Coefficients TensorProduct MixedGram
variable {I X : Type*} [AddCommGroup X] [DecidableEq I]
variable (D : RootDatum I X)

/-- Strict formal free-word length, with no weight-image comparison. -/
def freeBelow (n : ℕ) : Submodule Coefficients.Ring (PreF Coefficients.Ring I) :=
  Submodule.span Coefficients.Ring {x | ∃ w : List I,
    w.length < n ∧ x = monomial Coefficients.Ring w}

omit [DecidableEq I] in
theorem monomial_mem_freeBelow (w : List I) (n : ℕ) (h : w.length < n) :
    monomial Coefficients.Ring w ∈ freeBelow n :=
  Submodule.subset_span ⟨w, h, rfl⟩

omit [DecidableEq I] in
theorem create_mem_freeBelow (i : I) (n : ℕ) {x : PreF Coefficients.Ring I}
    (hx : x ∈ freeBelow n) : θ Coefficients.Ring i * x ∈ freeBelow (n + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [← monomial_cons]
    exact monomial_mem_freeBelow (i :: w) (n + 1) (by simpa using Nat.succ_lt_succ hw)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [mul_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [mul_smul_comm] using Submodule.smul_mem _ c ih

/-- The published native lowering operator strictly lowers formal word length. -/
theorem lowerFree_mem_freeBelow (i : I) (n : ℤ) (w : List I) :
    lowerFree D.toSuperCartanDatum Coefficients.q pi i n (monomial Coefficients.Ring w) ∈
      freeBelow w.length := by
  induction w with
  | nil => simp [monomial]
  | cons j w ih =>
    rw [monomial_cons, lowerFree_mixed_monomial D Coefficients.q pi pi_sq i j n
      (vermaDenominator_isUnit D.toSuperCartanDatum i)]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (create_mem_freeBelow j w.length ih)
    · split_ifs
      · exact Submodule.smul_mem _ _
          (monomial_mem_freeBelow w (w.length + 1) (Nat.lt_succ_self _))
      · exact Submodule.zero_mem _

variable [DecidableEq X]
variable (Λ Μ : X)

/-- Strict formal bidegree span in the original quotient tensor, not a basis. -/
def lowerBidegree (m n : ℕ) : Submodule Coefficients.Ring
    (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ) :=
  Submodule.span Coefficients.Ring {z | ∃ a b : List I,
    a.length < m ∧ b.length < n ∧
      z = project D Λ (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
        project D Μ (monomial Coefficients.Ring b)}

/-- Membership uses original quotient words and their formal lengths only. -/
theorem wordTensor_mem (a b : List I) (m n : ℕ) (ha : a.length < m) (hb : b.length < n) :
    project D Λ (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
      project D Μ (monomial Coefficients.Ring b) ∈ lowerBidegree D Λ Μ m n :=
  Submodule.subset_span ⟨a, b, ha, hb, rfl⟩

theorem lowerBidegree_mono {m n m' n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    lowerBidegree D Λ Μ m n ≤ lowerBidegree D Λ Μ m' n' := by
  apply Submodule.span_le.mpr
  rintro z ⟨a, b, ha, hb, rfl⟩
  exact wordTensor_mem D Λ Μ a b m' n' (ha.trans_le hm) (hb.trans_le hn)

/-- A lowered second factor has strictly smaller formal length. -/
theorem tmul_lower_mem (a b : List I) (i : I) (m n : ℕ)
    (ha : a.length < m) (hb : b.length ≤ n) :
    project D Λ (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
      project D Μ
        (lowerFree D.toSuperCartanDatum Coefficients.q pi i (D.h i Μ)
          (monomial Coefficients.Ring b)) ∈ lowerBidegree D Λ Μ m n := by
  have hh (x : PreF Coefficients.Ring I) (hx : x ∈ freeBelow b.length) :
      project D Λ (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
        project D Μ x ∈ lowerBidegree D Λ Μ m n := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact wordTensor_mem D Λ Μ a w m n ha (hw.trans_le hb)
    | zero => simp [project]
    | add x y hx hy ihx ihy =>
      simpa only [project, map_add, tmul_add] using Submodule.add_mem _ ihx ihy
    | smul c x hx ih =>
      simpa only [project, map_smul, tmul_smul] using Submodule.smul_mem _ c ih
  exact hh _ (lowerFree_mem_freeBelow D i (D.h i Μ) b)

@[simp] theorem lowerBidegree_zero_left (n : ℕ) : lowerBidegree D Λ Μ 0 n = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨a, b, ha, hb, hz⟩
    exact (Nat.not_lt_zero _ ha).elim
  · exact bot_le

@[simp] theorem lowerBidegree_zero_right (m : ℕ) : lowerBidegree D Λ Μ m 0 = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨a, b, ha, hb, hz⟩
    exact (Nat.not_lt_zero _ hb).elim
  · exact bot_le

end OddMath.CoveringQuantum.UDot.GenericVerma.NativeLeading
