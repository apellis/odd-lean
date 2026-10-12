/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.NativeCyclic.LengthLowering

/-!
# Local nilpotence of the native highest-weight raising operators

Formal free-word length bounds the actual raising action on the original
quotient. This is only the raising half of integrability.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.NativeLeading
open PreF Coefficients MixedGram
variable {I X : Type*} [AddCommGroup X]

/-- The strict length-zero free filtration is zero. -/
@[simp] theorem freeBelow_zero : freeBelow (I := I) 0 = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨w, hw, rfl⟩
    exact (Nat.not_lt_zero _ hw).elim
  · exact bot_le

/-- Monotonicity concerns formal words, not their images in the root lattice. -/
theorem freeBelow_mono {m n : ℕ} (h : m ≤ n) :
    freeBelow (I := I) m ≤ freeBelow n := by
  apply Submodule.span_le.mpr
  rintro x ⟨w, hw, rfl⟩
  exact monomial_mem_freeBelow w n (hw.trans_le h)

variable [DecidableEq I] (D : RootDatum I X)

/-- One application lowers the entire free length filtration. -/
theorem lowerFree_freeBelow (i : I) (a : ℤ) (n : ℕ)
    {x : PreF Coefficients.Ring I} (hx : x ∈ freeBelow (n + 1)) :
    lowerFree D.toSuperCartanDatum Coefficients.q pi i a x ∈ freeBelow n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact freeBelow_mono (Nat.le_of_lt_succ hw) (lowerFree_mem_freeBelow D i a w)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

/-- The exponent is the strict formal word-length bound, including zero. -/
theorem lowerFree_pow_eq_zero (i : I) (a : ℤ) (n : ℕ)
    {x : PreF Coefficients.Ring I} (hx : x ∈ freeBelow n) :
    (lowerFree D.toSuperCartanDatum Coefficients.q pi i a ^ n) x = 0 := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact ih (lowerFree_freeBelow D i a n hx)

omit [DecidableEq I] in
/-- Every free polynomial has a finite formal length bound. -/
theorem exists_mem_freeBelow (x : PreF Coefficients.Ring I) :
    ∃ n : ℕ, x ∈ freeBelow n := by
  induction x using induction_monomial with
  | word w => exact ⟨w.length + 1, monomial_mem_freeBelow w _ (Nat.lt_succ_self _)⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    exact ⟨max m n, Submodule.add_mem _
      (freeBelow_mono (Nat.le_max_left _ _) hm)
      (freeBelow_mono (Nat.le_max_right _ _) hn)⟩
  | smul c x hx =>
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, Submodule.smul_mem _ c hn⟩

variable [DecidableEq X] [Finite I]
variable (hD : D.toSuperCartanDatum.BarConsistent) (Λ : X)

/-- All powers intertwine the original free and quotient actions. -/
theorem integrableChevalley_pow_project (i : I) (n : ℕ)
    (x : PreF Coefficients.Ring I) :
    (integrableChevalley D hD Λ true i ^ n) (project D hD Λ x) =
      project D hD Λ ((lowerFree D.toSuperCartanDatum Coefficients.q pi i (D.h i Λ) ^ n) x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ← project_lower, ih,
      pow_succ, Module.End.mul_apply]

/-- Quantitative annihilation of any representative with bounded formal length. -/
theorem integrableChevalley_pow_project_eq_zero (i : I) (n : ℕ)
    {x : PreF Coefficients.Ring I} (hx : x ∈ freeBelow n) :
    (integrableChevalley D hD Λ true i ^ n) (project D hD Λ x) = 0 := by
  rw [integrableChevalley_pow_project, lowerFree_pow_eq_zero D i (D.h i Λ) n hx]
  simp [project]

/-- A projected word is killed by every exponent strictly above its length. -/
theorem integrableChevalley_pow_word_eq_zero (i : I) (w : List I) (n : ℕ)
    (hw : w.length < n) :
    (integrableChevalley D hD Λ true i ^ n)
      (project D hD Λ (monomial Coefficients.Ring w)) = 0 :=
  integrableChevalley_pow_project_eq_zero D hD Λ i n (monomial_mem_freeBelow w n hw)

/-- The same quantitative bound holds on the entire projected-word span. -/
theorem integrableChevalley_pow_span_eq_zero (i : I) (n : ℕ)
    {x : IntegrableQuotient D hD Λ}
    (hx : x ∈ Submodule.span Coefficients.Ring
      {y | ∃ w : List I, w.length < n ∧
        y = project D hD Λ (monomial Coefficients.Ring w)}) :
    (integrableChevalley D hD Λ true i ^ n) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact integrableChevalley_pow_word_eq_zero D hD Λ i w n hw
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, add_zero]
  | smul c x hx ih => simp only [map_smul, ih, smul_zero]

/-- Every vector of the actual highest-weight quotient is locally nilpotent
under each raising operator. No dominance or root-separation hypothesis is used. -/
theorem integrableChevalley_true_locally_nilpotent
    (x : IntegrableQuotient D hD Λ) (i : I) :
    ∃ n : ℕ, (integrableChevalley D hD Λ true i ^ n) x = 0 := by
  obtain ⟨x⟩ := x
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  obtain ⟨n, hn⟩ := exists_mem_freeBelow x
  exact ⟨n, integrableChevalley_pow_project_eq_zero D hD Λ i n hn⟩

end OddMath.CoveringQuantum.UDot.GenericVerma.NativeLeading
