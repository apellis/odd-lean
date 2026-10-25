/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleELVCoefficients
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! # Multicolour algebraic ELV coefficient specialization

This is an explicit quotient of abstract SYM, not a claim that an SKM action
has been constructed. Ordinary elementary truncation is used on even colours.
-/
noncomputable section
open scoped Classical
namespace OddMath.SKM.SYM
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k]

def elvElementaryRank (cutoff : I → ℕ) (i : I) : ℕ :=
  if D.parity i = 0 then cutoff i else cutoff i / 2

def ELVCoefficientRelation (cutoff : I → ℕ) (x : SYM D k) : Prop :=
  (∃ i r, elvElementaryRank D cutoff i ≤ r ∧ x = e D k i r) ∨
  (∃ i : {i : I // D.parity i = 1}, cutoff i.1 % 2 = 0 ∧
    x = delta D k i * elvChi D k i (cutoff i.1 / 2))

def elvCoefficientIdeal (cutoff : I → ℕ) : TwoSidedIdeal (SYM D k) :=
  TwoSidedIdeal.span {x | ELVCoefficientRelation D k cutoff x}

theorem mem_coefficientIdeal_iff (N : ℕ) (x : SYM D k) :
    x ∈ coefficientIdeal D k N ↔ x ∈ CoefficientAtLeast D k N :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _

theorem elvCoefficientRelation_mem_high {cutoff : I → ℕ} {N : ℕ}
    (hN : ∀ i, N ≤ cutoff i) {x : SYM D k}
    (hx : ELVCoefficientRelation D k cutoff x) :
    x ∈ CoefficientAtLeast D k (N + 1) := by
  rcases hx with ⟨i, r, hr, rfl⟩ | ⟨i, he, rfl⟩
  · apply coefficientAtLeast_antitone D k _ (elementary_mem_coefficientAtLeast D k i r)
    have := hN i
    unfold elvElementaryRank at hr
    unfold elementaryWeight
    split_ifs at * <;> omega
  · have hn : 1 + 2 * (cutoff i.1 / 2) = cutoff i.1 + 1 := by omega
    have hm := coefficientAtLeast_mul D k (delta_mem_coefficientAtLeast D k i)
      (elvChi_mem_coefficientAtLeast D k i (cutoff i.1 / 2))
    rw [hn] at hm
    exact coefficientAtLeast_antitone D k (Nat.add_le_add_right (hN i.1) 1) hm

theorem elvCoefficientIdeal_le_weight {cutoff : I → ℕ} {N : ℕ}
    (hN : ∀ i, N ≤ cutoff i) :
    elvCoefficientIdeal D k cutoff ≤ coefficientIdeal D k (N + 1) := by
  apply TwoSidedIdeal.span_le.mpr
  intro x hx
  exact (mem_coefficientIdeal_iff D k _ _).mpr (elvCoefficientRelation_mem_high D k hN hx)

/-- The actual multicolour coefficient quotient retains the entire bounded
coefficient span, including independent products of odd parameters. -/
theorem elvCoefficient_quotient_injective {cutoff : I → ℕ} {d : ℕ}
    (hd : ∀ i, d ≤ cutoff i) :
    Function.Injective (fun x : CoefficientAtMost D k d =>
      (elvCoefficientIdeal D k cutoff).ringCon.mk' (x : SYM D k)) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hmem : (x : SYM D k) - y ∈ elvCoefficientIdeal D k cutoff :=
    (TwoSidedIdeal.rel_iff _ _ _).mp (Quotient.exact hxy)
  have hw : (x : SYM D k) - y ∈ CoefficientAtLeast D k (d + 1) := by
    exact (mem_coefficientIdeal_iff D k _ _).mp (elvCoefficientIdeal_le_weight D k hd hmem)
  exact Submodule.disjoint_def.mp
    (disjoint_coefficientAtMost_coefficientAtLeast D k (Nat.lt_succ_self d)) _
    (Submodule.sub_mem _ x.property y.property)
    hw

end OddMath.SKM.SYM
