/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Content indices for global cyclotomic super actions

Ports the weight and block-successor part of
`Categorification/KLR/CyclotomicAction/Global.lean` and the absent-colour
index lemmas of `Categorification/KLR/CyclotomicAction/GlobalLoc.lean`.
The weight convention is `sum β - Λ`, with induction raising the weight.
These indices include the empty content. They are not yet weight-space
supercategories: the existing cyclotomic supermodule categories are indexed
by positive height, rather than by content. No global functor or local
inversion is asserted in this module.
-/

namespace OddMath.QuiverHecke.CyclotomicAction

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) (Λ : X)

/-- The weight of the cyclotomic block with content `β`. -/
def blockWeight (β : Multiset I) : X := (β.map D.α).sum - Λ

@[simp] theorem blockWeight_zero : blockWeight D Λ 0 = -Λ := by
  simp [blockWeight]

@[simp] theorem blockWeight_singleton (i : I) :
    blockWeight D Λ {i} = D.α i - Λ := by
  simp [blockWeight]

theorem blockWeight_cons (i : I) (β : Multiset I) :
    blockWeight D Λ ({i} + β) = blockWeight D Λ β + D.α i := by
  simp only [blockWeight, Multiset.map_add, Multiset.map_singleton,
    Multiset.sum_add, Multiset.sum_singleton]
  abel

/-- Contents contributing to a weight space; distinct contents are retained. -/
abbrev WeightBlocks (x : X) := {β : Multiset I // blockWeight D Λ β = x}

/-- Appending one strand on the set of content blocks. -/
def blockSucc (i : I) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) : WeightBlocks D Λ y :=
  ⟨{i} + β.1, by rw [blockWeight_cons, β.2, h]⟩

@[simp] theorem blockSucc_val (i : I) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) : (blockSucc D Λ i h β).1 = {i} + β.1 := rfl

theorem blockSucc_eq (i : I) {x y : X} {h : x + D.α i = y}
    {β : WeightBlocks D Λ x} {δ : WeightBlocks D Λ y}
    (hβ : blockSucc D Λ i h β = δ) : {i} + β.1 = δ.1 :=
  congrArg Subtype.val hβ

theorem blockSucc_injective (i : I) {x y : X} (h : x + D.α i = y) :
    Function.Injective (blockSucc D Λ i h) := by
  intro β γ e
  exact Subtype.ext (add_left_cancel (congrArg Subtype.val e))

instance (i : I) {x y : X} (h : x + D.α i = y) (δ : WeightBlocks D Λ y) :
    Subsingleton {β : WeightBlocks D Λ x // blockSucc D Λ i h β = δ} :=
  ⟨fun β γ => Subtype.ext (blockSucc_injective D Λ i h (β.2.trans γ.2.symm))⟩

/-- The two orders of adding colours have the same content. -/
theorem blockSucc_comm (i j : I) {x y z t : X}
    (h₁ : x + D.α j = y) (h₂ : y + D.α i = t)
    (h₃ : x + D.α i = z) (h₄ : z + D.α j = t) (β : WeightBlocks D Λ x) :
    blockSucc D Λ i h₂ (blockSucc D Λ j h₁ β) =
      blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β) :=
  Subtype.ext (add_left_comm _ _ _)

/-- Precisely the blocks containing `i` have a predecessor of colour `i`. -/
theorem exists_blockSucc_iff (i : I) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ y) :
    (∃ γ, blockSucc D Λ i h γ = β) ↔ i ∈ β.1 := by
  classical
  constructor
  · rintro ⟨γ, rfl⟩
    simp
  · intro hi
    have hw : blockWeight D Λ (β.1.erase i) + D.α i = x + D.α i := by
      rw [← blockWeight_cons, Multiset.singleton_add, Multiset.cons_erase hi, β.2, h]
    exact ⟨⟨β.1.erase i, add_right_cancel hw⟩,
      Subtype.ext (by simp only [blockSucc_val, Multiset.singleton_add,
        Multiset.cons_erase hi])⟩

/-- Empty fibres are the absent-colour boundary, not a missing height block. -/
theorem isEmpty_of_not_mem (i : I) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ y) (hi : i ∉ β.1) :
    IsEmpty {γ : WeightBlocks D Λ x // blockSucc D Λ i h γ = β} :=
  ⟨fun γ => hi ((exists_blockSucc_iff D Λ i h β).mp ⟨γ.1, γ.2⟩)⟩

/-- KKO's height is the negative of the pairing with the block weight. -/
theorem blockLoc_weight (i : I) {x : X} (β : WeightBlocks D Λ x) :
    -D.h i (Λ - (β.1.map D.α).sum) = D.h i x := by
  change -(D.cd.coroot i) _ = (D.cd.coroot i) _
  rw [← map_neg, neg_sub]
  exact congrArg (D.cd.coroot i) β.2

/-- Dominance and the off-diagonal Cartan inequalities determine the boundary sign. -/
theorem pair_nonpos_of_not_mem (hΛ : ∀ i, 0 ≤ D.h i Λ)
    (i : I) {x : X} (β : WeightBlocks D Λ x) (hi : i ∉ β.1) : D.h i x ≤ 0 := by
  have hs : ∀ s : Multiset I, i ∉ s → D.h i (s.map D.α).sum ≤ 0 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp [SKM.Datum.h]
    | cons j s ih =>
      intro hn
      have hij : i ≠ j := fun e => hn (e ▸ Multiset.mem_cons_self j s)
      have hj : D.h i (D.α j) ≤ 0 := D.isGCM.offDiag_nonpos i j hij
      have ht := ih (fun e => hn (Multiset.mem_cons_of_mem e))
      simpa only [Multiset.map_cons, Multiset.sum_cons, map_add] using add_nonpos hj ht
  rw [← β.2]
  change (D.cd.coroot i) ((β.1.map D.α).sum - Λ) ≤ 0
  rw [map_sub]
  exact sub_nonpos.mpr ((hs β.1 hi).trans (hΛ i))

/-- Height alone cannot label blocks if two simple roots differ. -/
theorem blockWeight_not_card (i j : I) (hij : D.α i ≠ D.α j) :
    ¬ ∃ w : ℕ → X, ∀ β : Multiset I, blockWeight D Λ β = w β.card := by
  rintro ⟨w, hw⟩
  have e := (hw {i}).trans (hw {j}).symm
  simp only [blockWeight_singleton] at e
  exact hij (sub_left_injective e)

end OddMath.QuiverHecke.CyclotomicAction
