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

end OddMath.QuiverHecke.CyclotomicAction
