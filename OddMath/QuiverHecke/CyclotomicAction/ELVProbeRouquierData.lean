/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDistinctCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDotUnit

/-! # OLD probe Rouquier generator data

Brundan–Ellis Definition 1.5 and (1.8)–(1.9): assemble the chosen probe
weight spaces, induction and signed dots with the negative equal crossing
and positive distinct crossing. Restriction and its prescribed adjunction,
the equal square and braid, and the natural dot unit are retained. Local
inversion records and multicolour coherence remain separate obligations.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u
private theorem braid_of_equal_crosses
    {k : Type u} [CommRing k] {A B C E : PiSCat.{u,u,u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ E)
    (t₁ u₁ : End (F ≫ G)) (t₂ u₂ : End (G ≫ H))
    (e₁ : u₁ = t₁) (e₂ : u₂ = t₂)
    (hb : let p := (associator F G H).inv ≫ t₁ ▷ H ≫ (associator F G H).hom
      let s := F ◁ t₂
      s ≫ p ≫ s = p ≫ s ≫ p) :
    let p := (associator F G H).inv ≫ u₁ ▷ H ≫ (associator F G H).hom
    let s := F ◁ u₂
    s ≫ p ≫ s = p ≫ s ≫ p := by
  cases e₁
  cases e₂
  exact hb

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (Λ : X)

/-- The selected crossing, using the negative equal and positive distinct maps. -/
def probeOldActionCross (i j : I) {a b c d : X}
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = c) (h₄ : c + D.α j = d) :
    probeOldE D Sc m j Λ h₁ ≫ probeOldE D Sc m i Λ h₂ ⟶
      probeOldE D Sc m i Λ h₃ ≫ probeOldE D Sc m j Λ h₄ :=
  if hij : i = j then by
    subst j
    have hbc : b = c := h₁.symm.trans h₃
    cases hbc
    exact probeOldActionEqualCross D Sc m i Λ h₁ h₂
  else probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄

theorem probeOldActionCross_equal (i : I) {a b c : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) :
    probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂ =
      probeOldActionEqualCross D Sc m i Λ h₁ h₂ := by
  rw [probeOldActionCross, dite_eq_left rfl]

theorem probeOldActionCross_distinct (i j : I) (hij : i ≠ j) {a b c d : X}
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = c) (h₄ : c + D.α j = d) :
    probeOldActionCross D Sc m Λ i j h₁ h₂ h₃ h₄ =
      probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ := by
  simp only [probeOldActionCross, dite_eq_right hij]

theorem probeOldActionCross_mem (i j : I) {a b c d : X}
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = c) (h₄ : c + D.α j = d) :
    probeOldActionCross D Sc m Λ i j h₁ h₂ h₃ h₄ ∈ parity (R := k) _ _
      (D.parity i * D.parity j) := by
  by_cases hij : i = j
  · subst j
    have hbc : b = c := h₁.symm.trans h₃
    cases hbc
    rw [probeOldActionCross_equal, SKM.zmod2_mul_self]
    exact probeOldActionEqualCross_mem D Sc m i Λ h₁ h₂
  · rw [probeOldActionCross_distinct D Sc m Λ i j hij]
    exact probeOldActionDistinctCross_mem D Sc m i j Λ h₁ h₂ h₃ h₄

/-- The selected generators, without assuming any local inverse record. -/
def probeOldRouquierData :
    SKM.RouquierData (k := k) (B := PiSCat.{u,u,u + 1} k) D where
  obj x := probeOldWeightSpace D Sc m Λ x
  E i _ _ h := probeOldE D Sc m i Λ h
  dot i _ _ h := probeOldActionDot D Sc m i Λ h
  dot_mem i _ _ h := probeOldActionDot_mem D Sc m i Λ h
  cross i j _ _ _ _ h₁ h₂ h₃ h₄ := probeOldActionCross D Sc m Λ i j h₁ h₂ h₃ h₄
  cross_mem i j _ _ _ _ h₁ h₂ h₃ h₄ := probeOldActionCross_mem D Sc m Λ i j h₁ h₂ h₃ h₄

/-- The right adjunction uses the selected restriction and unchanged unit and counit. -/
def probeOldRouquierDataAdjunction (i : I) {x y : X} (h : x + D.α i = y) :
    SKM.SuperAdjunction (k := k) ((probeOldRouquierData D Sc m Λ).E i h)
      (probeOldF D Sc m i Λ h) :=
  probeOldActionAdjunction D Sc m i Λ h

theorem probeOldRouquierData_dot_isUnit [Fact Sc.PureNilpotent] [Fintype I] (i : I) {x y : X} (h : x + D.α i = y) :
    IsUnit (End.of ((probeOldRouquierData D Sc m Λ).dot i h)) :=
  probeOldActionDot_isUnit D Sc m i Λ h

theorem probeOldRouquierData_square (i : I) {a b c : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) :
    (probeOldRouquierData D Sc m Λ).cross i i h₁ h₂ h₁ h₂ ≫
      (probeOldRouquierData D Sc m Λ).cross i i h₁ h₂ h₁ h₂ = 0 := by
  change probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂ ≫
    probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂ = 0
  rw [probeOldActionCross_equal]
  exact probeOldActionEqualCross_square D Sc m i Λ h₁ h₂

theorem probeOldRouquierData_braid (i : I) {a b c d : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) (h₃ : c + D.α i = d) :
    let E₁ := (probeOldRouquierData D Sc m Λ).E i h₁
    let E₂ := (probeOldRouquierData D Sc m Λ).E i h₂
    let E₃ := (probeOldRouquierData D Sc m Λ).E i h₃
    let t₁ := (associator E₁ E₂ E₃).inv ≫
      (probeOldRouquierData D Sc m Λ).cross i i h₁ h₂ h₁ h₂ ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom
    let t₂ := E₁ ◁ (probeOldRouquierData D Sc m Λ).cross i i h₂ h₃ h₂ h₃
    t₂ ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ t₁ := by
  exact braid_of_equal_crosses
    (probeOldE D Sc m i Λ h₁) (probeOldE D Sc m i Λ h₂) (probeOldE D Sc m i Λ h₃)
    (probeOldActionEqualCross D Sc m i Λ h₁ h₂)
    (probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂)
    (probeOldActionEqualCross D Sc m i Λ h₂ h₃)
    (probeOldActionCross D Sc m Λ i i h₂ h₃ h₂ h₃)
    (probeOldActionCross_equal D Sc m Λ i h₁ h₂)
    (probeOldActionCross_equal D Sc m Λ i h₂ h₃)
    (probeOldActionEqualCross_braid D Sc m i Λ h₁ h₂ h₃)

end OddMath.QuiverHecke
