/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.BlockMaps
import Mathlib.Tactic.LinearCombination

/-! # Extraction of the residual inverse

§4 of `docs/Nondegeneracy/ProbeWindowInverse.md`, (16)–(19) there. Let
`M = [s, B; Cc, E] : X ⊕ Oᴸ ⟶ Y ⊕ Oᵀ` (`ProbeWindow.gMap`) be invertible.

* If the cap window `[s; V₀, …, V_{h-1}]` has an entrywise inverse `(j, A)`, the residual
  `R : O^{h ⊕ L} ⟶ Oᵀ` with entries `A n ≫ Cc r` and `E l r - B l ≫ j ≫ Cc r` ((16), in
  execution order) is invertible (`ProbeWindow.isIso_capResidual`); its inverse has entries
  `B' r ≫ V n` and `E' r l`, read from `M⁻¹ = [a', B'; C', E']` ((17)).
* If the cup window `[s, U₀, …, U_{b-1}]` has an entrywise inverse `(j, D)`, the residual
  `R : Oᴸ ⟶ O^{T ⊕ b}` with entries `E l r - B l ≫ j ≫ Cc r` and `-(B l ≫ D n)` ((18)) is
  invertible (`ProbeWindow.isIso_cupResidual`); its inverse has entries `E' r l` and
  `-(U n ≫ C' l)` ((19)).

No property of `M` other than invertibility is used: both products are checked entrywise
from the four block equations of `M ≫ M⁻¹ = 𝟙` and `M⁻¹ ≫ M = 𝟙`.
-/

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- The object `Oᶥ` of `Mat_ C`. -/
abbrev pObj (O : C) (ι : Type) [Fintype ι] [DecidableEq ι] : Mat_ C where
  ι := ι
  X _ := O

variable {L T : Type} [Fintype L] [DecidableEq L] [Fintype T] [DecidableEq T]

/-- The residual (16) of an auxiliary map at a cap window. -/
def capResidual {X Y O : C} {h : ℕ} (B : L → (O ⟶ Y)) (Cc : T → (X ⟶ O)) (E : L → T → (O ⟶ O))
    (j : Y ⟶ X) (A : Fin h → (O ⟶ X)) : pObj O (Fin h ⊕ L) ⟶ pObj O T :=
  fun i r => Sum.elim (fun n => A n ≫ Cc r) (fun l => E l r - B l ≫ j ≫ Cc r) i

/-- The residual (18) of an auxiliary map at a cup window. -/
def cupResidual {X Y O : C} {b : ℕ} (B : L → (O ⟶ Y)) (Cc : T → (X ⟶ O)) (E : L → T → (O ⟶ O))
    (j : Y ⟶ X) (D : Fin b → (Y ⟶ O)) : pObj O L ⟶ pObj O (T ⊕ Fin b) :=
  fun l i => Sum.elim (fun r => E l r - B l ≫ j ≫ Cc r) (fun n => -(B l ≫ D n)) i

omit [DecidableEq L] [DecidableEq T] in
private lemma pObj_id_apply {O : C} {ι : Type} [Fintype ι] [DecidableEq ι] (i i' : ι) :
    (𝟙 (pObj O ι) : pObj O ι ⟶ pObj O ι) i i' = if i = i' then 𝟙 O else 0 := by
  by_cases hi : i = i'
  · subst hi; simp only [↓reduceIte]; exact Mat_.id_apply_self _ _
  · simp only [hi, ↓reduceIte]; exact Mat_.id_apply_of_ne _ _ _ hi

/-- The four block equations of `gMap a B Cc E ≫ gMap a' B' C' E' = 𝟙`. -/
private lemma gMap_comp_eq_id {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {X Y O : C} {a : X ⟶ Y} {B : ι → (O ⟶ Y)} {Cc : κ → (X ⟶ O)}
    {E : ι → κ → (O ⟶ O)} {a' : Y ⟶ X} {B' : κ → (O ⟶ X)} {C' : ι → (Y ⟶ O)}
    {E' : κ → ι → (O ⟶ O)} (H : gMap a B Cc E ≫ gMap a' B' C' E' = 𝟙 _) :
    a ≫ a' + ∑ r, Cc r ≫ B' r = 𝟙 X ∧ (∀ l, B l ≫ a' + ∑ r, E l r ≫ B' r = 0) ∧
      (∀ l, a ≫ C' l + ∑ r, Cc r ≫ E' r l = 0) ∧
      (∀ l l', B l ≫ C' l' + ∑ r, E l r ≫ E' r l' = if l = l' then 𝟙 O else 0) := by
  rw [gMap_comp, gMap_id] at H
  refine ⟨?_, fun l => ?_, fun l => ?_, fun l l' => ?_⟩
  · simpa using congrArg (fun f => f none none) H
  · simpa using congrArg (fun f => f (some l) none) H
  · simpa using congrArg (fun f => f none (some l)) H
  · simpa using congrArg (fun f => f (some l) (some l')) H

/-- **Extraction at a cap window**, (16)–(17) of `ProbeWindowInverse.md`. -/
theorem isIso_capResidual {X Y O : C} {h : ℕ} (s : X ⟶ Y) (B : L → (O ⟶ Y)) (Cc : T → (X ⟶ O))
    (E : L → T → (O ⟶ O)) [IsIso (gMap s B Cc E)] {V : Fin h → (X ⟶ O)} {j : Y ⟶ X}
    {A : Fin h → (O ⟶ X)} (H : IsCapInverse s V j A) :
    IsIso (capResidual B Cc E j A) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  have hMN := IsIso.hom_inv_id (gMap s B Cc E)
  have hNM := IsIso.inv_hom_id (gMap s B Cc E)
  rw [gMap_eta (inv (gMap s B Cc E))] at hMN hNM
  generalize (inv (gMap s B Cc E)) none none = a' at hMN hNM
  generalize (fun r => (inv (gMap s B Cc E)) (some r) none) = B' at hMN hNM
  generalize (fun l => (inv (gMap s B Cc E)) none (some l)) = C' at hMN hNM
  generalize (fun r l => (inv (gMap s B Cc E)) (some r) (some l)) = E' at hMN hNM
  obtain ⟨m1, m2, m3, m4⟩ := gMap_comp_eq_id hMN
  obtain ⟨n1, n2, n3, n4⟩ := gMap_comp_eq_id hNM
  have h2' : ∀ n {Z : C} (g : Y ⟶ Z), A n ≫ s ≫ g = 0 := fun n Z g => by
    rw [reassoc_of% (h2 n), Limits.zero_comp]
  have h1' : ∀ {Z : C} (g : Y ⟶ Z), j ≫ s ≫ g = g := by
    intro Z g; simp [reassoc_of% h1]
  refine ⟨fun r i => Sum.elim (fun n => B' r ≫ V n) (fun l => E' r l) i, ?_, ?_⟩
  · ext i i'
    rw [Mat_.comp_apply, pObj_id_apply]
    rcases i with n | l <;> rcases i' with n' | l'
    · have e := congrArg (fun g => A n ≫ g ≫ V n') m1
      simp only [capResidual] at e ⊢
      block_norm at e ⊢
      rw [h2', zero_add, h4] at e
      exact e
    · have e := congrArg (fun g => A n ≫ g) (m3 l')
      simp only [capResidual] at e ⊢
      block_norm at e ⊢
      rw [h2', zero_add] at e
      exact e
    · have e1 := congrArg (fun g => g ≫ V n') (m2 l)
      have e2 := congrArg (fun g => B l ≫ j ≫ g ≫ V n') m1
      simp only [capResidual] at e1 e2 ⊢
      block_norm at e1 e2 ⊢
      rw [h1', h3, Limits.comp_zero] at e2
      linear_combination (norm := abel) e1 - e2
    · have e1 := m4 l l'
      have e2 := congrArg (fun g => B l ≫ j ≫ g) (m3 l')
      simp only [capResidual] at e1 e2 ⊢
      block_norm at e1 e2 ⊢
      rw [h1'] at e2
      linear_combination (norm := abel) e1 - e2
  · ext r r'
    rw [Mat_.comp_apply, pObj_id_apply]
    have e1 := congrArg (fun g => B' r ≫ g ≫ Cc r') h5
    have e2 := n4 r r'
    have e3 := congrArg (fun g => g ≫ j ≫ Cc r') (n2 r)
    simp only [capResidual] at e1 e2 e3 ⊢
    block_norm at e1 e2 e3 ⊢
    linear_combination (norm := abel) e1 + e2 - e3

/-- **Extraction at a cup window**, (18)–(19) of `ProbeWindowInverse.md`. -/
theorem isIso_cupResidual {X Y O : C} {b : ℕ} (s : X ⟶ Y) (B : L → (O ⟶ Y)) (Cc : T → (X ⟶ O))
    (E : L → T → (O ⟶ O)) [IsIso (gMap s B Cc E)] {U : Fin b → (O ⟶ Y)} {j : Y ⟶ X}
    {D : Fin b → (Y ⟶ O)} (H : IsCupInverse s U j D) :
    IsIso (cupResidual B Cc E j D) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  have hMN := IsIso.hom_inv_id (gMap s B Cc E)
  have hNM := IsIso.inv_hom_id (gMap s B Cc E)
  rw [gMap_eta (inv (gMap s B Cc E))] at hMN hNM
  generalize (inv (gMap s B Cc E)) none none = a' at hMN hNM
  generalize (fun r => (inv (gMap s B Cc E)) (some r) none) = B' at hMN hNM
  generalize (fun l => (inv (gMap s B Cc E)) none (some l)) = C' at hMN hNM
  generalize (fun r l => (inv (gMap s B Cc E)) (some r) (some l)) = E' at hMN hNM
  obtain ⟨m1, m2, m3, m4⟩ := gMap_comp_eq_id hMN
  obtain ⟨n1, n2, n3, n4⟩ := gMap_comp_eq_id hNM
  have h1' : ∀ {Z : C} (g : X ⟶ Z), s ≫ j ≫ g = g := by
    intro Z g; simp [reassoc_of% h1]
  have h3' : ∀ n {Z : C} (g : X ⟶ Z), U n ≫ j ≫ g = 0 := fun n Z g => by
    rw [reassoc_of% (h3 n), Limits.zero_comp]
  refine ⟨fun i l => Sum.elim (fun r => E' r l) (fun n => -(U n ≫ C' l)) i, ?_, ?_⟩
  · ext l l'
    rw [Mat_.comp_apply, pObj_id_apply]
    have e1 := m4 l l'
    have e2 := congrArg (fun g => B l ≫ j ≫ g) (m3 l')
    have e3 := congrArg (fun g => B l ≫ g ≫ C' l') h5
    simp only [cupResidual] at e1 e2 e3 ⊢
    block_norm at e1 e2 e3 ⊢
    linear_combination (norm := abel) e1 - e2 + e3
  · ext i i'
    rw [Mat_.comp_apply, pObj_id_apply]
    rcases i with r | n <;> rcases i' with r' | n'
    · have e1 := n4 r r'
      have e2 := congrArg (fun g => g ≫ j ≫ Cc r') (n2 r)
      simp only [cupResidual] at e1 e2 ⊢
      block_norm at e1 e2 ⊢
      rw [h1'] at e2
      linear_combination (norm := abel) e1 - e2
    · have e := congrArg (fun g => g ≫ D n') (n2 r)
      simp only [cupResidual] at e ⊢
      block_norm at e ⊢
      rw [h2, Limits.comp_zero, zero_add] at e
      linear_combination (norm := abel) -e
    · have e1 := congrArg (fun g => U n ≫ g) (n3 r')
      have e2 := congrArg (fun g => U n ≫ g ≫ j ≫ Cc r') n1
      simp only [cupResidual] at e1 e2 ⊢
      block_norm at e1 e2 ⊢
      rw [h1', h3'] at e2
      linear_combination (norm := abel) e2 - e1
    · have e := congrArg (fun g => U n ≫ g ≫ D n') n1
      simp only [cupResidual] at e ⊢
      block_norm at e ⊢
      rw [h2, Limits.comp_zero, Limits.comp_zero, zero_add, h4] at e
      linear_combination (norm := abel) e

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
