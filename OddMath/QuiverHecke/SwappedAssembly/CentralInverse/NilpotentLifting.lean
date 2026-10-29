/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Inverses modulo a nilpotent ideal

Two steps of §§4–5 of `docs/Nondegeneracy/SwappedHomInversion.md` that only use nilpotence of
an error term, in an arbitrary preadditive category.

* (12), nilpotent lifting: if `g` inverts `f` up to errors `𝟙 - f ≫ g` and `𝟙 - g ≫ f` that are
  nilpotent endomorphisms, then `f` is invertible (`isIso_of_isNilpotent_sub`). Applied in
  `Mat_ C`, nilpotence of the error is nilpotence for the matrix ideal, not entrywise.
* (10): the block map `[1, l; m, 1]` on `A ⊞ B` is invertible when `m ≫ l` is nilpotent
  (`isIso_unipotentBlock`), by the factorization through `diag(1, 1 - m ≫ l)`.

In `SwappedHomInversion.md` the nilpotence comes from the reservoir closures `b_(s,r)` of
positive degree (its (8)–(9)), which uses the gradings (G6)–(G8); here it is a hypothesis.
-/

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

open CategoryTheory Limits

variable {C : Type*} [Category C] [Preadditive C]

/-- An endomorphism `1 - e` with `e` nilpotent is invertible. -/
theorem isIso_one_sub_of_isNilpotent {X : C} (e : X ⟶ X) (he : IsNilpotent (show End X from e)) :
    IsIso (𝟙 X - e) :=
  (isUnit_iff_isIso (𝟙 X - e : End X)).1 he.isUnit_one_sub

/-- **Nilpotent lifting** (`SwappedHomInversion.md` (12)). If `g` is inverse to `f` up to the
nilpotent errors `𝟙 - f ≫ g` and `𝟙 - g ≫ f`, then `f` is invertible. -/
theorem isIso_of_isNilpotent_sub {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : IsNilpotent (show End X from 𝟙 X - f ≫ g))
    (hY : IsNilpotent (show End Y from 𝟙 Y - g ≫ f)) : IsIso f := by
  have h₁ : IsIso (f ≫ g) := by
    have := isIso_one_sub_of_isNilpotent _ hX
    rwa [sub_sub_cancel] at this
  have h₂ : IsIso (g ≫ f) := by
    have := isIso_one_sub_of_isNilpotent _ hY
    rwa [sub_sub_cancel] at this
  have hl : f ≫ (g ≫ inv (f ≫ g)) = 𝟙 X := by rw [← Category.assoc, IsIso.hom_inv_id]
  have hr : (inv (g ≫ f) ≫ g) ≫ f = 𝟙 Y := by rw [Category.assoc, IsIso.inv_hom_id]
  have he : g ≫ inv (f ≫ g) = inv (g ≫ f) ≫ g := by
    calc g ≫ inv (f ≫ g) = ((inv (g ≫ f) ≫ g) ≫ f) ≫ (g ≫ inv (f ≫ g)) := by
          rw [hr, Category.id_comp]
      _ = inv (g ≫ f) ≫ g := by
          rw [Category.assoc (inv (g ≫ f) ≫ g), hl, Category.comp_id]
  exact ⟨⟨g ≫ inv (f ≫ g), hl, by rw [he, hr]⟩⟩

section Biproduct

variable [HasBinaryBiproducts C] {A B : C}

/-- The block map `[1, l; m, 1] : A ⊞ B ⟶ A ⊞ B`: `inl ↦ inl + l ≫ inr`, `inr ↦ m ≫ inl + inr`.
This is `A0 = 1 + KI` of `SwappedHomInversion.md` (10), with `l = C_RP j_P`, `m = D_PR j_R`. -/
noncomputable def unipotentBlock (l : A ⟶ B) (m : B ⟶ A) : A ⊞ B ⟶ A ⊞ B :=
  biprod.desc (biprod.inl + l ≫ biprod.inr) (m ≫ biprod.inl + biprod.inr)

/-- The lower shear `inl ↦ inl`, `inr ↦ m ≫ inl + inr`. -/
noncomputable def lowerShear (m : B ⟶ A) : A ⊞ B ⟶ A ⊞ B :=
  biprod.desc biprod.inl (m ≫ biprod.inl + biprod.inr)

/-- The upper shear `inl ↦ inl + l ≫ inr`, `inr ↦ inr`. -/
noncomputable def upperShear (l : A ⟶ B) : A ⊞ B ⟶ A ⊞ B :=
  biprod.desc (biprod.inl + l ≫ biprod.inr) biprod.inr

theorem lowerShear_comp (m m' : B ⟶ A) : lowerShear m ≫ lowerShear m' = lowerShear (m + m') := by
  apply biprod.hom_ext' <;>
    simp [lowerShear, Preadditive.add_comp, add_assoc]

theorem upperShear_comp (l l' : A ⟶ B) : upperShear l ≫ upperShear l' = upperShear (l + l') := by
  apply biprod.hom_ext'
  · simp only [upperShear, biprod.inl_desc_assoc, Preadditive.add_comp, biprod.inl_desc,
      Category.assoc, biprod.inr_desc]
    abel
  · simp [upperShear]

theorem lowerShear_zero : lowerShear (0 : B ⟶ A) = 𝟙 (A ⊞ B) := by
  apply biprod.hom_ext' <;> simp [lowerShear]

theorem upperShear_zero : upperShear (0 : A ⟶ B) = 𝟙 (A ⊞ B) := by
  apply biprod.hom_ext' <;> simp [upperShear]

instance isIso_lowerShear (m : B ⟶ A) : IsIso (lowerShear m) :=
  ⟨⟨lowerShear (-m), by rw [lowerShear_comp, add_neg_cancel, lowerShear_zero],
    by rw [lowerShear_comp, neg_add_cancel, lowerShear_zero]⟩⟩

instance isIso_upperShear (l : A ⟶ B) : IsIso (upperShear l) :=
  ⟨⟨upperShear (-l), by rw [upperShear_comp, add_neg_cancel, upperShear_zero],
    by rw [upperShear_comp, neg_add_cancel, upperShear_zero]⟩⟩

/-- `[1, l; m, 1] = [1, 0; m, 1] ≫ diag(1, 1 - m ≫ l) ≫ [1, l; 0, 1]`. -/
theorem unipotentBlock_eq (l : A ⟶ B) (m : B ⟶ A) :
    unipotentBlock l m = lowerShear m ≫ biprod.map (𝟙 A) (𝟙 B - m ≫ l) ≫ upperShear l := by
  apply biprod.hom_ext'
  · simp [unipotentBlock, lowerShear, upperShear]
  · simp [unipotentBlock, lowerShear, upperShear, Preadditive.add_comp, Preadditive.comp_add,
      Preadditive.sub_comp]

/-- `SwappedHomInversion.md` (10): `[1, l; m, 1]` is invertible when `m ≫ l` is nilpotent. -/
theorem isIso_unipotentBlock (l : A ⟶ B) (m : B ⟶ A) (h : IsNilpotent (show End B from m ≫ l)) :
    IsIso (unipotentBlock l m) := by
  have := isIso_one_sub_of_isNilpotent _ h
  have : IsIso (biprod.map (𝟙 A) (𝟙 B - m ≫ l)) :=
    (biprod.mapIso (Iso.refl A) (asIso (𝟙 B - m ≫ l))).isIso_hom
  rw [unipotentBlock_eq]
  infer_instance

end Biproduct

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
