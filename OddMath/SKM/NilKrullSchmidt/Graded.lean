/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.NilKrullSchmidt.Laurent

/-!
# Nilpotent filtrations of graded supercategories

A filtration of the Hom-spaces of a graded supercategory, compatible with composition,
vanishing in each fixed degree in high filtration index, and with finite-dimensional
quotient in each degree by its first step, induces a `NilFiltration` of the shifted
degree-zero category `ShiftBase k C`. This is the form in which the Hom-spaces of
Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §11, supply the
Krull–Schmidt input of Theorem 11.7 for arbitrary colour sets: positive-degree bubbles
generate the filtration, and degreewise finite dimensionality is not needed.
-/

noncomputable section

namespace OddMath.KrullSchmidtNil

open CategoryTheory StringDiagrams StringDiagrams.GSKar GradedSupercategory Supercategory

variable (k : Type*) {C : Type*} [Field k] [Category C] [Preadditive C] [Linear k C]
  [Supercategory k C] [GradedSupercategory k C]

/-- A multiplicative filtration of the Hom-spaces of a graded supercategory that vanishes
degreewise in high index and has finite-dimensional degreewise quotients by its first step. -/
structure GradedNilFiltration where
  /-- The filtration steps. -/
  G : ℕ → ∀ X Y : C, Submodule k (X ⟶ Y)
  zero : ∀ X Y, G 0 X Y = ⊤
  antitone : ∀ d X Y, G (d + 1) X Y ≤ G d X Y
  comp_mem : ∀ {a b : ℕ} {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z},
    f ∈ G a X Y → g ∈ G b Y Z → f ≫ g ∈ G (a + b) X Z
  vanish : ∀ (X Y : C) (n : ℤ), ∃ D, ∀ f ∈ G D X Y, f ∈ degree (R := k) X Y n → f = 0
  finiteDimensional : ∀ (X Y : C) (n : ℤ), FiniteDimensional k
    (degree (R := k) X Y n ⧸ (G 1 X Y).comap (degree (R := k) X Y n).subtype)

namespace GradedNilFiltration

variable {k}

/-- The underlying morphism of the original category of a shifted degree-zero morphism. -/
def under (X Y : ShiftBase k C) :
    (X ⟶ Y) →ₗ[k] (X.obj.obj.obj.obj ⟶ Y.obj.obj.obj.obj) where
  toFun f := f.val.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem under_injective (X Y : ShiftBase k C) : Function.Injective (under X Y) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem under_mem (X Y : ShiftBase k C) (f : X ⟶ Y) :
    under X Y f ∈ degree (R := k) X.obj.obj.obj.obj Y.obj.obj.obj.obj
      (0 + (X.obj.obj.obj.shift - Y.obj.obj.obj.shift)) :=
  f.val.property

/-- The induced nilpotent filtration of the shifted degree-zero category. -/
def toShiftBase (Φ : GradedNilFiltration k (C := C)) : NilFiltration k (ShiftBase k C) where
  F d X Y := (Φ.G d X.obj.obj.obj.obj Y.obj.obj.obj.obj).comap (under X Y)
  zero X Y := by rw [Φ.zero, Submodule.comap_top]
  antitone d X Y := Submodule.comap_mono (Φ.antitone d _ _)
  comp_mem hf hg := Φ.comp_mem hf hg
  vanish X Y := by
    obtain ⟨D, hD⟩ := Φ.vanish X.obj.obj.obj.obj Y.obj.obj.obj.obj
      (0 + (X.obj.obj.obj.shift - Y.obj.obj.obj.shift))
    refine ⟨D, eq_bot_iff.mpr fun f hf => ?_⟩
    apply under_injective X Y
    rw [map_zero]
    exact hD _ hf (under_mem X Y f)
  finiteDimensional X Y := by
    set A := degree (R := k) X.obj.obj.obj.obj Y.obj.obj.obj.obj
      (0 + (X.obj.obj.obj.shift - Y.obj.obj.obj.shift))
    let u : (X ⟶ Y) →ₗ[k] A := (under X Y).codRestrict A (under_mem X Y)
    let := Φ.finiteDimensional X.obj.obj.obj.obj Y.obj.obj.obj.obj
      (0 + (X.obj.obj.obj.shift - Y.obj.obj.obj.shift))
    let q := Submodule.mapQ ((Φ.G 1 X.obj.obj.obj.obj Y.obj.obj.obj.obj).comap (under X Y))
      ((Φ.G 1 X.obj.obj.obj.obj Y.obj.obj.obj.obj).comap A.subtype) u (fun f hf => hf)
    apply FiniteDimensional.of_injective q
    intro a b h
    induction a using Submodule.Quotient.induction_on with
    | H a =>
      induction b using Submodule.Quotient.induction_on with
      | H b =>
        rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at h
        rw [Submodule.Quotient.eq]
        change under X Y (a - b) ∈ Φ.G 1 X.obj.obj.obj.obj Y.obj.obj.obj.obj
        exact h

end GradedNilFiltration

namespace GSKar

/-- The Laurentian envelope theorem of BE2 §11 from a graded nilpotent filtration and a lower
bound on degrees: `K₀` of the graded additive Karoubi envelope is free over `ℤ[q, q⁻¹]`. -/
theorem k0_free_laurentInt_of_graded (Φ : GradedNilFiltration k (C := C))
    (h : HomBoundedBelow (k := k) (C := C)) :
    letI := K₀.moduleLaurentInt k (GSKar k C)
    Module.Free (LaurentPolynomial ℤ) (K₀ (GSKar k C)) :=
  KrullSchmidtNil.GSKar.k0_free_laurentInt Φ.toShiftBase h

end GSKar

end OddMath.KrullSchmidtNil
