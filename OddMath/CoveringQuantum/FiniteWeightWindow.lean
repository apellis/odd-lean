/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.Datum
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite weight windows

The algebraic finite-lattice step for the finite-support extension of Brundan–Ellis,
*Super Kac–Moody 2-categories*, Theorem 12.1. The window is a submodule of the original
weight group, not a replacement by finitely supported coordinates or a central quotient.

Torsion-freeness and a family of integral coroot-separating weights are explicit
intermediate inputs. Constructing these weights from the complex source realization,
and comparing the categorical presentations, remain separate. Root independence is
inherited only when supplied. No categorical nondegeneracy is assumed or proved here.
-/

namespace OddMath.CoveringQuantum.FiniteWeightWindow

variable {J X : Type*} [AddCommGroup X]

/-- The integral span of the seed weights, selected roots and separating weights. -/
def lattice (W : Finset X) (α ω : J → X) : Submodule ℤ X :=
  Submodule.span ℤ ((W : Set X) ∪ Set.range α ∪ Set.range ω)

variable (W : Finset X) (α ω : J → X)

theorem weight_mem {x : X} (hx : x ∈ W) : x ∈ lattice W α ω :=
  Submodule.subset_span (Or.inl (Or.inl hx))

theorem root_mem (j : J) : α j ∈ lattice W α ω :=
  Submodule.subset_span (Or.inl (Or.inr ⟨j, rfl⟩))

theorem separating_mem (j : J) : ω j ∈ lattice W α ω :=
  Submodule.subset_span (Or.inr ⟨j, rfl⟩)

/-- The inclusion is the submodule inclusion, retaining every weight coordinate. -/
abbrev inclusion : lattice W α ω →ₗ[ℤ] X := (lattice W α ω).subtype

theorem inclusion_injective : Function.Injective (inclusion W α ω) :=
  Subtype.val_injective

/-- A selected root as an element of the window. -/
def root (j : J) : lattice W α ω := ⟨α j, root_mem W α ω j⟩

/-- A separating weight as an element of the window. -/
def separating (j : J) : lattice W α ω := ⟨ω j, separating_mem W α ω j⟩

/-- Restriction of an ambient integral linear form, without changing its values. -/
def restrict (f : Module.Dual ℤ X) : Module.Dual ℤ (lattice W α ω) :=
  f.comp (inclusion W α ω)

@[simp] theorem restrict_apply (f : Module.Dual ℤ X) (x : lattice W α ω) :
    restrict W α ω f x = f (x : X) := rfl

@[simp] theorem restrict_root (f : Module.Dual ℤ X) (j : J) :
    restrict W α ω f (root W α ω j) = f (α j) := rfl

@[simp] theorem restrict_separating (f : Module.Dual ℤ X) (j : J) :
    restrict W α ω f (separating W α ω j) = f (ω j) := rfl

variable [Finite J]

theorem fg : (lattice W α ω).FG :=
  Submodule.fg_span ((W.finite_toSet.union (Set.finite_range α)).union (Set.finite_range ω))

instance finite : Module.Finite ℤ (lattice W α ω) :=
  Module.Finite.of_fg (fg W α ω)

/-- Restricting coroots preserves independence, witnessed by evaluating at the
separating weights. This is not asserted for an arbitrary root datum. -/
theorem coroot_linearIndependent [DecidableEq J] (h : J → Module.Dual ℤ X)
    (hω : ∀ i j, h i (ω j) = if i = j then 1 else 0) :
    LinearIndependent ℤ (fun j ↦ restrict W α ω (h j)) := by
  let := Fintype.ofFinite J
  apply Fintype.linearIndependent_iff.mpr
  intro g hg j
  have he := congrArg (fun f : Module.Dual ℤ (lattice W α ω) ↦
    f (separating W α ω j)) hg
  simpa [LinearMap.sum_apply, separating, hω] using he

omit [Finite J] in
/-- Root independence is inherited through the inclusion, never assumed by `RootDatum`. -/
theorem root_linearIndependent (hα : LinearIndependent ℤ α) :
    LinearIndependent ℤ (root W α ω) :=
  LinearIndependent.of_comp (inclusion W α ω) hα

variable [Module.IsTorsionFree ℤ X]

/-- Finite generation and ambient torsion-freeness give a finite-rank free lattice. -/
theorem free : Module.Free ℤ (lattice W α ω) := inferInstance

/-- An explicit finite basis exists, including when the window has rank zero. -/
noncomputable def finiteBasis : Σ n : ℕ, Module.Basis (Fin n) ℤ (lattice W α ω) :=
  Module.basisOfFiniteTypeTorsionFree'

/-- The full dual lattice, not merely the span of the restricted coroots. -/
abbrev dual := Module.Dual ℤ (lattice W α ω)

theorem dual_finite : Module.Finite ℤ (dual W α ω) := inferInstance

theorem dual_free : Module.Free ℤ (dual W α ω) := inferInstance

/-- Evaluation identifies the window with the integral double dual. -/
noncomputable def perfect : lattice W α ω ≃ₗ[ℤ] Module.Dual ℤ (dual W α ω) :=
  Module.evalEquiv ℤ (lattice W α ω)

@[simp] theorem perfect_apply (x : lattice W α ω) (f : dual W α ω) :
    perfect W α ω x f = f x := rfl

end OddMath.CoveringQuantum.FiniteWeightWindow

namespace OddMath.CoveringQuantum.RootDatum

variable {I X : Type*} [AddCommGroup X] (D : RootDatum I X)
    (J : Finset I) (W : Finset X) (ω : J → X)

/-- A finite-colour datum on the submodule spanned inside the existing weight group.
No finiteness of the ambient colour type or nondegeneracy hypothesis is required. -/
def weightWindow : RootDatum J (FiniteWeightWindow.lattice W (fun j : J ↦ D.α j) ω) where
  a i j := D.a i j
  isGCM := {
    diag := fun i ↦ D.isGCM.diag i
    offDiag_nonpos := fun i j hij ↦ D.isGCM.offDiag_nonpos i j
      (fun h ↦ hij (Subtype.ext h))
    zero_comm := fun i j ↦ D.isGCM.zero_comm i j }
  d i := D.d i
  d_pos i := D.d_pos i
  d_mul_symm i j := D.d_mul_symm i j
  parity i := D.parity i
  even_of_odd i j := D.even_of_odd i j
  cd := {
    root := FiniteWeightWindow.root W (fun j : J ↦ D.α j) ω
    coroot := fun i ↦ FiniteWeightWindow.restrict W (fun j : J ↦ D.α j) ω (D.cd.coroot i)
    coroot_root_self := fun i ↦ D.cd.coroot_root_self i }
  coroot_root i j := D.coroot_root i j

@[simp] theorem weightWindow_h (i : J)
    (x : FiniteWeightWindow.lattice W (fun j : J ↦ D.α j) ω) :
    (D.weightWindow J W ω).h i x = D.h i (x : X) := rfl

@[simp] theorem weightWindow_root (j : J) :
    ((D.weightWindow J W ω).α j : X) = D.α j := rfl

/-- The coroots of the restricted datum are independent under the explicit
integral separating-family premise. -/
theorem weightWindow_coroot_linearIndependent [DecidableEq J]
    (hω : ∀ i j : J, D.h i (ω j) = if i = j then 1 else 0) :
    LinearIndependent ℤ (D.weightWindow J W ω).cd.coroot :=
  FiniteWeightWindow.coroot_linearIndependent W (fun j : J ↦ D.α j) ω
    (fun i ↦ D.cd.coroot i) hω

/-- Selected root independence passes to the restricted datum. -/
theorem weightWindow_root_linearIndependent
    (hα : LinearIndependent ℤ (fun j : J ↦ D.α j)) :
    LinearIndependent ℤ (D.weightWindow J W ω).α :=
  FiniteWeightWindow.root_linearIndependent W (fun j : J ↦ D.α j) ω hα

end OddMath.CoveringQuantum.RootDatum
