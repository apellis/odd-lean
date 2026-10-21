/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.FiniteWeightWindow
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Basic.Complex.Basic

/-!
# Integral weights of a complex realization

For the realization in Brundan–Ellis, *Super Kac–Moody 2-categories*, §1,
`weightLattice` is the actual submodule of the full complex dual integral on every
ambient coroot. The entire independent coroot family has a linear left inverse:
Mathlib constructs this by extending a basis of its image to a Hamel basis.
Its coordinates therefore give integral separating weights on all colours, not
merely on a selected finite subset. No finite-dimensionality is imposed.

The finite windows retain arbitrary seed weights and central directions. Their
freeness and both independence premises are discharged from the source realization.
This is the lattice step toward the finite-support extension of conditional
Theorem 12.1, not algebra/form transport or categorical nondegeneracy.
-/

namespace OddMath.CoveringQuantum.SourceWeightLattice

variable {I H : Type*} [AddCommGroup H] [Module ℂ H]

/-- All complex-linear forms integral on every ambient coroot. -/
def weightLattice (h : I → H) : Submodule ℤ (Module.Dual ℂ H) where
  carrier := {f | ∀ i, ∃ n : ℤ, f (h i) = (n : ℂ)}
  zero_mem' := fun _ ↦ ⟨0, by simp⟩
  add_mem' := by
    intro f g hf hg i
    obtain ⟨m, hm⟩ := hf i
    obtain ⟨n, hn⟩ := hg i
    exact ⟨m + n, by simp [hm, hn]⟩
  smul_mem' := by
    intro n f hf i
    obtain ⟨m, hm⟩ := hf i
    exact ⟨n * m, by simp [hm, zsmul_eq_mul]⟩

variable (h : I → H)

/-- The inclusion into the full complex dual does not discard central directions. -/
abbrev inclusion : weightLattice h →ₗ[ℤ] Module.Dual ℂ H :=
  (weightLattice h).subtype

theorem inclusion_injective : Function.Injective (inclusion h) := Subtype.val_injective

instance torsionFree : Module.IsTorsionFree ℤ (weightLattice h) := inferInstance

/-- The unique integer evaluation on an ambient coroot. -/
noncomputable def coroot (i : I) : Module.Dual ℤ (weightLattice h) where
  toFun f := (f.property i).choose
  map_add' f g := by
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_add, ← (f.property i).choose_spec, ← (g.property i).choose_spec,
      ← ((f + g).property i).choose_spec]
    simp
  map_smul' n f := by
    apply Int.cast_injective (α := ℂ)
    simp only [RingHom.id_apply, smul_eq_mul, Int.cast_mul]
    rw [← (f.property i).choose_spec, ← ((n • f).property i).choose_spec]
    simp [zsmul_eq_mul]

@[simp] theorem cast_coroot (i : I) (f : weightLattice h) :
    (coroot h i f : ℂ) = (f : Module.Dual ℂ H) (h i) :=
  (f.property i).choose_spec.symm

/-- A simultaneous left inverse for the entire ambient coroot family. The pinned
basis-extension theorem works for arbitrary index sets and vector spaces. -/
noncomputable def coordinates : H →ₗ[ℂ] (I →₀ ℂ) :=
  (Finsupp.linearCombination ℂ h).leftInverse

theorem coordinates_coroot (hh : LinearIndependent ℂ h) (i : I) :
    coordinates h (h i) = Finsupp.single i 1 := by
  have he := LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr hh) (Finsupp.single i 1)
  simpa [coordinates] using he

/-- Delta-coordinate forms, integral on all ambient coroots. -/
noncomputable def omega (hh : LinearIndependent ℂ h) (j : I) : weightLattice h := by
  classical
  refine ⟨(Finsupp.lapply j).comp (coordinates h), fun i ↦ ?_⟩
  exact ⟨if i = j then 1 else 0, by simp [coordinates_coroot h hh, Finsupp.single_apply]⟩

@[simp] theorem omega_apply (hh : LinearIndependent ℂ h) [DecidableEq I] (i j : I) :
    (omega h hh j : Module.Dual ℂ H) (h i) = if i = j then 1 else 0 := by
  simp [omega, coordinates_coroot h hh, Finsupp.single_apply]

@[simp] theorem coroot_omega (hh : LinearIndependent ℂ h) [DecidableEq I] (i j : I) :
    coroot h i (omega h hh j) = if i = j then 1 else 0 := by
  apply Int.cast_injective (α := ℂ)
  simp

variable (C : SuperCartanDatum I) (α : I → Module.Dual ℂ H)
    (ha : ∀ i j, α j (h i) = (C.a i j : ℂ))

/-- Source roots belong to the full integral weight lattice by their Cartan evaluations. -/
def root (j : I) : weightLattice h := ⟨α j, fun i ↦ ⟨C.a i j, ha i j⟩⟩

@[simp] theorem coroot_root (i j : I) : coroot h i (root h C α ha j) = C.a i j := by
  apply Int.cast_injective (α := ℂ)
  rw [cast_coroot]
  exact ha i j

/-- Complex-independent source roots remain independent over the integers in P. -/
theorem root_linearIndependent (hα : LinearIndependent ℂ α) :
    LinearIndependent ℤ (root h C α ha) :=
  LinearIndependent.of_comp (inclusion h) (hα.restrict_scalars' ℤ)

/-- The source realization as the existing covering-quantum root datum. -/
noncomputable def datum : RootDatum I (weightLattice h) where
  toSuperCartanDatum := C
  cd := {
    root := root h C α ha
    coroot := coroot h
    coroot_root_self := fun i ↦ by rw [coroot_root, C.isGCM.diag] }
  coroot_root := coroot_root h C α ha

variable (hh : LinearIndependent ℂ h) (J : Finset I) (W : Finset (weightLattice h))

/-- A window inside the actual source P, with unrestricted finite seed weights. -/
noncomputable abbrev window :=
  FiniteWeightWindow.lattice W (fun j : J ↦ root h C α ha j)
    (fun j : J ↦ omega h hh j)

/-- The actual finite-colour datum retains the original Cartan evaluations. -/
noncomputable def windowDatum : RootDatum J (window h C α ha hh J W) :=
  (datum h C α ha).weightWindow J W (fun j ↦ omega h hh j)

theorem window_free : Module.Free ℤ (window h C α ha hh J W) := inferInstance

theorem window_coroot_linearIndependent :
    LinearIndependent ℤ (windowDatum h C α ha hh J W).cd.coroot := by
  classical
  apply (datum h C α ha).weightWindow_coroot_linearIndependent
  intro i j
  change coroot h i (omega h hh j) = _
  simp only [coroot_omega, Subtype.coe_inj]

theorem window_root_linearIndependent (hα : LinearIndependent ℂ α) :
    LinearIndependent ℤ (windowDatum h C α ha hh J W).α := by
  apply (datum h C α ha).weightWindow_root_linearIndependent
  exact (root_linearIndependent h C α ha hα).comp (fun j : J ↦ (j : I))
    Subtype.val_injective

/-- Every seed survives literally, including arbitrary infinite-support or central weights. -/
def seedLift (x : weightLattice h) (hx : x ∈ W) : window h C α ha hh J W :=
  ⟨x, FiniteWeightWindow.weight_mem W _ _ hx⟩

@[simp] theorem seedLift_coe (x : weightLattice h) (hx : x ∈ W) :
    (seedLift h C α ha hh J W x hx : weightLattice h) = x := rfl

end OddMath.CoveringQuantum.SourceWeightLattice
