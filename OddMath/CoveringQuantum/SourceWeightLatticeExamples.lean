/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.SourceWeightLattice

/-! # Complex realization with infinite colours and a retained central direction -/

noncomputable section

namespace OddMath.CoveringQuantum.SourceWeightLatticeConsumer

open SourceWeightLattice

abbrev H := (ℕ →₀ ℂ) × ℂ

def h (i : ℕ) : H := (Finsupp.single i 1, 0)

def coord (i : ℕ) : Module.Dual ℂ H :=
  (Finsupp.lapply i).comp (LinearMap.fst ℂ (ℕ →₀ ℂ) ℂ)

def centralForm : Module.Dual ℂ H := LinearMap.snd ℂ (ℕ →₀ ℂ) ℂ

def alpha (i : ℕ) : Module.Dual ℂ H := (2 : ℂ) • coord i

def cartan : SuperCartanDatum ℕ where
  a i j := if i = j then 2 else 0
  isGCM := {
    diag := fun i ↦ by simp
    offDiag_nonpos := fun i j hij ↦ by simp [hij]
    zero_comm := fun i j ↦ by simp [eq_comm] }
  d _ := 1
  d_pos _ := by decide
  d_mul_symm i j := by simp [eq_comm]
  parity _ := 0
  even_of_odd _ _ hp := by simp at hp

theorem cartan_eval (i j : ℕ) : alpha j (h i) = (cartan.a i j : ℂ) := by
  simp [alpha, coord, h, cartan, Finsupp.single_apply]

theorem coroots_independent : LinearIndependent ℂ h := by
  apply linearIndependent_iff'.mpr
  intro s g hg i hi
  have he := congrArg (fun x : H ↦ coord i x) hg
  simpa [map_sum, h, coord, Finsupp.single_apply, hi, eq_comm] using he

theorem roots_independent : LinearIndependent ℂ alpha := by
  apply linearIndependent_iff'.mpr
  intro s g hg i hi
  have he := congrArg (fun f : Module.Dual ℂ H ↦ f (h i)) hg
  have hz : g i * 2 = 0 := by
    simpa [LinearMap.sum_apply, alpha, coord, h, Finsupp.single_apply, hi, eq_comm] using he
  exact (mul_eq_zero.mp hz).resolve_right (by norm_num)

abbrev P := weightLattice h

/-- All coroot coordinates are one; the central coefficient is the rational one-half. -/
def seed : P :=
  ⟨(Finsupp.linearCombination ℂ (fun _ : ℕ ↦ (1 : ℂ))).comp
      (LinearMap.fst ℂ (ℕ →₀ ℂ) ℂ) + (1 / 2 : ℂ) • centralForm,
    fun i ↦ ⟨1, by simp [h, centralForm]⟩⟩

def central : P := ⟨centralForm, fun i ↦ ⟨0, by simp [centralForm, h]⟩⟩

def colours : Finset ℕ := {0, 1}

noncomputable def weights : Finset P := by
  classical
  exact {seed, central}

noncomputable abbrev lattice :=
  window h cartan alpha cartan_eval coroots_independent colours weights

noncomputable abbrev restrictedDatum : RootDatum colours lattice :=
  windowDatum h cartan alpha cartan_eval coroots_independent colours weights

example : Infinite ℕ := inferInstance
example : Module.IsTorsionFree ℤ P := inferInstance
example : Module.Finite ℤ lattice := inferInstance
example : Module.Free ℤ lattice :=
  window_free h cartan alpha cartan_eval coroots_independent colours weights
example : LinearIndependent ℤ restrictedDatum.cd.coroot :=
  window_coroot_linearIndependent h cartan alpha cartan_eval coroots_independent colours weights
example : LinearIndependent ℤ restrictedDatum.α :=
  window_root_linearIndependent h cartan alpha cartan_eval coroots_independent colours weights
    roots_independent

noncomputable def seedInWindow : lattice :=
  seedLift h cartan alpha cartan_eval coroots_independent colours weights seed (by simp [weights])

noncomputable def centralInWindow : lattice :=
  seedLift h cartan alpha cartan_eval coroots_independent colours weights central
    (by simp [weights])

theorem seed_retained : (seedInWindow : P) = seed := rfl

theorem seed_coroot (i : ℕ) : coroot h i seed = 1 := by
  apply Int.cast_injective (α := ℂ)
  simp [cast_coroot, seed, h, centralForm]

theorem seed_support_infinite : Set.Infinite (Function.support (fun i ↦ coroot h i seed)) := by
  simpa [Function.support, seed_coroot] using
    (Set.infinite_univ : Set.Infinite (Set.univ : Set ℕ))

theorem seed_central_value : ((seedInWindow : P) : Module.Dual ℂ H) (0, 1) = 1 / 2 := by
  simp [seedInWindow, seedLift, seed, centralForm]

theorem central_retained : (centralInWindow : P) = central := rfl

theorem central_nonzero : centralInWindow ≠ 0 := by
  intro he
  have hv := congrArg (fun x : lattice ↦ ((x : P) : Module.Dual ℂ H) (0, 1)) he
  norm_num [centralInWindow, seedLift, central, centralForm] at hv

theorem central_coroot_zero (i : ℕ) : coroot h i (centralInWindow : P) = 0 := by
  apply Int.cast_injective (α := ℂ)
  simp [cast_coroot, centralInWindow, seedLift, central, centralForm, h]

/-- The Hamel-extension weights separate even colours outside the selected window. -/
example : coroot h 37 (omega h coroots_independent 37) = 1 := by simp
example : coroot h 38 (omega h coroots_independent 37) = 0 := by simp

end OddMath.CoveringQuantum.SourceWeightLatticeConsumer


/-! # Product-weight consumer with an infinite-support weight and central direction -/

namespace OddMath.CoveringQuantum.FiniteWeightWindowConsumer

open FiniteWeightWindow

abbrev Weight := (ℕ → ℤ) × ℚ

def omega (j : ℕ) : Weight := (fun i ↦ if j = i then 1 else 0, 0)

def coroot (i : ℕ) : Module.Dual ℤ Weight where
  toFun x := x.1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def datum : RootDatum ℕ Weight where
  a i j := if i = j then 2 else 0
  isGCM := {
    diag := fun i ↦ by simp
    offDiag_nonpos := fun i j hij ↦ by simp [hij]
    zero_comm := fun i j ↦ by simp [eq_comm] }
  d _ := 1
  d_pos _ := by decide
  d_mul_symm i j := by simp [eq_comm]
  parity _ := 0
  even_of_odd _ _ h := by simp at h
  cd := {
    root := fun j ↦ 2 • omega j
    coroot := coroot
    coroot_root_self := fun i ↦ by simp [coroot, omega] }
  coroot_root i j := by simp [coroot, omega, eq_comm]

def colours : Finset ℕ := {0, 1}

/-- The first component is nonzero at every natural index; the second is central. -/
def seed : Weight := (fun _ ↦ 1, 1 / 2)

def central : Weight := (0, 1)

noncomputable def weights : Finset Weight := by
  classical
  exact {seed, central}

abbrev selectedRoots : colours → Weight := fun j ↦ datum.α j
abbrev selectedOmega : colours → Weight := fun j ↦ omega j
noncomputable abbrev window := lattice weights selectedRoots selectedOmega

example : Infinite ℕ := inferInstance
example : Module.IsTorsionFree ℤ Weight := inferInstance

theorem separation (i j : colours) :
    datum.h i (selectedOmega j) = if i = j then 1 else 0 := by
  change (if (j : ℕ) = (i : ℕ) then (1 : ℤ) else 0) = _
  simp only [Subtype.coe_inj, eq_comm]

theorem selectedRoots_independent : LinearIndependent ℤ selectedRoots := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg j
  have he := congrArg (fun x : Weight ↦ coroot j x) hg
  have hz : g j * 2 = 0 := by
    simpa [map_sum, selectedRoots, datum, coroot, omega, Subtype.coe_inj, eq_comm] using he
  omega

example : Module.Finite ℤ window := inferInstance
example : Module.Free ℤ window := free weights selectedRoots selectedOmega
example : Function.Injective (inclusion weights selectedRoots selectedOmega) :=
  inclusion_injective weights selectedRoots selectedOmega
example : Module.Finite ℤ (dual weights selectedRoots selectedOmega) :=
  dual_finite weights selectedRoots selectedOmega
example : Module.Free ℤ (dual weights selectedRoots selectedOmega) :=
  dual_free weights selectedRoots selectedOmega

example : LinearIndependent ℤ (datum.weightWindow colours weights selectedOmega).cd.coroot :=
  datum.weightWindow_coroot_linearIndependent colours weights selectedOmega separation

example : LinearIndependent ℤ (datum.weightWindow colours weights selectedOmega).α :=
  datum.weightWindow_root_linearIndependent colours weights selectedOmega selectedRoots_independent

noncomputable def seedLift : window :=
  ⟨seed, weight_mem weights selectedRoots selectedOmega (by simp [weights])⟩

noncomputable def centralLift : window :=
  ⟨central, weight_mem weights selectedRoots selectedOmega (by simp [weights])⟩

theorem seed_retained : (seedLift : Weight) = seed := rfl

theorem seed_support_infinite : Set.Infinite (Function.support seed.1) := by
  simpa [Function.support, seed] using (Set.infinite_univ : Set.Infinite (Set.univ : Set ℕ))

theorem seed_central_nonzero : (seedLift : Weight).2 ≠ 0 := by
  norm_num [seedLift, seed]

theorem central_retained : (centralLift : Weight).2 = 1 := rfl

theorem central_nonzero : centralLift ≠ 0 := by
  intro h
  have he := congrArg (fun x : window ↦ (x : Weight).2) h
  norm_num [centralLift, central] at he

theorem central_coroot_zero (i : ℕ) : coroot i (centralLift : Weight) = 0 := rfl

example (x : window) (f : dual weights selectedRoots selectedOmega) :
    perfect weights selectedRoots selectedOmega x f = f x := rfl

example (x : window) :
    (perfect weights selectedRoots selectedOmega).symm
      (perfect weights selectedRoots selectedOmega x) = x :=
  (perfect weights selectedRoots selectedOmega).symm_apply_apply x

example : (lattice (∅ : Finset Weight) (fun j : Fin 0 ↦ Fin.elim0 j)
    (fun j : Fin 0 ↦ Fin.elim0 j)) = ⊥ := by
  simp [lattice]

end OddMath.CoveringQuantum.FiniteWeightWindowConsumer
