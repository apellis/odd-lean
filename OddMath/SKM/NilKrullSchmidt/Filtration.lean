/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.NilKrullSchmidt.Basic

/-!
# Nilpotent filtrations and Karoubi envelopes of matrix categories

Input for the first preliminary fact of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, §11, without degreewise finite-dimensionality. A `NilFiltration` of a
linear category is a multiplicative decreasing filtration of all Hom-spaces by subspaces,
exhaustive at `0`, vanishing on each Hom-space in large filtration degree, and of finite
codimension in filtration degree `1`. The idempotent completion of its additive envelope
is then `NilFinite`: endomorphisms with all matrix entries in filtration degree `1` form a
nilpotent two-sided ideal of finite codimension.
-/

noncomputable section

namespace OddMath.KrullSchmidtNil

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Module

universe v u

variable (k : Type*) [Field k] (𝒞 : Type u) [Category.{v} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]

/-- A multiplicative decreasing filtration of Hom-spaces with finite-codimensional first
step, vanishing on each Hom-space in large degree. -/
structure NilFiltration where
  F : ℕ → ∀ X Y : 𝒞, Submodule k (X ⟶ Y)
  zero : ∀ X Y, F 0 X Y = ⊤
  antitone : ∀ d X Y, F (d + 1) X Y ≤ F d X Y
  comp_mem : ∀ {a b : ℕ} {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z},
    f ∈ F a X Y → g ∈ F b Y Z → f ≫ g ∈ F (a + b) X Z
  vanish : ∀ X Y, ∃ D, F D X Y = ⊥
  finiteDimensional : ∀ X Y, FiniteDimensional k ((X ⟶ Y) ⧸ F 1 X Y)

namespace NilFiltration

variable {k 𝒞}
variable (Φ : NilFiltration k 𝒞)

theorem mem_of_le {d e : ℕ} (h : d ≤ e) {X Y : 𝒞} {f : X ⟶ Y} (hf : f ∈ Φ.F e X Y) :
    f ∈ Φ.F d X Y := by
  induction h with
  | refl => exact hf
  | step _ ih => exact ih (Φ.antitone _ X Y hf)

theorem mem_zero {X Y : 𝒞} (f : X ⟶ Y) : f ∈ Φ.F 0 X Y := by
  rw [Φ.zero]; exact Submodule.mem_top

theorem eq_zero_of_le {X Y : 𝒞} {D e : ℕ} (hD : Φ.F D X Y = ⊥) (h : D ≤ e) {f : X ⟶ Y}
    (hf : f ∈ Φ.F e X Y) : f = 0 := by
  have := Φ.mem_of_le h hf
  rwa [hD, Submodule.mem_bot] at this

/-- The matrix entries of a morphism of the Karoubi envelope of `Mat_ 𝒞`, modulo filtration
degree `1`. -/
def entryQuot (P Q : Karoubi (Mat_ 𝒞)) :
    (P ⟶ Q) →ₗ[k] ∀ i : P.X.ι, ∀ j : Q.X.ι, (P.X.X i ⟶ Q.X.X j) ⧸ Φ.F 1 (P.X.X i) (Q.X.X j) where
  toFun f i j := Submodule.Quotient.mk (f.f i j)
  map_add' f g := by
    funext i j
    change Submodule.Quotient.mk (f.f i j + g.f i j) = _
    rw [Submodule.Quotient.mk_add]
    rfl
  map_smul' r f := by
    funext i j
    simp only [RingHom.id_apply, Pi.smul_apply, ← Submodule.Quotient.mk_smul]
    rfl

theorem mem_ker_entryQuot {P Q : Karoubi (Mat_ 𝒞)} (f : P ⟶ Q) :
    f ∈ LinearMap.ker (Φ.entryQuot P Q) ↔ ∀ i j, f.f i j ∈ Φ.F 1 _ _ := by
  simp only [LinearMap.mem_ker, entryQuot, LinearMap.coe_mk, AddHom.coe_mk, funext_iff,
    Pi.zero_apply, Submodule.Quotient.mk_eq_zero]

theorem comp_entry_mem {a b : ℕ} {P Q R : Karoubi (Mat_ 𝒞)} {f : P ⟶ Q} {g : Q ⟶ R}
    (hf : ∀ i j, f.f i j ∈ Φ.F a _ _) (hg : ∀ i j, g.f i j ∈ Φ.F b _ _) :
    ∀ i j, (f ≫ g).f i j ∈ Φ.F (a + b) _ _ := by
  intro i j
  rw [Karoubi.comp_f, Mat_.comp_apply]
  exact Submodule.sum_mem _ fun l _ => Φ.comp_mem (hf i l) (hg l j)

theorem pow_entry_mem {P : Karoubi (Mat_ 𝒞)} {f : P ⟶ P} (hf : ∀ i j, f.f i j ∈ Φ.F 1 _ _) :
    ∀ m : ℕ, ∀ i j, (toEnd f ^ m : P ⟶ P).f i j ∈ Φ.F m _ _ := by
  intro m
  induction m with
  | zero => exact fun i j => Φ.mem_zero _
  | succ m ih =>
    rw [pow_succ, End.mul_def, add_comm]
    exact Φ.comp_entry_mem hf ih

/-- A nilpotent filtration makes the Karoubi envelope of the additive envelope
`NilFinite`. -/
theorem nilFinite_karoubi (Φ : NilFiltration k 𝒞) : NilFinite k (Karoubi (Mat_ 𝒞)) where
  exists_isNilIdeal P := by
    refine ⟨LinearMap.ker (Φ.entryQuot P P), ?_, ?_, ?_, ?_⟩
    · intro f g hg
      rw [mem_ker_entryQuot] at hg ⊢
      simpa only [zero_add] using Φ.comp_entry_mem (fun i j => Φ.mem_zero (f.f i j)) hg
    · intro f g hf
      rw [mem_ker_entryQuot] at hf ⊢
      simpa only [add_zero] using Φ.comp_entry_mem hf (fun i j => Φ.mem_zero (g.f i j))
    · intro f hf
      rw [mem_ker_entryQuot] at hf
      classical
      choose D hD using fun ij : P.X.ι × P.X.ι => Φ.vanish (P.X.X ij.1) (P.X.X ij.2)
      let L := Finset.univ.sup D
      refine ⟨L, ?_⟩
      apply Karoubi.hom_ext
      apply Mat_.hom_ext
      intro i j
      have hL : D (i, j) ≤ L := Finset.le_sup (Finset.mem_univ _)
      rw [Φ.eq_zero_of_le (hD (i, j)) hL (Φ.pow_entry_mem hf L i j)]
      rfl
    · have : FiniteDimensional k (LinearMap.range (Φ.entryQuot P P)) := by
        have := fun i j => Φ.finiteDimensional (P.X.X i) (P.X.X j)
        infer_instance
      exact LinearEquiv.finiteDimensional (Φ.entryQuot P P).quotKerEquivRange.symm

end NilFiltration

end OddMath.KrullSchmidtNil
