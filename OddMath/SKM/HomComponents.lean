/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.Envelope
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Shifted Hom spaces and homogeneous components

For Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
§12, the comparison of shifted even degree-zero Hom spaces with graded super-Hom
components. We construct this comparison for `UGr` and `UUnderline` over a
commutative ring, under (1.31). No finiteness of colours or Hom spaces is needed.
The source shift is `n`: the envelope degree is `d + targetShift - sourceShift`.
This is a prerequisite for the dimension comparison, not Theorem 12.1.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Supercategory GradedSupercategory

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous} {ν μ : UGr D Sc sy hc}

/-- The 1-morphism `Q^n Π^a A` in the underlying SKM 2-category. -/
abbrev shiftedUnderlying (n : ℤ) (a : ZMod 2) (A : ν ⟶ μ) :
    (⟨⟨⟨⟨ν⟩⟩⟩⟩ : UUnderline D Sc sy hc) ⟶ ⟨⟨⟨⟨μ⟩⟩⟩⟩ :=
  ⟨⟨QPiEnvelope.mk n a A⟩⟩

/-- The degree-`n`, parity-`a` component of the SKM super-Hom module. -/
abbrev homComponent (A B : ν ⟶ μ) (n : ℤ) (a : ZMod 2) : Submodule k (A ⟶ B) :=
  degree (R := k) A B n ⊓ parity (R := k) A B a

/-- Forgetting the degree-zero and even wrappers identifies shifted underlying
Hom with the homogeneous component. The inverse is induced by `QPiEnvelope.ofHom`. -/
def shiftedHomEquiv (A B : ν ⟶ μ) (n : ℤ) (a : ZMod 2) :
    (shiftedUnderlying n a A ⟶ shiftedUnderlying 0 0 B) ≃ₗ[k]
      homComponent A B n a where
  toFun f := ⟨QPiEnvelope.toHom f.1.1, by
    constructor
    · change f.1.1 ∈ degree (R := k) A B n
      have h := f.1.2
      change f.1.1 ∈ degree (R := k) A B (0 + (n - 0)) at h
      rw [sub_zero, zero_add] at h
      exact h
    · change f.1.1 ∈ parity (R := k) A B a
      have h := f.2
      change f.1.1 ∈ parity (R := k) A B (0 + (a + 0)) at h
      rw [add_zero, zero_add] at h
      exact h⟩
  invFun f := ⟨⟨QPiEnvelope.ofHom f.1, by
    change f.1 ∈ degree (R := k) A B (0 + (n - 0))
    rw [sub_zero, zero_add]
    exact f.2.1⟩, by
    change f.1 ∈ parity (R := k) A B (0 + (a + 0))
    rw [add_zero, zero_add]
    exact f.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem shiftedHomEquiv_apply_val (A B : ν ⟶ μ) (n : ℤ) (a : ZMod 2)
    (f : shiftedUnderlying n a A ⟶ shiftedUnderlying 0 0 B) :
    (shiftedHomEquiv A B n a f).1 = QPiEnvelope.toHom f.1.1 := rfl

@[simp]
theorem shiftedHomEquiv_symm_apply_val (A B : ν ⟶ μ) (n : ℤ) (a : ZMod 2)
    (f : homComponent A B n a) :
    ((shiftedHomEquiv A B n a).symm f).1.1 = QPiEnvelope.ofHom f.1 := rfl

@[simp]
theorem shiftedHomEquiv_id (A : ν ⟶ μ) :
    shiftedHomEquiv A A 0 0 (𝟙 (shiftedUnderlying 0 0 A)) =
      ⟨𝟙 A, id_mem_degree A, id_mem A⟩ := rfl

end OddMath.SKM

namespace OddMath.SKM

open CategoryTheory

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [Field k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous} {ν μ : UGr D Sc sy hc}

/-- The finite-dimensional version of the §12 coefficient comparison.
Both spaces are explicitly finite-dimensional; this does not assert local finiteness. -/
theorem shiftedHom_finrank (A B : ν ⟶ μ) (n : ℤ) (a : ZMod 2)
    [FiniteDimensional k (shiftedUnderlying n a A ⟶ shiftedUnderlying 0 0 B)]
    [FiniteDimensional k (homComponent A B n a)] :
    Module.finrank k (shiftedUnderlying n a A ⟶ shiftedUnderlying 0 0 B) =
      Module.finrank k (homComponent A B n a) :=
  (shiftedHomEquiv A B n a).finrank_eq

end OddMath.SKM
