/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVIdealSum
import OddMath.QuiverHecke.CyclotomicAction.ELVPDescent
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The cokernel of the full ELV P map

The ideal-sum equality identifies the kernel of the canonical append quotient
and its cokernel with the actual cyclotomic quotient on the enlarged word.
These are ground-ring linear maps; no polynomial module or projectivity
assertion is made.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The canonical quotient map imposing the remaining first-position relations. -/
def canonicalAppendTarget (i : I) (v w : List I) :
    AppendTarget D Sc cutoff i v w →ₗ[k] Old D Sc cutoff (v ++ [i]) w :=
  (appendRelations D Sc cutoff i v w).mapQ (ideal D Sc cutoff (v ++ [i]) w)
    LinearMap.id (appendRelations_le_ideal D Sc cutoff i v w)

@[simp] theorem canonicalAppendTarget_projection (i : I) (v w : List I)
    (f : hom D Sc cutoff (v ++ [i]) w) :
    canonicalAppendTarget D Sc cutoff i v w (appendProjection D Sc cutoff i v w f) =
      (ideal D Sc cutoff (v ++ [i]) w).mkQ f := rfl

theorem canonicalAppendTarget_surjective (i : I) (v w : List I) :
    Function.Surjective (canonicalAppendTarget D Sc cutoff i v w) := by
  intro z
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff (v ++ [i]) w).mkQ_surjective z
  exact ⟨appendProjection D Sc cutoff i v w f, rfl⟩

/-- The kernel is exactly the image of the prescribed descended P map. -/
theorem ker_canonicalAppendTarget (i : I) (v w : List I) :
    LinearMap.ker (canonicalAppendTarget D Sc cutoff i v w) =
      LinearMap.range (pMap D Sc cutoff i v w) := by
  ext z
  obtain ⟨f, rfl⟩ := appendProjection_surjective D Sc cutoff i v w z
  rw [LinearMap.mem_ker, canonicalAppendTarget_projection, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hf
    rw [ideal_eq_appendRelations_sup_range] at hf
    obtain ⟨r, hr, s, hs, he⟩ := Submodule.mem_sup.mp hf
    obtain ⟨b, rfl⟩ := hs
    refine ⟨projection D Sc cutoff i v w b, ?_⟩
    rw [← he, map_add, (appendProjection_eq_zero_iff D Sc cutoff i v w r).mpr hr, zero_add]
    rfl
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := (relations D Sc cutoff i v w).mkQ_surjective b
    have hh : appendProjection D Sc cutoff i v w (appendW D Sc cutoff i v ≫ a) =
        appendProjection D Sc cutoff i v w f := hb
    have hr : appendW D Sc cutoff i v ≫ a - f ∈ appendRelations D Sc cutoff i v w := by
      apply (appendProjection_eq_zero_iff D Sc cutoff i v w _).mp
      rw [map_sub, hh, sub_self]
    have hi := appendRelations_le_ideal D Sc cutoff i v w hr
    have hw := ideal_comp D Sc cutoff (appendW_mem_ideal D Sc cutoff i v) a
    have H := (ideal D Sc cutoff (v ++ [i]) w).sub_mem hw hi
    simpa only [sub_sub_cancel] using H

/-- The cokernel of P is the actual enlarged-word cyclotomic quotient. -/
def pMapCokernelEquiv (i : I) (v w : List I) :
    (AppendTarget D Sc cutoff i v w ⧸ LinearMap.range (pMap D Sc cutoff i v w)) ≃ₗ[k]
      Old D Sc cutoff (v ++ [i]) w :=
  (Submodule.quotEquivOfEq _ _ (ker_canonicalAppendTarget D Sc cutoff i v w).symm).trans
    ((canonicalAppendTarget D Sc cutoff i v w).quotKerEquivOfSurjective
      (canonicalAppendTarget_surjective D Sc cutoff i v w))

@[simp] theorem pMapCokernelEquiv_mk (i : I) (v w : List I)
    (z : AppendTarget D Sc cutoff i v w) :
    pMapCokernelEquiv D Sc cutoff i v w (Submodule.Quotient.mk z) =
      canonicalAppendTarget D Sc cutoff i v w z := rfl

end OddMath.QuiverHecke.ELVOld
