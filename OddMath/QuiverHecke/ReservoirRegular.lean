/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ReservoirVacuumDetection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Regular coordinates on the connected reservoir

Ports the cyclic-coordinate step of
`Categorification/KLR/CyclotomicAction/Vacuum.lean` and
`Categorification/KLR/CyclotomicAction/VacuumProduct.lean` to the signed
coefficient category. Composition below is the existing super coefficient
composition, not ordinary multiplication on an unsigned tensor product.
The maps act on the exact ELV quotient. Comparison with the word module of a
fused action remains separate.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The defining relation span is stable under postcomposition. -/
theorem elvRelationSpan_postcomp {s t t' : List I}
    (g : coefficientObj D Sc t ⟶ coefficientObj D Sc t')
    {f : coefficientObj D Sc s ⟶ coefficientObj D Sc t}
    (hf : f ∈ ELVRelationSpan D Sc cutoff s t) :
    f ≫ g ∈ ELVRelationSpan D Sc cutoff s t' := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v, hv, r, hr, a, b, rfl⟩ := hf
    exact Submodule.subset_span ⟨v, hv, r, hr, a, b ≫ g, by simp⟩
  | zero => simp
  | add f h _ _ hf hh => simpa using Submodule.add_mem _ hf hh
  | smul r f _ hf => simpa using Submodule.smul_mem _ r hf

/-- Postcomposition on a fixed source component of the connected regular module. -/
def reservoirPostcomp {s t t' : List I}
    (g : coefficientObj D Sc t ⟶ coefficientObj D Sc t') :
    ReservoirQuotient D Sc cutoff s t →ₗ[k] ReservoirQuotient D Sc cutoff s t' :=
  (ELVRelationSpan D Sc cutoff s t).mapQ (ELVRelationSpan D Sc cutoff s t')
    { toFun := fun f => f ≫ g
      map_add' := by intros; simp
      map_smul' := by intros; simp }
    (by intro f hf; exact elvRelationSpan_postcomp D Sc cutoff g hf)

@[simp] theorem reservoirPostcomp_mk {s t t' : List I}
    (g : coefficientObj D Sc t ⟶ coefficientObj D Sc t')
    (f : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    reservoirPostcomp D Sc cutoff g ((ELVRelationSpan D Sc cutoff s t).mkQ f) =
      (ELVRelationSpan D Sc cutoff s t').mkQ (f ≫ g) := rfl

/-- The cyclic regular vector at a word. -/
def reservoirRegularGenerator (t : List I) : ReservoirQuotient D Sc cutoff t t :=
  (ELVRelationSpan D Sc cutoff t t).mkQ (𝟙 _)

/-- Evaluation on the regular cyclic vector gives precisely the quotient class. -/
@[simp] theorem reservoirPostcomp_generator {t t' : List I}
    (g : coefficientObj D Sc t ⟶ coefficientObj D Sc t') :
    reservoirPostcomp D Sc cutoff g (reservoirRegularGenerator D Sc cutoff t) =
      (ELVRelationSpan D Sc cutoff t t').mkQ g := by
  unfold reservoirRegularGenerator
  rw [reservoirPostcomp_mk, Category.id_comp]

end OddMath.QuiverHecke
