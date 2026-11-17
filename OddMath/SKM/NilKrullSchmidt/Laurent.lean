/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.NilKrullSchmidt.Filtration
import StringDiagrams.Super.GSKarLaurent

/-!
# Laurent Krull–Schmidt bases modulo nil ideals

The corrected first preliminary fact of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, §11, used in Theorems 11.3 and 11.7, under `NilFinite` instead of
finite-dimensionality of degree-zero Homs: `K₀` is free over `ℤ[q, q⁻¹]` on the
integer-shift orbits of indecomposables whenever the spaces of maps from sufficiently
negative shifts of an indecomposable to itself vanish.

For graded additive Karoubi envelopes, `NilFinite` follows from a nilpotent filtration of
the shifted degree-zero category (`NilFiltration`), and the vanishing condition from a lower
bound on the degrees of the original Hom-spaces.
-/

noncomputable section

namespace OddMath.KrullSchmidtNil

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Module
  StringDiagrams StringDiagrams.KrullSchmidt LaurentPolynomial

variable (k : Type*) [Field k] {C : Type*} [Category C] [Preadditive C]
    [Linear k C] [QPiCategory k C] [HasBinaryBiproducts C] [NilFinite k C]
    [IsIdempotentComplete C]

/-- The Laurent basis on integer-shift orbits of indecomposables, under `NilFinite`. -/
def laurentBasis (h : ShiftHomBoundedBelow k (C := C)) :
    letI := K₀.moduleLaurentInt k C
    letI := indecShiftAction k (C := C)
    Basis (LaurentBasis.Orbit (ι := IndecClass C)) (LaurentPolynomial ℤ) (K₀ C) := by
  let := K₀.moduleLaurentInt k C
  let := indecShiftAction k (C := C)
  exact LaurentBasis.ofOrbits (indecBasis k)
    (fun n i => by
      simp only [indecBasis_apply]
      exact int_T_smul_indec k n i)
    (indec_shift_free k h)

/-- `K₀` is free over `ℤ[q, q⁻¹]` under `NilFinite` and the shift lower bound. -/
theorem k0_free_laurentInt (h : ShiftHomBoundedBelow k (C := C)) :
    letI := K₀.moduleLaurentInt k C
    Module.Free (LaurentPolynomial ℤ) (K₀ C) := by
  let := K₀.moduleLaurentInt k C
  exact Module.Free.of_basis (laurentBasis k h)

end OddMath.KrullSchmidtNil

namespace OddMath.KrullSchmidtNil.GSKar

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Module
  StringDiagrams StringDiagrams.GSKar GradedSupercategory Supercategory

variable {k C : Type*} [Field k] [Category C] [Preadditive C] [Linear k C]
  [Supercategory k C] [GradedSupercategory k C]

/-- A nilpotent filtration of the shifted degree-zero category makes the graded additive
Karoubi envelope `NilFinite`. -/
theorem nilFinite (Φ : NilFiltration k (ShiftBase k C)) : NilFinite k (GSKar k C) :=
  Φ.nilFinite_karoubi

/-- Laurentian lower bounds of the original category imply the categorical shift bound on
every indecomposable of the graded additive Karoubi envelope, under `NilFinite`. -/
theorem shiftHomBoundedBelow [NilFinite k (GSKar k C)]
    (h : HomBoundedBelow (k := k) (C := C)) :
    KrullSchmidt.ShiftHomBoundedBelow k (C := GSKar k C) := by
  intro i
  obtain ⟨N, hN⟩ := shift_hom_boundedBelow h i.rep i.rep
  refine ⟨N, fun n hn => ?_⟩
  have heq : K₀.mk (KrullSchmidt.indecShift k n i).rep =
      K₀.mk ((shiftFunctor n).obj i.rep) := by
    rw [← int_T_smul_mk]
    exact (KrullSchmidt.int_T_smul_indec k n i).symm
  obtain ⟨f, g, hfg⟩ := exists_retract_of_mk_eq k
    (KrullSchmidt.indecShift k n i).isIndec_rep heq
  have := hN n hn
  refine ⟨fun a b => ?_⟩
  rw [← Category.id_comp a, ← Category.id_comp b, ← hfg, Category.assoc, Category.assoc,
    Subsingleton.elim (g ≫ a) (g ≫ b)]

/-- The Laurentian envelope theorem used by BE2 Theorems 11.3 and 11.7 under a nilpotent
filtration of the shifted degree-zero category instead of degreewise finite-dimensionality:
`K₀` is free over `ℤ[q, q⁻¹]`, with basis the integer-shift orbits of indecomposables. -/
theorem k0_free_laurentInt (Φ : NilFiltration k (ShiftBase k C))
    (h : HomBoundedBelow (k := k) (C := C)) :
    letI := K₀.moduleLaurentInt k (GSKar k C)
    Module.Free (LaurentPolynomial ℤ) (K₀ (GSKar k C)) := by
  have := nilFinite Φ
  exact KrullSchmidtNil.k0_free_laurentInt k (shiftHomBoundedBelow h)

end OddMath.KrullSchmidtNil.GSKar
