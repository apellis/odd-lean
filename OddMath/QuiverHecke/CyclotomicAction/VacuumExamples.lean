/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Vacuum
import OddMath.QuiverHecke.Examples

/-! # A nonzero vacuum inclusion over the rationals

The zero-polynomial specialization tests the height-one quotient and the
vacuum colour cut without imposing a finite-dimensionality assertion.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke.VacuumExamples
open Examples

private theorem canWord_one (n : ℕ) : Categorification.TypeA.canWord n 1 = [] := by
  apply List.length_eq_zero_iff.mp
  rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]

private def identityIndex : NFIdx [()] [()] :=
  ⟨([], 1), by simp, by simp, by simp [canWord_one, cw]⟩

private theorem identity_ne_zero :
    (𝟙 ((pres datum scalars).obj (ob datum [()]))) ≠ 0 := by
  have h := (linearIndependent_nf datum scalars [()] [()]).ne_zero identityIndex
  have hn : identityIndex.nf (D := datum) (Sc := scalars) =
      𝟙 ((pres datum scalars).obj (ob datum [()])) := by
    simp only [NFIdx.nf, identityIndex, List.map_nil, List.nil_append, canWord_one, cw]
    rw [cl, ← Presentation.diag_id]
    exact Presentation.diag_eq_of_layers_eq _ rfl
  rwa [hn] at h

private theorem zero_ideal : cyclotomicIdeal datum scalars (fun _ => 0) 0 = ⊥ := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro z ⟨w, b, rfl⟩
    simp [cyclotomicGenerator]
  · exact bot_le

/-- The vacuum unit survives in the height-one zero-polynomial quotient. -/
theorem vacuum_unit_ne_zero :
    vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := by
  let : DecidableEq (Word Unit 1) := Classical.decEq _
  rw [vacuumAppend_one]
  intro h
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp h
  rw [zero_ideal] at hm
  have he : Hn.wordIdempotent (appendWord () (vacuumWord (I := Unit))) =
      (0 : Hn datum scalars 1) := hm
  let w : Word Unit 1 := appendWord () vacuumWord
  have hs : (DFinsupp.single (w, w) (𝟙 (wordObj datum scalars w)) : Hn datum scalars 1) =
      DFinsupp.single (w, w) 0 := by
    rw [DFinsupp.single_zero]
    simpa only [Hn.wordIdempotent, FiniteHomMatrix.idem, FiniteHomMatrix.single] using he
  have hi : (𝟙 (wordObj datum scalars w)) = 0 :=
    DFinsupp.single_injective (i := (w, w)) hs
  exact identity_ne_zero hi

/-- A nonzero scalar is not lost by the vacuum inclusion. -/
theorem vacuum_two_ne_zero :
    vacuumAppend datum scalars () (fun _ => 0)
      (algebraMap ℚ (Hn datum scalars 0) 2) ≠ 0 := by
  rw [vacuumAppend_scalar]
  exact smul_ne_zero (by norm_num)
    (by simpa only [vacuumAppend_one] using vacuum_unit_ne_zero)

/-- The scalar formula is compatible with the even quotient component. -/
theorem vacuum_two_even :
    vacuumAppend datum scalars () (fun _ => 0)
      (algebraMap ℚ (Hn datum scalars 0) 2) ∈
      cyclotomicParity datum scalars (fun _ => 0) (by intro i m h; simp at h) 0 0 := by
  apply vacuumAppend_parity
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (SetLike.one_mem_graded _)

end OddMath.QuiverHecke.VacuumExamples
