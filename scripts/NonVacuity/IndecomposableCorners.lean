import OddMath

/-! # Indecomposable summands have residue field `k` and type M (BE2 Corollary 11.4)

On the datum of `OddMath.QuiverHecke.AlgebraExamples` over `ℚ`: the unit object `(∅, 1)` is
indecomposable (its endomorphisms are the scalars, and `1 ≠ 0` by the normal form basis), so the
corollary applies to it.
-/

noncomputable section
open CategoryTheory StringDiagrams KrullSchmidt OddMath.SKM.Summands
open OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples Categorification.TypeA

namespace NonVacuity.IndecomposableCorners

theorem id_ne_zero : 𝟙 (hObj datum scalars symmetrizer homogeneous []) ≠ 0 := by
  intro h
  have hw : canWord 0 1 = [] := List.length_eq_zero_iff.1 (by simp [length_canWord])
  let i : NFIdx (I := ℕ) [] [] := ⟨([], 1), List.Pairwise.nil, by simp, by simp [hw, cw]⟩
  refine (linearIndependent_nf datum scalars [] []).ne_zero i ?_
  rw [← Category.comp_id i.nf]
  exact (congrArg (i.nf ≫ ·) h).trans Limits.comp_zero

theorem isIndec_unit : IsIndec (Wd datum scalars symmetrizer homogeneous [] 0 0) := by
  refine ⟨fun hZ => id_ne_zero ?_, fun e he => ?_⟩
  · have := congrArg evR ((Limits.IsZero.iff_id_eq_zero _).1 hZ)
    rwa [evR_id] at this
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (mem_span_id_nil (evR e))
    have he' := congrArg evR he
    rw [evR_comp, ← hc, Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul] at he'
    have hcc : (c * c - c) • 𝟙 (hObj datum scalars symmetrizer homogeneous []) = 0 := by
      rw [sub_smul, he', sub_self]
    have hc2 : c * (c - 1) = 0 := by
      rw [mul_sub, mul_one]; exact (smul_eq_zero.1 hcc).resolve_right id_ne_zero
    rcases mul_eq_zero.1 hc2 with h0 | h1
    · left; exact evR_injective (by rw [← hc, h0, zero_smul]; rfl)
    · right; exact evR_injective (by rw [← hc, sub_eq_zero.1 h1, one_smul]; rfl)

/-- **BE2 Corollary 11.4** for the indecomposable unit object. -/
example : CornerTypeM (𝟙 (hObj datum scalars symmetrizer homogeneous [])) :=
  cornerTypeM_of_isIndec (Category.id_comp _)
    ⟨GradedSupercategory.id_mem_degree _, Supercategory.id_mem _⟩ isIndec_unit

#print axioms cornerTypeM_of_isIndec

end NonVacuity.IndecomposableCorners
