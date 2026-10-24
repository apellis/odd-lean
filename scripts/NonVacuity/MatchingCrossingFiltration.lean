import OddMath.SKM.Nondegeneracy
import OddMath.SKM.MixedCrossingLocalExamples

/-!
Crossing-filtered expansions for dotted two-colour odd matchings.
The support bounds use abstract SYM coefficients and arbitrary complete choices.
These are existence statements, not matching independence or nonvanishing claims.
-/

noncomputable section
namespace NonVacuity.MatchingCrossingFiltration
open CategoryTheory StringDiagrams Presentation StringDiagrams.Chord OddMath.SKM
open MixedCrossingLocalExamples

private abbrev D₂ := oddDatum
private def sc : Scalars D₂ ℚ where
  t := fun _ _ => 1
  t_self := by intros; rfl
  t_symm_of_d_eq_zero := by intros; rfl
  s := fun _ _ _ _ => 0
  s_symm := by intros; rfl
  s_eq_zero := by intros; rfl
  two_isUnit := by intro _; exact isUnit_iff_ne_zero.mpr (by norm_num)

private def cs : CScalars sc where
  c := fun _ _ => 1
  shift := by intros; simp [sc]

private def sourceChoice : MatchingBasisChoice A [] :=
  Classical.choice (MatchingBasisChoice.nonempty A [])

private def targetChoice : MatchingBasisChoice B [] :=
  Classical.choice (MatchingBasisChoice.nonempty B [])

/-- The one-crossing dotted matching has an expansion with no higher-crossing labels. -/
theorem source_dotted_expansion :
    ∃ z : sourceChoice.Labels →₀ SYM D₂ ℚ,
      sourceChoice.expansion cs 0 z = xev cs 0 A [] (dLay A sourceDots) ∧
        ∀ t ∈ z.support, ncr₂ t.1.val < 2 := by
  exact sourceChoice.exists_expansion_of_mem_ltL cs 0
    (Submodule.subset_span ⟨dLay A sourceDots, by decide, rfl⟩)

/-- The zero-crossing dotted matching uses only zero-crossing representatives. -/
theorem target_dotted_expansion :
    ∃ z : targetChoice.Labels →₀ SYM D₂ ℚ,
      targetChoice.expansion cs 0 z = xev cs 0 B [] (dLay B targetDots) ∧
        ∀ t ∈ z.support, ncr₂ t.1.val = 0 := by
  obtain ⟨z, hz, hbound⟩ := targetChoice.exists_expansion_of_mem_ltL cs 0
    (N := 1) (Submodule.subset_span ⟨dLay B targetDots, by decide, rfl⟩)
  exact ⟨z, hz, fun t ht => by have := hbound t ht; omega⟩

#print axioms OddMath.SKM.ltL_le_of_canon_dots_mem
#print axioms OddMath.SKM.ltL_le_diagBubSpan_decoratedFamily₂
#print axioms OddMath.SKM.MatchingBasisChoice.exists_expansion_of_mem_ltL
#print axioms source_dotted_expansion
#print axioms target_dotted_expansion
end NonVacuity.MatchingCrossingFiltration
