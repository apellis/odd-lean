import OddMath.SKM.Nondegeneracy
import OddMath.SKM.MixedCrossingLocalExamples

/-!
Signed decorated comparison on a two-colour odd matching over admissible rational scalars.
The repeated-dot example retains the separate error bounds; the zero-dot example removes
both lower-dot errors. Neither example asserts independence or nonvanishing of morphisms.
-/

noncomputable section
namespace NonVacuity.MatchingDecoratedSign
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

private def q : ℕ → ℕ × ℕ := Classical.choose (matching_bounded_points source_matching)
private theorem q_spec : ∀ j ∈ leftEnds₂ A R,
    (q j).1 ≤ R.length ∧ OnStrand₂ A R j (q j) :=
  Classical.choose_spec (matching_bounded_points source_matching)

private theorem exists_serialization (n : ℕ → ℕ) :
    ∃ ds, Decorates₂ A R q n ds := by
  apply exists_tmoves_dotPts_perm
  intro p hp
  obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
  rw [List.eq_of_mem_replicate hp]
  exact (q_spec j hj).1

private def σ (n : ℕ → ℕ) : List (DTMove Bool) := Classical.choose (exists_serialization n)
private theorem σ_spec (n : ℕ → ℕ) : Decorates₂ A R q n (σ n) :=
  Classical.choose_spec (exists_serialization n)

private abbrev s := pairing₂ A R
private abbrev v := s.map Prod.snd

private theorem canonical_crossings : ncr (canon s) = 1 :=
  (reduced₂_bent_normal_form cs 0 source_matching source_reduced.1).2.1.symm

/-- Three open dots, including a repeated dot, with separate lower-crossing and lower-dot errors. -/
theorem repeated_dot_comparison :
    ∃ (p : ZMod 2), ∃ eC eF eD,
      eC ∈ LtL D₂ sc cs 0 [] v 1 ∧
      eF ∈ FewerDots cs 0 s 3 ∧
      eD ∈ DecSpan cs 0 (dualW A ++ A) (cupA (dualW A))
        (R.map (shiftT A.length)) v 3 ∧
      xev cs 0 [] v (chordLay [] (canon s) ++ dotsOn v [0, 0, 1]) =
        zsign ℚ p • xev cs 0 [] v (cupA (dualW A) ++
          dLay (dualW A ++ A) ((σ (fun j => ([0, 0, 1].map (lEnd s)).count j)).map
            (shiftD A.length))) + (eC + (eF + eD)) := by
  exact canon_dots_eq_sign_decorated₂_add_errors (cs := cs) 0 A [] R
    source_matching source_reduced.1 q (fun j hj => (q_spec j hj).2) σ σ_spec
    source_matching.pairing_properties.2.2.symm 1
    source_matching.pairing_properties.1 source_matching.pairing_properties.2.1
    canonical_crossings (Iso.refl _) [0, 0, 1] (by decide)

/-- With no open dots, only a strictly lower-crossing error remains. -/
theorem zero_dot_comparison :
    ∃ (p : ZMod 2), ∃ eC,
      eC ∈ LtL D₂ sc cs 0 [] v 1 ∧
      xev cs 0 [] v (chordLay [] (canon s)) =
        zsign ℚ p • xev cs 0 [] v (cupA (dualW A) ++
          dLay (dualW A ++ A) ((σ (fun _ => 0)).map (shiftD A.length))) + eC := by
  obtain ⟨p, eC, eF, eD, hC, hF, hD, he⟩ :=
    canon_dots_eq_sign_decorated₂_add_errors (cs := cs) 0 A [] R
      source_matching source_reduced.1 q (fun j hj => (q_spec j hj).2) σ σ_spec
      source_matching.pairing_properties.2.2.symm 1
      source_matching.pairing_properties.1 source_matching.pairing_properties.2.1
      canonical_crossings (Iso.refl _) [] (by simp)
  have hF0 : FewerDots cs 0 s 0 = ⊥ := by
    apply le_antisymm _ bot_le
    refine Submodule.span_le.2 ?_
    rintro _ ⟨js, γ, -, hlen, -, -⟩
    omega
  have hD0 : DecSpan cs 0 (dualW A ++ A) (cupA (dualW A))
      (R.map (shiftT A.length)) v 0 = ⊥ := by
    apply le_antisymm _ bot_le
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ds, Z, β, -, -, -, hlen, -, -⟩
    omega
  have eF0 : eF = 0 := by simpa only [List.length_nil, hF0, Submodule.mem_bot] using hF
  have eD0 : eD = 0 := by simpa only [List.length_nil, hD0, Submodule.mem_bot] using hD
  refine ⟨p, eC, hC, ?_⟩
  simpa [eF0, eD0, dotsOn] using he

#print axioms OddMath.SKM.canon_dots_signRel_decorated₂
#print axioms OddMath.SKM.canon_dots_eq_sign_decorated₂_add_errors
#print axioms repeated_dot_comparison
#print axioms zero_dot_comparison
end NonVacuity.MatchingDecoratedSign
