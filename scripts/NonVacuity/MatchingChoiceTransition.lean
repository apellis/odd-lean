import OddMath.SKM.MatchingChoiceTransition
import OddMath.SKM.MixedCrossingLocalExamples

/-!
Native choice-transition consumers over two odd colours and rational scalars.
The two explicit point placements lie before and after a genuine crossing;
the resulting nonempty serializers differ as lists. Their signed comparison
retains finite abstract-SYM lower coefficients in an actual complete choice.
No independence or nonvanishing conclusion is assumed.
-/
noncomputable section
namespace NonVacuity.MatchingChoiceTransition
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
private def F : MatchingBasisChoice A [] :=
  Classical.choice (MatchingBasisChoice.nonempty A [])

private theorem ends : leftEnds₂ A R = [0, 1] := by
  classical
  change (List.range 4).filter (fun j => decide (IsLeftEnd
    [(4, (false, true)), (6, (true, false)), (4, (true, true)), (6, (false, false))] j)) = [0, 1]
  norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
  exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

private def q₀ (j : ℕ) : ℕ × ℕ := (0, 3 - j)
private def q₁ (j : ℕ) : ℕ × ℕ := (1, 3 - j)

private theorem q₀_spec : ∀ j ∈ leftEnds₂ A R,
    (q₀ j).1 ≤ R.length ∧ OnStrand₂ A R j (q₀ j) := by
  intro j hj
  have he := ends
  rw [he] at hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> unfold OnStrand₂ <;> decide

private theorem q₁_spec : ∀ j ∈ leftEnds₂ A R,
    (q₁ j).1 ≤ R.length ∧ OnStrand₂ A R j (q₁ j) := by
  intro j hj
  have he := ends
  rw [he] at hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> unfold OnStrand₂ <;> decide

private theorem exists_serialization (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ A R, (q j).1 ≤ R.length) (n : ℕ → ℕ) :
    ∃ ds, Decorates₂ A R q n ds := by
  apply exists_tmoves_dotPts_perm
  intro p hp
  obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
  rw [List.eq_of_mem_replicate hp]
  exact hq j hj

private def σ₀ (n : ℕ → ℕ) := (exists_serialization q₀ (fun j hj => (q₀_spec j hj).1) n).choose
private def σ₁ (n : ℕ → ℕ) := (exists_serialization q₁ (fun j hj => (q₁_spec j hj).1) n).choose
private theorem σ₀_spec (n) : Decorates₂ A R q₀ n (σ₀ n) :=
  (exists_serialization q₀ (fun j hj => (q₀_spec j hj).1) n).choose_spec
private theorem σ₁_spec (n) : Decorates₂ A R q₁ n (σ₁ n) :=
  (exists_serialization q₁ (fun j hj => (q₁_spec j hj).1) n).choose_spec

/-- The test uses distinct actual dot placements, not just different proof witnesses. -/
theorem serializers_distinct : σ₀ (fun j => if j = 0 then 1 else 0) ≠
    σ₁ (fun j => if j = 0 then 1 else 0) := by
  have h₀ := (σ₀_spec (fun j => if j = 0 then 1 else 0)).2
  have h₁ := (σ₁_spec (fun j => if j = 0 then 1 else 0)).2
  have he := ends
  rw [he] at h₀ h₁
  change (DTMove.dotPts _).Perm [(0, 3)] at h₀
  change (DTMove.dotPts _).Perm [(1, 3)] at h₁
  intro h
  rw [h] at h₀
  have hh := h₀.symm.trans h₁
  simp at hh

private abbrev s := pairing₂ A R
private theorem hc : ncr (canon s) = 1 :=
  (reduced₂_bent_normal_form cs 0 source_matching source_reduced.1).2.1.symm

/-- Three dots at the two placements differ by a sign and lower finite SYM terms. -/
theorem two_placements_filtered :
    SignRel (((Finsupp.supported (SYM D₂ ℚ) ℚ {t | F.dotBound 1 3 t}).map
        (F.expansion cs 0)).comap (bendG cs 0 A []))
      (xev cs 0 [] (dualW A ++ []) (cupA (dualW A) ++ dLay (dualW A ++ A)
        ((σ₀ (fun j => ([0, 0, 1].map (lEnd s)).count j)).map (shiftD A.length))))
      (xev cs 0 [] (dualW A ++ []) (cupA (dualW A) ++ dLay (dualW A ++ A)
        ((σ₁ (fun j => ([0, 0, 1].map (lEnd s)).count j)).map (shiftD A.length)))) := by
  have h₀ := F.canonical_filtered_signRel cs 0 1 R source_matching source_reduced.1
    q₀ (fun j hj => (q₀_spec j hj).2) σ₀ σ₀_spec
    source_matching.pairing_properties.1 source_matching.pairing_properties.2.1
    source_matching.pairing_properties.2.2 hc (Iso.refl _) [0, 0, 1] (by decide)
  have h₁ := F.canonical_filtered_signRel cs 0 1 R source_matching source_reduced.1
    q₁ (fun j hj => (q₁_spec j hj).2) σ₁ σ₁_spec
    source_matching.pairing_properties.1 source_matching.pairing_properties.2.1
    source_matching.pairing_properties.2.2 hc (Iso.refl _) [0, 0, 1] (by decide)
  exact h₀.symm.trans h₁

/-- The native iff applies at this nonempty odd boundary with abstract coefficients. -/
theorem all_complete_choices (G : MatchingBasisChoice A []) :
    Function.Injective (F.expansion cs 0) ↔ Function.Injective (G.expansion cs 0) :=
  F.expansion_injective_choice_iff cs 0 G

#print axioms serializers_distinct
#print axioms two_placements_filtered
#print axioms all_complete_choices
end NonVacuity.MatchingChoiceTransition
