import OddMath.SKM.TopClosureCoefficients
import OddMath.SKM.MixedCrossingLocalExamples

/-! Full-coefficient source-prefix closure on a concrete two-odd-color datum. -/

noncomputable section
namespace NonVacuity.TopClosureCoefficients
open CategoryTheory StringDiagrams Presentation OddMath.SKM

private abbrev D₂ := MixedCrossingLocalExamples.oddDatum
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

private def p : SYM D₂ ℚ :=
  SYM.delta D₂ ℚ ⟨false, rfl⟩ +
    SYM.delta D₂ ℚ ⟨false, rfl⟩ * SYM.delta D₂ ℚ ⟨true, rfl⟩ + SYM.e D₂ ℚ false 0

private def colour : Fin 2 → Bool := ![false, true]
private def word : List (Letter Bool) := List.ofFn fun r => (true, colour r)
private def F : MatchingBasisChoice word word := Classical.choice (MatchingBasisChoice.nonempty word word)
private def correction : PositiveWordDots word :=
  ⟨[([], Shape.dot false, [up true])], by simp [word, colour, Shape.dom, Shape.cod],
    by intro x hx; simp only [List.mem_singleton] at hx; subst x; exact ⟨[], false, [up true], rfl⟩,
    by simp⟩

/-- One actual added odd dot, with a full inhomogeneous coefficient, becomes
canonical labels of strictly greater dot count. -/
theorem finite_correction (t : (F.atTop colour colour).Labels) :
    ∃ r : (F.atTop colour colour).Labels →₀ SYM D₂ ℚ,
      (∀ u ∈ r.support, (F.atTop colour colour).openDots t < (F.atTop colour colour).openDots u) ∧
      (F.atTop colour colour).targetExpansion cs 0 r =
        xev cs 0 word word ((F.atTop colour colour).layers t) ≫
          positiveWordExpansion cs 0 word (Finsupp.single correction p) :=
  F.top_positiveExpansion_lift cs colour colour 0 t (Finsupp.single correction p)

#print axioms MatchingBasisChoice.top_correction_signed
#print axioms MatchingBasisChoice.top_positiveExpansion_lift
#print axioms finite_correction
end NonVacuity.TopClosureCoefficients
