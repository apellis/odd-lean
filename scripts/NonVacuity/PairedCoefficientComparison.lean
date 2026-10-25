import OddMath.SKM.PairedCoefficientComparison
import OddMath.SKM.MatchingChoiceCoefficients
import OddMath.SKM.MixedCrossingLocalExamples

noncomputable section
namespace NonVacuity.PairedCoefficientComparison
open OddMath.SKM
private abbrev D := MixedCrossingLocalExamples.oddDatum
private abbrev K := SYM D ℚ
private def d : K := SYM.delta D ℚ ⟨false, rfl⟩
private def column (i : Unit × ℕ) : K →ₗ[ℚ] (ℕ →₀ K) :=
  (MatchingTransition.rightColumn (k := ℚ)
    (Finsupp.single i.2 1 + if i.2 = 0 then 0 else Finsupp.single (i.2 - 1) d)).comp
      (SYM.parityTwist D ℚ (i.2 : ZMod 2))

-- Every positive row has a genuinely exterior lower coefficient, while
-- the leading coefficient is a parity involution of the entire input.
theorem fullSYM_comparison_injective : Function.Injective (pairedCoefficientComparison column) := by
  classical
  apply pairedCoefficientComparison_injective column Prod.snd (fun _ => 1)
    (fun _ => isUnit_one) (fun i => (i.2 : ZMod 2))
  · intro i j p h
    have hne : i.2 ≠ j.2 := by omega
    have hlo : i.2 ≠ j.2 - 1 := by omega
    by_cases hj : j.2 = 0
    · have hi : i.2 ≠ 0 := by omega
      simp [column, LinearMap.comp_apply, hj, hi]
    · simp [column, LinearMap.comp_apply, hj, hne, hlo]
  · intro i j p _ h
    exact (h (Subsingleton.elim _ _)).elim
  · intro i p
    by_cases hi : i.2 = 0
    · simp [column, LinearMap.comp_apply, hi]
    · have hlo : i.2 ≠ i.2 - 1 := by omega
      simp [column, LinearMap.comp_apply, hi, hlo]

example (f g : (Unit × ℕ) →₀ K)
    (h : pairedCoefficientComparison column f = pairedCoefficientComparison column g) : f = g :=
  fullSYM_comparison_injective h

#print axioms pairedCoefficientComparison_injective
#print axioms fullSYM_comparison_injective
end NonVacuity.PairedCoefficientComparison
