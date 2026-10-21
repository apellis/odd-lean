import OddMath

/-! Concrete consumers of the BE2 §8 independence bridge. No instance of the
Nondegeneracy Conjecture is asserted. -/
noncomputable section
namespace NondegeneracyConsumer
open OddMath.SKM
open TwoStrandShiftConsumer

private def cs : CScalars scalars where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [scalars]

private def oneStrand : MatchingBasisChoice [(true, ())] [(true, ())] :=
  (MatchingBasisChoice.nonempty _ _).some

private def emptyWords : MatchingBasisChoice ([] : List (Letter Unit)) [] :=
  (MatchingBasisChoice.nonempty _ _).some

example : Function.Surjective (oneStrand.expansion cs (-2)) :=
  oneStrand.expansion_surjective cs (-2)

example : oneStrand.IsBasis cs (-2) ↔
    Function.Injective (oneStrand.expansion cs (-2)) :=
  oneStrand.isBasis_iff_injective cs (-2)

example : emptyWords.IsBasis cs 0 ↔
    Function.Injective (emptyWords.expansion cs 0) :=
  emptyWords.isBasis_iff_injective cs 0

example : NondegeneracyConjecture cs ↔
    ∀ (a b : List (Letter Unit)), wt datum 0 a = wt datum 0 b →
      ∀ (μ : ℤ) (F : MatchingBasisChoice a b), Function.Injective (F.expansion cs μ) :=
  nondegeneracyConjecture_iff_injective cs

#print axioms OddMath.SKM.betaSYM_range
#print axioms OddMath.SKM.MatchingBasisChoice.nonempty
#print axioms OddMath.SKM.MatchingBasisChoice.expansion_surjective
#print axioms OddMath.SKM.MatchingBasisChoice.isBasis_iff_injective
#print axioms OddMath.SKM.nondegeneracyConjecture_iff_injective
end NondegeneracyConsumer
