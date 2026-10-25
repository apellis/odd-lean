import OddMath.QuiverHecke.SpectatorDetection
import OddMath.SKM.MixedCrossingLocalExamples

/-! # Two odd colours in the spectator evaluation interface

The categorical evaluation and joint detection are displayed as hypotheses.
These examples do not construct a cyclotomic action or identify its bubbles.
-/
noncomputable section
namespace OddMath.QuiverHecke.SpectatorDetectionExamples
open CategoryTheory StringDiagrams OddMath.SKM
open scoped Classical
open OddMath.SKM.MixedCrossingLocalExamples

private def params : Scalars oddDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

private def bubbles : CScalars params where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [params]

private def i : {i : Bool // oddDatum.parity i = 1} := ⟨false, rfl⟩
private def j : {i : Bool // oddDatum.parity i = 1} := ⟨true, rfl⟩

/-- Both exterior factors are evaluated jointly with the active affine map. -/
example (P : SpectatorImage oddDatum params (0 : Bool → ℤ) [false, true] [false, true])
    (E : SpectatorEvaluation oddDatum params bubbles 0 _ _ P) :
    E.observe (upwardCoefficientMap oddDatum params bubbles 0 _ _
      (sourceCoefficientHom oddDatum params (SYM.delta oddDatum ℚ i * SYM.delta oddDatum ℚ j)
        (𝟙 _))) =
      (ELVRelationSpan oddDatum params P.cutoff (P.spectators ++ [false, true])
        (P.spectators ++ [false, true])).mkQ
        (P.bubble (SYM.delta oddDatum ℚ i * SYM.delta oddDatum ℚ j) ≫
          spectatorAffine oddDatum params P.spectators [false, true] [false, true] (𝟙 _)) := by
  rw [E.observe_coefficient]
  exact congrArg _ (P.image_source _ _)

example {A : Type*} (P : A → SpectatorImage oddDatum params (0 : Bool → ℤ)
    [false, true] [false, true])
    (E : ∀ a, SpectatorEvaluation oddDatum params bubbles 0 _ _ (P a))
    (h : ∀ f, (∀ a, (P a).quotientImage f = 0) → f = 0) :
    Function.Injective (upwardCoefficientMap oddDatum params bubbles 0 [false, true] [false, true]) :=
  upwardCoefficientMap_injective_of_spectators oddDatum params bubbles 0 _ _ P E h

end OddMath.QuiverHecke.SpectatorDetectionExamples

#print axioms OddMath.QuiverHecke.SpectatorEvaluation.observe_coefficient
#print axioms OddMath.QuiverHecke.upwardCoefficientMap_injective_of_spectators
#print axioms OddMath.QuiverHecke.upward_independence_of_spectators
