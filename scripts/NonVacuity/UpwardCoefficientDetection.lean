import OddMath.QuiverHecke.UpwardCoefficientDetection
import OddMath.SKM.MixedCrossingLocalExamples

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke OddMath.SKM
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

/-- Actual evaluation, with both odd coefficients retained, at a single fixed
external weight. This does not assert that the bubble image is nonzero. -/
example : upwardCoefficientMap oddDatum params bubbles (0 : Bool → ℤ)
    [false, true] [false, true]
    (sourceCoefficientHom oddDatum params (SYM.delta oddDatum ℚ i * SYM.delta oddDatum ℚ j)
      (𝟙 ((OddMath.QuiverHecke.pres oddDatum params).obj (OddMath.QuiverHecke.ob oddDatum [false, true])))) =
    bubAt oddDatum params 0 (upWord [false, true])
      (betaSYM bubbles 0 (SYM.delta oddDatum ℚ i * SYM.delta oddDatum ℚ j)) := by
  rw [upwardCoefficientMap_source]
  erw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The remaining fixed-weight action obligation is displayed explicitly;
this conditional consumer does not manufacture a witness to it. -/
example (h : FiniteUpwardObservations oddDatum params bubbles (0 : Bool → ℤ)
    [false, true] [false, true]) :
    Function.Injective (upwardCoefficientMap oddDatum params bubbles 0 [false, true] [false, true]) :=
  upwardCoefficientMap_injective_of_observations oddDatum params bubbles 0 _ _ h

#print axioms upwardCoefficientMap_source
#print axioms cyclicObservation
#print axioms upwardCoefficientMap_injective_of_observations
