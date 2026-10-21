import OddMath

/-! Non-vacuity checks in `NonVacuity.TwoStrandShifts`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.TwoStrandShifts

open CategoryTheory TwoStrandShiftConsumer

example (ν : ℤ) :
    (positiveShift ν).hom ≫ (positiveShift ν).inv = 𝟙 _ ∧
      (positiveShift ν).inv ≫ (positiveShift ν).hom = 𝟙 _ :=
  positive_inverse_equations ν

example (ν : ℤ) :
    (negativeShift ν).hom ≫ (negativeShift ν).inv = 𝟙 _ ∧
      (negativeShift ν).inv ≫ (negativeShift ν).hom = 𝟙 _ :=
  negative_inverse_equations ν

end NonVacuity.TwoStrandShifts
